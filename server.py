# -*- coding: utf-8 -*-
"""МАД ГРАФИКА — графический клиент Сферы Миров.

Запуск: python -X utf8 server.py   ->  http://localhost:8765
Браузер <-> этот сервер (HTTP + SSE) <-> sowmud.ru:5555 (telnet, cp1251, MSDP).

Сам выбирает кодировку (1 = Windows JMC, Telnet) и вводит имя пользователя; пароль вводит человек.
Карта зоны: клетки из mudbot\\data\\game.db (rooms) + ЗОНЫ\\<зона>\\клетки.csv (эксплор) + клетки, увиденные
сейчас по MSDP (только в памяти). game.db меняется только по клику человека: заметки к клеткам, отметка «скрытая».
Перенесено из КЛОД МАД2\\webui (раскладка по Mapper, путь, миникарта -> мобы на карте, заметки, спидволки).

Для инструментов:  POST /send (команды, по строке)   GET /log?from=N   GET /api/state
"""
import collections
import glob
import json
import os
import queue
import re
import socket
import sqlite3
import subprocess
import sys
import threading
import time
from collections import deque, defaultdict
from http.server import ThreadingHTTPServer, BaseHTTPRequestHandler
from urllib.parse import urlparse, parse_qs

HOST, PORT = "sowmud.ru", 5555
WEB_PORT = 8765
APP_NAME = "Погоняем лысого"
USER = ""                                                      # имя аккаунта и пароль — из аккаунт_<имя>.txt (строка 1 — имя, 2 — пароль)
PW = ""
NAME = ""                                                      # пусто — профиль ещё не выбран (выбирается в окне)
ENC = "cp1251"
HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "data")                              # всё, что нужно клиенту, лежит рядом с ним
DB = os.path.join(DATA, "game.db")
ZONES_DIR = os.path.join(DATA, "ЗОНЫ")
KNOWN_TXT = os.path.join(DATA, "известные_строки.txt")
try:
    VERSION = open(os.path.join(HERE, "VERSION"), encoding="utf-8").read().strip()
except OSError:
    VERSION = "dev"
LOG = os.path.join(HERE, "game.log")

IAC, DONT, DO, WONT, WILL, SB, SE, GA = 255, 254, 253, 252, 251, 250, 240, 249
MSDP = 69
M_VAR, M_VAL, T_OPEN, T_CLOSE, A_OPEN, A_CLOSE = 1, 2, 3, 4, 5, 6
MSDP_VARS = ["ROOM", "HEALTH", "HEALTH_MAX", "MANA", "MANA_MAX", "MOVEMENT", "MOVEMENT_MAX",
             "EXPERIENCE", "EXPERIENCE_MAX", "MONEY", "LEVEL", "AFFECTS"]

DIRW = {"N": "север", "S": "юг", "E": "восток", "W": "запад", "U": "вверх", "D": "вниз"}
RUDIR = {"север": "N", "юг": "S", "восток": "E", "запад": "W", "вверх": "U", "вниз": "D"}
OPP = {"N": "S", "S": "N", "E": "W", "W": "E", "U": "D", "D": "U"}
STEP = {"N": (0, -1), "S": (0, 1), "E": (1, 0), "W": (-1, 0)}

ANSI = re.compile(r"\x1b\[([0-9;]*)([A-Za-z])")
# обычная и боевая строка состояния: «… 569067C [Айлина:Великолепное] [воин дроу:Великолепное] Вых:СЮ>>»
PROMPT = re.compile(r"^(?P<hp>\d+)H (?P<mp>\d+)M (?P<mv>\d+)V (?P<exp>\S+) (?P<coins>\d+)C "
                    r"(?:\[(?P<me>[^\]:]+):(?P<mecond>[^\]]+)\] \[(?P<foe>[^\]:]+):(?P<foecond>[^\]]+)\] )?Вых:(?P<exits>\S*?)>+ ?")
MOBHEAD = re.compile(r"^(.+?) \[уровень (\d+)\], (.+)$")
MAPCH = set("+-|:~/ @mMGRO%=$\"#?_]!>.v^")


# ======================= разбор ANSI =======================
class Sgr:
    def __init__(self):
        self.fg, self.bold = None, False

    def apply(self, codes):
        for c in (codes or "0").split(";"):
            c = int(c) if c.isdigit() else 0
            if c == 0:
                self.fg, self.bold = None, False
            elif c == 1:
                self.bold = True
            elif c == 22:
                self.bold = False
            elif 30 <= c <= 37:
                self.fg = c - 30
            elif c == 39:
                self.fg = None

    def code(self):
        return ("b" if self.bold else "") + (str(self.fg) if self.fg is not None else "")


def split_colored(line, sgr):
    """Строка с ANSI -> (чистая строка, цвет каждого символа), sgr — состояние, переходит между строками."""
    chars, cols, i = [], [], 0
    for m in ANSI.finditer(line):
        for ch in line[i:m.start()]:
            chars.append(ch); cols.append(sgr.code())
        if m.group(2) == "m":
            sgr.apply(m.group(1))
        i = m.end()
    for ch in line[i:]:
        chars.append(ch); cols.append(sgr.code())
    return "".join(chars), cols


def cut_raw(raw, n):
    """Начало строки с ANSI-кодами до n видимых символов."""
    pos = vis = 0
    while pos < len(raw) and vis < n:
        m = ANSI.match(raw, pos)
        if m:
            pos = m.end()
            continue
        pos += 1
        vis += 1
    return raw[:pos]


def first_color(cols, text):
    for ch, c in zip(text, cols):
        if not ch.isspace():
            return c
    return ""


def is_map_line(s):
    return len(s) >= 9 and set(s) <= MAPCH and any(ch in s for ch in "+|:")


# ======================= база и карта =======================
def db():
    c = sqlite3.connect(DB, timeout=20)
    c.row_factory = sqlite3.Row
    return c


LIVE = {}                 # vnum -> (zone, name, exits) — увиденное по MSDP в этом запуске
_world = {}               # кеш: vnum -> [zone, name, exits]
_world_lock = threading.Lock()


def load_world():
    """Все клетки: game.db + ЗОНЫ\\*\\клетки.csv + LIVE. Выходы объединяются."""
    with _world_lock:
        if _world:
            return _world
        w = {}
        try:
            c = db()
            for r in c.execute("select vnum,zone,name,exits from rooms"):
                try:
                    ex = json.loads(r["exits"] or "{}")
                except Exception:
                    ex = {}
                w[str(r["vnum"])] = [r["zone"], r["name"], ex]
            c.close()
        except Exception as e:
            print("game.db:", e)
        for f in glob.glob(os.path.join(ZONES_DIR, "*", "клетки.csv")):
            zone = os.path.basename(os.path.dirname(f))
            try:
                rows = open(f, encoding="cp1251").read().splitlines()[1:]
            except OSError:
                continue
            for ln in rows:
                p = ln.split(";")
                if len(p) < 3 or not p[0].isdigit():
                    continue
                ex = {}
                for part in p[2].split(","):
                    if "=" in part:
                        d, v = part.split("=", 1)
                        d = RUDIR.get(d.strip())
                        if d and v.strip().isdigit():
                            ex[d] = v.strip()
                old = w.get(p[0])
                if old:
                    old[2] = {**old[2], **ex}
                else:
                    w[p[0]] = [zone, p[1], ex]
        for v, (z, n, ex) in LIVE.items():
            if v in w:
                w[v][2] = {**w[v][2], **ex}
                w[v][0] = z or w[v][0]
            else:
                w[v] = [z, n, dict(ex)]
        _world.update(w)
        return _world


def norm_zone(z):
    return (z or "").replace('"', "'").strip()


def zone_rooms(zone):
    w = load_world()
    nz = norm_zone(zone)
    return {v: (r[1], dict(r[2])) for v, r in w.items() if norm_zone(r[0]) == nz}


def dt_exits():
    """ЗОНЫ\\дт_выходы.txt: (зона, клетка, направление) — ДТ, красные клетки, запреты."""
    out = set()
    try:
        for ln in open(os.path.join(ZONES_DIR, "дт_выходы.txt"), encoding="cp1251").read().splitlines():
            p = ln.split(";")
            if len(p) >= 3 and RUDIR.get(p[2].strip()):
                out.add((p[1].strip().lower(), RUDIR[p[2].strip()]))
    except OSError:
        pass
    return out


MST = {"N": (-1, 0, 0), "S": (1, 0, 0), "W": (0, -1, 0), "E": (0, 1, 0), "U": (0, 0, 1), "D": (0, 0, -1)}


def _norm(s):
    return (s or "").lower().replace("ё", "е").replace("-", " ").strip()


def mapper_layout(c, zone, rooms):
    """Раскладка по картам MUD Mapper (X — строка, Y — столбец, L — этаж): привязка клеток по названию и соседям."""
    cells = c.execute("select x,y,l,name from mapper_rooms where zone=?", (zone,)).fetchall()
    if not cells:
        return None
    M = {(r["x"], r["y"], r["l"]): _norm(r["name"]) for r in cells}
    byname_m = defaultdict(list)
    for k, n in M.items():
        byname_m[n].append(k)
    byname_r = defaultdict(list)
    for v, (n, _) in rooms.items():
        byname_r[_norm(n)].append(v)
    match, used = {}, set()
    for n, rl in byname_r.items():
        if len(rl) == 1 and len(byname_m.get(n, [])) == 1:
            match[rl[0]] = byname_m[n][0]
            used.add(byname_m[n][0])
    if not match:
        return None

    def nb(cell, d):
        m = MST[d]
        return (cell[0] + m[0], cell[1] + m[1], cell[2] + m[2])

    changed = True
    while changed:
        changed = False
        for v, cell in list(match.items()):
            for d, w in rooms[v][1].items():
                if w in rooms and w not in match and d in MST:
                    k = nb(cell, d)
                    if k in M and k not in used and M[k] == _norm(rooms[w][0]):
                        match[w] = k; used.add(k); changed = True
        for w in [x for x in rooms if x not in match]:
            for d, t in rooms[w][1].items():
                if t in match and d in MST:
                    k = nb(match[t], OPP[d])
                    if k in M and k not in used and M[k] == _norm(rooms[w][0]):
                        match[w] = k; used.add(k); changed = True
                        break
    return {v: (k[1], k[0], k[2]) for v, k in match.items()}, len(match)


def layout(zone):
    """Раскладка зоны: по Mapper, если привязалась половина клеток, иначе обход по направлениям."""
    rooms = zone_rooms(zone)
    w = load_world()
    hid_links = []
    for a, (_, ex) in list(rooms.items()):        # скрытые проходы односторонние: достраиваем обратную связь
        for d, b in list(ex.items()):
            if b in rooms and d in OPP and OPP[d] not in rooms[b][1]:
                rooms[b][1][OPP[d]] = a
                hid_links.append([b, OPP[d], a])
    lvl, loc = {}, {}
    for start in rooms:
        if start in lvl:
            continue
        lvl[start] = 0
        loc[start] = (0, 0)
        used = {(0, 0, 0): start}
        q = deque([start])
        while q:
            a = q.popleft()
            for d, b in rooms[a][1].items():
                if b not in rooms or b in lvl:
                    continue
                if d in ("U", "D"):
                    lvl[b] = lvl[a] + (1 if d == "U" else -1)
                    p = loc[a]
                elif d in STEP:
                    lvl[b] = lvl[a]
                    p = (loc[a][0] + STEP[d][0], loc[a][1] + STEP[d][1])
                else:
                    continue
                while (lvl[b],) + p in used:
                    p = (p[0] + 1, p[1])
                loc[b] = p
                used[(lvl[b],) + p] = b
                q.append(b)
    groups, seen = [], set()
    for start in rooms:
        if start in seen:
            continue
        stack, g = [start], []
        seen.add(start)
        while stack:
            a = stack.pop()
            g.append(a)
            for b in rooms[a][1].values():
                if b in rooms and b not in seen:
                    seen.add(b); stack.append(b)
        groups.append(g)
    pos, offx = {}, 0
    for vs in groups:
        x0 = min(loc[v][0] for v in vs)
        y0 = min(loc[v][1] for v in vs)
        for v in vs:
            pos[v] = (loc[v][0] - x0 + offx, loc[v][1] - y0)
        offx += max(loc[v][0] - x0 for v in vs) + 4
    layout_kind, matched = "bfs", 0
    c = db()
    try:
        ml = mapper_layout(c, zone, rooms)
    except Exception:
        ml = None
    if ml and ml[1] >= 0.5 * len(rooms):
        mpos, matched = ml
        layout_kind = "mapper"
        right = max(p[0] for p in mpos.values()) + 4
        for v in rooms:
            if v in mpos:
                pos[v] = (mpos[v][0], mpos[v][1]); lvl[v] = mpos[v][2]
        for v in [x for x in rooms if x not in mpos]:
            placed = False
            for d, t in rooms[v][1].items():
                if t in mpos and d in MST:
                    m = MST[OPP[d]]
                    cand = (pos[t][0] + m[1], pos[t][1] + m[0])
                    lvl[v] = lvl[t] + m[2]
                    while any(pos.get(o) == cand and lvl.get(o) == lvl[v] for o in mpos):
                        cand = (cand[0] + 1, cand[1])
                    pos[v] = cand
                    placed = True
                    break
            if not placed:
                pos[v] = (pos[v][0] + right, pos[v][1])
    edges, links = [], []
    for a, (n, ex) in rooms.items():
        for d, b in ex.items():
            if b in rooms and d in STEP:
                if a < b:
                    edges.append([a, b])
            elif b not in rooms:
                links.append([a, d, w[b][0] if b in w else "?"])
    c.execute("CREATE TABLE IF NOT EXISTS room_flags (vnum TEXT, flag TEXT, PRIMARY KEY (vnum, flag))")
    hidden = [r["vnum"] for r in c.execute("select vnum from room_flags where flag='hidden'") if r["vnum"] in rooms]
    notes = notes_map(c, set(rooms))
    c.close()
    dts = dt_exits()
    dt = [[v, d] for v, (n, ex) in rooms.items() for d in DIRW if (n.lower(), d) in dts]
    return {"zone": zone, "rooms": [[v, rooms[v][0], pos[v][0], pos[v][1], lvl[v]] for v in rooms],
            "edges": edges, "links": links, "hidden": hidden, "hid_links": hid_links, "notes": notes,
            "layout": layout_kind, "matched": matched, "dt": dt,
            "ud": [[a, d, ex[d], rooms[ex[d]][0], lvl[ex[d]]] for a, (n, ex) in rooms.items()
                   for d in ("U", "D") if d in ex and ex[d] in rooms]}


def ensure_notes(c):
    c.execute("CREATE TABLE IF NOT EXISTS room_notes (id INTEGER PRIMARY KEY AUTOINCREMENT, vnum TEXT, text TEXT, ts TEXT)")
    if "grp" not in [r[1] for r in c.execute("PRAGMA table_info(room_notes)")]:
        c.execute("ALTER TABLE room_notes ADD COLUMN grp TEXT")


def notes_map(c, vset):
    ensure_notes(c)
    cnt = {r[0]: r[1] for r in c.execute("select grp,count(*) from room_notes where grp is not null group by grp")}
    out = defaultdict(list)
    for r in c.execute("select id,vnum,text,ts,grp from room_notes order by id"):
        if r["vnum"] in vset:
            out[r["vnum"]].append({"id": r["id"], "text": r["text"], "ts": r["ts"], "grp": r["grp"], "n": cnt.get(r["grp"], 1)})
    return out


def find_path(a, b):
    g = {v: dict(r[2]) for v, r in load_world().items()}
    for x, ex in list(g.items()):                 # скрытые проходы: обратная связь
        for d, y in list(ex.items()):
            if y in g and d in OPP and OPP[d] not in g[y]:
                g[y][OPP[d]] = x
    prev, q = {a: None}, deque([a])
    while q:
        v = q.popleft()
        if v == b:
            break
        for d, n in g.get(v, {}).items():
            if n not in prev:
                prev[n] = (v, d); q.append(n)
    if b not in prev:
        return None
    out = []
    while prev[b]:
        v, d = prev[b]
        out.append(d); b = v
    return out[::-1]


# ======================= гаги =======================
GAGS_TXT = os.path.join(HERE, "гаги.txt")


def jmc_to_regex(p):
    """Шаблон JMC (%0..%9 — что угодно, ^ — начало строки) -> регулярное выражение JS/Python."""
    anchored = p.startswith("^")
    p = p[1:] if anchored else p
    parts = re.split(r"%\d+", p.strip())
    rx = "(?:.*?)".join(re.escape(x) for x in parts)
    return ("^" if anchored else "") + rx


def gag_list():
    """Гаги: #substitute {…} {.} из профиля JMC персонажа + МАД ГРАФИКА\\гаги.txt (регулярки, # — комментарий)."""
    out = []
    f = profile_path(NAME) if NAME else None
    if f and os.path.exists(f):
        for ln in open(f, encoding="utf-8", errors="replace"):
            m = re.match(r"^#substitute \{(.+)\} \{\.\}", ln)
            if m:
                out.append(jmc_to_regex(m.group(1)))
    if os.path.exists(GAGS_TXT):
        for ln in open(GAGS_TXT, encoding="utf-8"):
            ln = ln.rstrip("\n")
            if ln.strip() and not ln.lstrip().startswith("#"):
                out.append(ln)
    return out


# ======================= известные мобы (для автоосмотра) =======================
CARDS_CSV = os.path.join(HERE, "карточки_мобов.csv")
CARDS_HEAD = "дата;зона;клетка;строка в комнате;имя;уровень;класс;особенности;хиты;мана;навыки;раса;описание\n"
_known = set()
_known_lock = threading.Lock()


def norm_line(s):
    s = re.sub(r"\s*\(x\d+\)|\s*\[\d+\]", "", s)
    s = re.sub(r"\s*\.\.\..*$", "", s)             # все ауры: «...светящийся шарик ...освящение ...огненный щит» (набор меняется — ключ не должен)
    s = re.sub(r"\s*\([^)]*\)", "", s)             # «(невидим)» и т.п.
    return s.strip().rstrip(".").lower().replace("ё", "е")


def known_lines():
    with _known_lock:
        if _known:
            return _known
        k = set()
        try:
            c = db()
            for tbl, col in (("mob_cards", "room"), ("mob_lines", "line")):
                for (v,) in c.execute(f"select {col} from {tbl}"):
                    if v:
                        k.add(norm_line(v))
            c.close()
        except Exception as e:
            print("known:", e)
        if os.path.exists(KNOWN_TXT):
            k.update(x for x in open(KNOWN_TXT, encoding="utf-8").read().splitlines() if x)
        if os.path.exists(CARDS_CSV):
            for ln in open(CARDS_CSV, encoding="utf-8").read().splitlines()[1:]:
                p = ln.split(";")
                if len(p) > 3:
                    k.add(norm_line(p[3]))
        _known.update(k)
        return _known


# после списка комнаты до строки состояния идут чужие события (чат, бой, приходы-уходы): это уже не содержимое комнаты
ROOM_END = re.compile(r"Вы |\S+ (?:сказал\S*|говорит|крикнул\S*|прошептал\S*|спросил\S*|ответил\S*|воскликнул\S*)(?=\s)"
                      r"|.* (?:вступил\S* в бой|произнес\S* магические слова|(?:прилетел|пришел|улетел|ушел|убежал)\S* (?:с|на) "
                      r"|прекратил\S* следовать|начал\S* следовать|передал\S* .*лидерство)")
FIGHT = re.compile(r"^(.+?) (?:стоит|стоят|сидит|сидят|летает|летают|лежит|лежат|отдыхает|отдыхают|спит|спят) здесь, сража\S+ с ")


def mob_label(line):
    """«Имя · Проф · ур.N» из карточки по строке моба в комнате; None — карточки нет."""
    key = norm_line(line)
    try:
        c = db()
        for r in c.execute("select name,prof,level,room from mob_cards"):
            if r["room"] and norm_line(r["room"]) == key:
                c.close()
                return f'{r["name"]} · {r["prof"] or "?"} · ур.{r["level"]}'
        for r in c.execute("select m.line,k.name,k.prof,k.level from mob_lines m join mob_cards k on k.zone=m.zone and k.name=m.name"):
            if norm_line(r["line"]) == key:
                c.close()
                return f'{r["name"]} · {r["prof"] or "?"} · ур.{r["level"]}'
        c.close()
        if os.path.exists(CARDS_CSV):
            rows = [ln.split(";") for ln in open(CARDS_CSV, encoding="utf-8").read().splitlines()[1:]]
            rows = [p for p in rows if len(p) > 6]
            for p in rows:
                if norm_line(p[3]) == key:
                    return f"{p[4]} · {p[6] or '?'} · ур.{p[5]}"
        fm = FIGHT.match(re.sub(r"^\([^)]*\)\s*", "", line.strip()))     # «(очарован) » спереди не в счёт          # в бою строка своя у каждого («…сражается с Сьероном!»): ищем карточку по имени моба
        if fm:
            short = fm.group(1).lower().replace("ё", "е")
            c = db()
            for r in c.execute("select name,prof,level from mob_cards"):
                if r["name"].lower().replace("ё", "е") == short:
                    c.close()
                    return f'{r["name"]} · {r["prof"] or "?"} · ур.{r["level"]}'
            c.close()
            for p in rows if os.path.exists(CARDS_CSV) else []:
                f2 = FIGHT.match(p[3])          # короткое описание в бою ≠ имя карточки («Очарованная узница» = «Хранительница пепла»)
                if p[4].lower().replace("ё", "е") == short or (f2 and f2.group(1).lower().replace("ё", "е") == short):
                    return f"{p[4]} · {p[6] or '?'} · ур.{p[5]}"
    except Exception as e:
        print("label:", e)
    return None


def save_card(card, line, cur):
    new = not os.path.exists(CARDS_CSV)
    clean = lambda x: str(x).replace(";", ",").replace("\n", " ")
    hp = "/".join(map(str, card["hp"])) if card["hp"] else ""
    mp = "/".join(map(str, card["mana"])) if card["mana"] else ""
    row = [time.strftime("%d.%m.%Y %H:%M"), (cur or {}).get("area", ""), (cur or {}).get("vnum", ""), line,
           card["name"], card["level"], card["cls"], " ".join("[%s]" % f for f in card["flags"]), hp, mp,
           card["skills"], card["race"], card["desc"]]
    with open(CARDS_CSV, "a", encoding="utf-8") as f:
        if new:
            f.write(CARDS_HEAD)
        f.write(";".join(clean(x) for x in row) + "\n")
    with _known_lock:
        _known.add(norm_line(line))


# ======================= миникарта =======================
def parse_minimap(block):
    """block: [(чистая строка, цвета)]. Клетка — 3 символа внутри стен, шаг 4.
    Возвращает {(dx,dy): [обычные m, M, агрессивные (красная m)]} относительно @ (dy>0 — юг)."""
    rows = [(s, c) for s, c in block if "+" not in s]
    me = None
    for ri, (s, c) in enumerate(rows):
        for i, ch in enumerate(s):
            if ch == "@" and "2" in c[i]:            # я — зелёная @
                me = (i // 4, ri)
                break
        if me:
            break
    if me is None:
        for ri, (s, c) in enumerate(rows):
            i = s.find("@")
            if i >= 0:
                me = (i // 4, ri); break
    if me is None:
        return {}
    out = {}
    for ri, (s, c) in enumerate(rows):
        for col in range(0, (len(s) + 3) // 4):
            rng = range(4 * col + 1, min(len(s), 4 * col + 4))
            m = sum(1 for k in rng if s[k] == "m")
            M = sum(1 for k in rng if s[k] == "M")
            a = sum(1 for k in rng if s[k] == "m" and "1" in c[k].lstrip("b")[:1])
            if m or M:
                out[(col - me[0], ri - me[1])] = [m - a, M, a]
    return out


def mobs_to_rooms(rel, cur):
    if not cur or not rel:
        return {}
    w = load_world()
    pos = {(0, 0): cur}
    seen = {cur}
    q = deque([(cur, 0, 0)])
    while q:
        v, x, y = q.popleft()
        for d, b in w.get(v, [None, None, {}])[2].items():
            if d in STEP and b not in seen:
                nx, ny = x + STEP[d][0], y + STEP[d][1]
                if abs(nx) <= 10 and abs(ny) <= 10:
                    seen.add(b)
                    pos.setdefault((nx, ny), b)
                    q.append((b, nx, ny))
    return {pos[k]: v for k, v in rel.items() if k in pos}


# ======================= MSDP =======================
def msdp_parse(data, i=0, end=None):
    end = len(data) if end is None else end
    out, var = {}, None

    def table(i):
        depth, j = 1, i
        while j < len(data) and depth:
            if data[j] == T_OPEN:
                depth += 1
            elif data[j] == T_CLOSE:
                depth -= 1
            j += 1
        return msdp_parse(data, i, j - 1), j

    def value(i):
        if i < end and data[i] == T_OPEN:
            return table(i + 1)
        if i < end and data[i] == A_OPEN:
            arr, i = [], i + 1
            while i < end and data[i] != A_CLOSE:
                if data[i] == M_VAL:
                    v, i = value(i + 1)
                    arr.append(v)
                else:
                    i += 1
            return arr, i + 1
        j = i
        while j < end and data[j] not in (M_VAR, M_VAL, T_CLOSE, A_CLOSE):
            j += 1
        return data[i:j].decode(ENC, "replace"), j

    while i < end:
        b = data[i]
        if b == M_VAR:
            j = i + 1
            while j < end and data[j] != M_VAL:
                j += 1
            var = data[i + 1:j].decode(ENC, "replace")
            i = j
        elif b == M_VAL:
            v, i = value(i + 1)
            if var is not None:
                out[var] = v
        else:
            i += 1
    return out


# ======================= соединение с игрой =======================
PRESENCE_WORDS = os.path.join(DATA, "presence_words.txt")
PRESENCE_LOG = os.path.join(HERE, "presence_calib.log")
PRESENCE_DUMP = os.path.join(HERE, "presence_dump.log")      # разбор: последние строки перед ответом на проверку / тревогой
PRESENCE_SHADOW = os.path.join(HERE, "presence_shadow.log")   # тень: серии строк без словаря, одна строка на серию
PRESENCE_SEEN = os.path.join(HERE, "presence_seen.txt")      # строки, которые уже встречались: проверка каждый раз новая, обычный текст повторяется
AUTO_MOL = os.environ.get("PRESENCE_AUTO_MOL", "1") != "0"   # автонажатие «мол тут» на автопроверке; 0 — выключить


class Presence:
    """Проверка присутствия (справка ПРОВЕРКА_ПРИСУТСТВИЯ): поток строк проверки без префикса — тарабарщина
    (автопроверка) или осмысленные, но нехарактерные для обстановки строки (ручная); цвет любой, кроме чёрного.
    Строка «своя», если подходит под любое выражение из data\\presence_words.txt (словарь бота Чвырла). Остальные считаем.
    Тревога: >= 5 чужих строк за 10 с. 3 одинаковые в раунде больше не тревожат — уходят в лог/тень, окно не открывают.
    Цвет в правиле не участвует (только пишется в лог): тревога по 5 строкам за 10 с, цвет не решает.
    Каждая подозрительная строка пишется туда же; по ответу на проверку и по её исходу последние строки
    (включая те, что словарь счёл «своими») выгружаются в presence_dump.log — так видно, что именно пришло."""
    WINDOW, PER_WINDOW, QUIET = 10.0, 5, 90.0

    def __init__(self):
        self.words = []
        if os.path.exists(PRESENCE_WORDS):
            for ln in open(PRESENCE_WORDS, encoding="utf-8"):
                ln = ln.rstrip("\n")
                if ln and not ln.startswith("#"):
                    try:
                        self.words.append(re.compile(ln))
                    except re.error:
                        pass
        self.seen = set()
        if os.path.exists(PRESENCE_SEEN):
            self.seen = set(open(PRESENCE_SEEN, encoding="utf-8").read().splitlines())
        self.round = 0
        self.hits = deque()                         # (время, раунд, цвет, текст)
        self.last_alarm = 0.0
        self.buf = deque(maxlen=400)                # последние строки для разбора: (время, вид, цвет, текст, №правила)
        self._last_dump = 0.0
        self.sh_seen, self.sh_hits = {}, deque()    # тень: свои повторы и серия
        self.sh_last, self.sh_armed, self.sh_alarm_t = 0.0, True, -1e9
        self.last_auto = False                      # можно жать «мол тут» без человека

    def prompt(self):
        self.round += 1

    def line(self, clean, cols, now=None, raw=None):
        """Вызывать на каждую строку игры. Вернёт список строк проверки или None. Тень только пишет лог, тревогу не трогает."""
        now = time.time() if now is None else now
        chk = self._line(clean, cols, now)
        if chk:
            self.sh_alarm_t = now                         # окно открылось: тень пометит серию alarm=1
        self.shadow(now, clean, raw)
        return chk

    def shadow(self, now, clean, raw):
        """Тень: серия >= 5 строк за 10 с без словаря (слова считаются, «своя» тоже) -> одна строка в presence_shadow.log.
        Вид строки берётся из buf (его заполнил _line). Окно, hits, seen и last_alarm не трогает.
        Нужна, чтобы увидеть, что съедает словарь на ручной проверке; включать вторым триггером — после просмотра лога."""
        if not self.buf:
            return
        t, kind, col, s, idx = self.buf[-1]
        if t != now or s != clean.strip() or kind not in ("своя", "ПнП") or re.search(r"\[\d+\]", s):
            return                                        # buf[-1] не наша строка / статус, отступ, повтор, чёрная, урон
        key = re.sub(r"\d+", "#", s.lower())
        if now - self.sh_seen.get(key, -1e9) < 600.0:     # своя память повторов, на 10 минут от первого появления
            return
        if len(self.sh_seen) > 2000:
            self.sh_seen = {k: v for k, v in self.sh_seen.items() if now - v < 600.0}
            if len(self.sh_seen) > 2000:
                self.sh_seen.clear()
        self.sh_seen[key] = now
        if now - self.sh_last >= self.WINDOW:             # окно опустело — серия кончилась, можно писать следующую
            self.sh_armed = True
        self.sh_last = now
        codes = "".join(re.findall(r"\x1b\[[\d;]*m", raw or ""))
        self.sh_hits.append((now, kind, idx, s, codes))
        while self.sh_hits and now - self.sh_hits[0][0] > self.WINDOW:
            self.sh_hits.popleft()
        if not self.sh_armed or len(self.sh_hits) < self.PER_WINDOW:
            return
        self.sh_armed = False                             # одно событие на серию
        h = list(self.sh_hits)
        own = [x[2] for x in h if x[1] == "своя"]
        cols_seen = []
        for x in h:
            if x[4] not in cols_seen:
                cols_seen.append(x[4])
        try:
            with open(PRESENCE_SHADOW, "a", encoding="utf-8") as f:
                f.write("%s %s: %d за 10 с, %d за 3.5 с | alarm=%d | своя=%d (%s) ПнП=%d | цвета %s | %s\n" % (
                    time.strftime("%d.%m %H:%M:%S"), NAME, len(h), sum(1 for x in h if now - x[0] <= 3.5), int(now - self.sh_alarm_t <= self.WINDOW),
                    len(own), ",".join(map(str, own)), len(h) - len(own),
                    " ".join(ascii(c)[:40] for c in cols_seen[:6]), " | ".join(x[3][:60] for x in h[:3])))
            if os.path.getsize(PRESENCE_SHADOW) > 100_000:      # лог не растёт: остаются последние 300 серий
                with open(PRESENCE_SHADOW, encoding="utf-8") as f:
                    tail = f.readlines()[-300:]
                with open(PRESENCE_SHADOW, "w", encoding="utf-8") as f:
                    f.writelines(tail)
        except OSError:
            pass

    def _line(self, clean, cols, now):
        s = clean.strip()
        used = {c for ch, c in zip(clean, cols) if not ch.isspace()}
        col = used.pop() if len(used) == 1 else "*"      # "*" — в строке несколько цветов
        if re.match(r"\d+H \d+M \d+V ", s):               # строка состояния без «Вых:» (группа): PROMPT её не знает, раунд считаем здесь
            self.round += 1
            self.note(now, "статус", col, s)
            return None
        if clean[:1].isspace() or s[:1].isdigit() or not re.search(r"[А-Яа-яЁё]{2}", s):
            self.note(now, "пропуск", col, s)
            return None
        for i, w in enumerate(self.words):
            if w.search(s):
                self.note(now, "своя", col, s, i)
                return None
        key = re.sub(r"\d+", "#", s.lower())
        if now - self.last_alarm >= self.QUIET:           # во время и сразу после тревоги не запоминаем и «виденность» не учитываем
            if key in self.seen:                          # уже видели такую строку: это не случайная бессмыслица проверки
                self.note(now, "видел", col, s)
                return None
            self.seen.add(key)
            try:
                with open(PRESENCE_SEEN, "a", encoding="utf-8") as f:
                    f.write(key + "\n")
            except OSError:
                pass
        if col == "0":                                    # чёрный проверка не использует
            self.note(now, "чёрная", col, s)
            return None
        self.note(now, "ПнП", col, s)
        plog("ПнП цвет %s: %s" % (col or "-", s))         # каждая подозрительная строка — в presence_calib.log (как КЛОД ЕБЛАН у JMC)
        self.hits.append((now, self.round, col, s))
        while self.hits and now - self.hits[0][0] > self.WINDOW:
            self.hits.popleft()
        if len(self.hits) >= self.PER_WINDOW:
            reason = "%d строк за %d с" % (len(self.hits), self.WINDOW)
        else:
            return None
        if now - self.last_alarm < self.QUIET:
            return None
        self.last_alarm = now
        self.last_auto = bool(AUTO_MOL)              # 5 строк за 10 с — автопроверка (ручную за скобки)
        try:                                              # строки проверки в память обычных не попадают (вдруг выпадут снова)
            self.seen -= {re.sub(r"\d+", "#", h[3].lower()) for h in self.hits}
            with open(PRESENCE_SEEN, "w", encoding="utf-8") as f:
                f.write("".join(k + "\n" for k in self.seen))
        except OSError:
            pass
        try:
            with open(PRESENCE_LOG, "a", encoding="utf-8") as f:
                f.write("%s %s: %s\n" % (time.strftime("%d.%m %H:%M:%S"), NAME, reason))
                for t, r, c, x in self.hits:
                    f.write("  %s раунд %d цвет %s  %s\n" % (time.strftime("%H:%M:%S", time.localtime(t)), r, c, x))
        except OSError:
            pass
        self.dump("тревога: " + reason)
        return [h[3] for h in self.hits]

    def note(self, now, kind, col, s, idx=None):
        """Строка в кольцевой буфер — что клиент видел и как её понял (своя / ПнП / видел / пропуск / статус)."""
        self.buf.append((now, kind, col, s, idx))

    def dump(self, tag):
        """Выгрузить последние строки в presence_dump.log: по ответу на проверку видно, что было до него.
        Пишутся и строки, которые словарь счёл «своими»: так видно, не съел ли словарь ручную проверку."""
        now = time.time()
        if now - self._last_dump < 3.0:                  # «усердно помолились» и «прошли проверку» идут подряд
            return
        self._last_dump = now
        try:
            with open(PRESENCE_DUMP, "a", encoding="utf-8") as f:
                f.write("%s ==== %s ====\n" % (time.strftime("%d.%m %H:%M:%S"), tag))
                for t, kind, col, s, idx in self.buf:
                    f.write("  %s.%03d  %-7s цвет %-5s %s%s\n" % (
                        time.strftime("%H:%M:%S", time.localtime(t)), int((t % 1) * 1000),
                        kind, col or "-", s, ("  (правило %d)" % idx) if idx is not None else ""))
        except OSError:
            pass


GROW = r"^(\s{0,2}\d{1,2}\s|\s{3})\S"          # строка таблицы группы: номер (1–2 цифры) или 3 пробела (без номера)


SOUND_CHECK = "icq"            # звук проверки/подозрения; варианты: python server.py --sounds
SOUND_HIZ = "гонг"             # звук на сообщение Хизмедара (разработчик игры, иммплементор)
SOUNDS = {                     # (частота Гц, длительность мс); свой звук — файл data\\звуки\\<имя>.wav, он главнее
    "icq": [(784, 130), (587, 320)],                                  # «ой-ой», как сообщение в ICQ (приблизительно)
    "колокольчик": [(1319, 110), (1568, 110), (2093, 350)],
    "сирена": [(900, 220), (600, 220), (900, 220), (600, 220)],
    "гонг": [(220, 500), (165, 700)],
    "хизмедар": [(523, 100), (659, 100), (784, 100), (1047, 300)],
}


def play(name):
    def run():
        try:
            import winsound
            wav = os.path.join(DATA, "звуки", name + ".wav")
            if os.path.exists(wav):
                winsound.PlaySound(wav, winsound.SND_FILENAME)
            else:
                for f, ms in SOUNDS.get(name, []):
                    winsound.Beep(f, ms)
        except Exception:
            pass
    threading.Thread(target=run, daemon=True).start()


def plog(msg):
    """Метка времени в presence_calib.log: когда окно проверки открылось, нажали, дошло ли до клиента и до игры."""
    try:
        with open(PRESENCE_LOG, "a", encoding="utf-8") as f:
            f.write("%s %s\n" % (time.strftime("%d.%m %H:%M:%S"), msg))
    except OSError:
        pass


def popup_main(name, port, lines, auto="0"):
    """Окно поверх всех при проверке присутствия: «мол тут» шлёт ответ в клиент name, «ок» переключает на его окно.
    auto="1" — автопроверка: окно само жмёт «мол тут» через 0.8 с (ручная проверка-вопрос остаётся человеку)."""
    import ctypes
    import tkinter as tk
    import urllib.request
    auto = str(auto) == "1"
    plog("окно %s: открыто%s" % (name, " (авто)" if auto else ""))
    root = tk.Tk()
    root.title("ПРОВЕРКА — " + name)
    root.configure(bg="#b00020")
    root.geometry("640x420+%d+%d" % (root.winfo_screenwidth() // 2 - 320, root.winfo_screenheight() // 4))
    tk.Label(root, text="ПРОВЕРКА ПРИСУТСТВИЯ\n" + name, bg="#b00020", fg="white", font=("Segoe UI", 16, "bold")).pack(pady=8)
    tk.Label(root, text=lines, bg="#b00020", fg="white", wraplength=430, font=("Segoe UI", 9)).pack()

    def mol():
        t0 = time.time()
        for _ in range(3):                              # ответ не должен теряться молча: до трёх попыток, каждая до 10 с
            try:
                urllib.request.urlopen(urllib.request.Request("http://127.0.0.1:%s/send" % port, os.environ.get("PRESENCE_TEST_CMD", "молиться я тут").encode("utf-8"), method="POST"), timeout=10)
                plog("окно %s: «мол тут» нажато%s, клиент принял за %d мс" % (name, " (авто)" if auto else "", (time.time() - t0) * 1000))
                break
            except OSError as e:
                plog("окно %s: «мол тут» не дошло до клиента: %r" % (name, e))
        root.destroy()

    def ok():
        u = ctypes.windll.user32
        found = []
        cb = ctypes.WINFUNCTYPE(ctypes.c_bool, ctypes.c_void_p, ctypes.c_void_p)(lambda h, _: found.append(h) or True)
        u.EnumWindows(cb, 0)
        for h in found:
            b = ctypes.create_unicode_buffer(200)
            u.GetWindowTextW(h, b, 200)
            if u.IsWindowVisible(h) and b.value.startswith(name + " — "):
                u.ShowWindow(h, 9)
                u.SetForegroundWindow(h)
                break
        root.destroy()

    tk.Button(root, text="мол тут", width=22, height=3, command=mol, bg="#2e7d32", fg="white", activebackground="#43a047",
              font=("Segoe UI", 26, "bold")).pack(padx=10, pady=(0, 6))
    tk.Button(root, text="ок", width=3, command=ok, font=("Segoe UI", 8)).pack(side="right", padx=10, pady=4)

    def beeper():
        while True:
            play(SOUND_CHECK)
            time.sleep(5)
    threading.Thread(target=beeper, daemon=True).start()

    def top():
        root.attributes("-topmost", True)
        root.after(1000, top)
    top()
    root.after(75000, root.destroy)                       # у проверки на ответ 1 минута
    if auto:                                              # автопроверка: не ждём человека
        root.after(800, mol)
    elif os.environ.get("PRESENCE_TEST_CMD"):             # проверка самого окна без настоящей проверки: безопасная команда и «нажатие» через 2 с
        root.after(2000, mol)
    root.mainloop()


class Mud:
    def __init__(self):
        self.hiz_t = 0.0
        self.popup_p = None
        self.presence = Presence()
        self.sock = None
        self.lock = threading.Lock()
        self.subs = []
        self.lines = []                 # весь вывод без цвета (для /log)
        self.partial = ""
        self.state = "off"              # off / charset / user / pass / game
        self.connected = False
        self.msdp_on = False
        self.sgr = Sgr()
        self.map_block = []
        self.room = None                # {name, desc[], exits, items[], mobs[]}
        self.room_stage = None          # None / name / desc / contents
        self.card = None
        self.card_lines = None
        self.cur = None                 # {vnum, area, name, exits}
        self.trail = deque(maxlen=60)
        self.mobs = {}
        self.st = {}
        self.minimap = None
        self.autolook = False
        self.profile = None
        self.grp = None                 # разбираемая таблица группы
        self.group = None               # последняя таблица группы
        self.look_queue = []            # [(команда, строка моба)]
        self.looking = collections.deque()      # отправленные «смотреть»: (строка моба, время); ответы приходят по порядку
        self.look_skip = {}             # строка -> когда не вышло; через 5 мин пробуем снова (игроки и т.п. — зря, но не навсегда)
        self.fl_grp = False
        self.grp_show = 0               # до этого времени таблицу группы не прячем от окна игры (ручная команда «группа»)
        self.hide_map = True            # карту «реж карт да» не показывать в окне игры (она рисуется в миникарте)
        self.fl_tail = ""               # фильтр карты: недописанная строка, похожая на строку карты
        self.last_nl = True             # фильтр карты: последний показанный текст закончился переводом строки
        self.fl_open = False            # фильтр карты: блок карты начался на недописанной строке (приглашение)
        self.fl_block = []              # фильтр карты: накопленные строки возможного блока карты [(строка, длина приглашения)]
        self.pw_sent = False            # сохранённый пароль уже отправляли
        self.pw_bad = False             # игра ответила «Неправильный пароль» — больше сам не отправляю

    # ---------- в браузер ----------
    def emit(self, kind, data):
        msg = json.dumps({"t": kind, "d": data}, ensure_ascii=False)
        for q in list(self.subs):
            q.put(msg)

    def snapshot(self):
        return {"status": "on" if self.connected else "off", "cur": self.cur, "trail": list(self.trail),
                "mobs": self.mobs, "st": self.st, "room": self.room, "card": self.card, "minimap": self.minimap,
                "group": self.group, "name": NAME}

    # ---------- карта «реж карт да»: вырезать из потока в окно игры ----------
    def _fl_flush(self, out):
        blk, self.fl_block = self.fl_block, []
        small = bool(blk) and all(len(ANSI.sub("", raw).rstrip(chr(13))[k:]) == 29 for raw, k in blk)       # у края карты видно 2–3 строки, остальное пусто
        if (len(blk) >= 5 or small) and self.hide_map:      # как в finish_map: от 5 строк (или полной ширины 29) — это миникарта, в игре её нет
            raw0, k = blk[0]
            if k:                                           # первая строка карты идёт сразу за приглашением — приглашение оставляем
                out.append(cut_raw(raw0, k) + "\x1b[0m\r\n")
            elif self.fl_open:                              # приглашение уже показано без конца строки — закрыть строку
                out.append("\r\n")
        else:
            out.extend(raw + "\n" for raw, _k in blk)

    def _fl_line(self, raw, out):
        plain = ANSI.sub("", raw).rstrip("\r")
        p = PROMPT.match(plain)
        rs = (plain[p.end():] if p else plain).rstrip()
        show = time.time() < self.grp_show
        if self.fl_grp and not show:                        # таблица группы идёт только в окно группы
            if rs.startswith("---") or (not p and re.match(GROW, plain) and len(plain) > 20):
                return
            self.fl_grp = False
        if not show and re.match(r"^\s+Имя\s+H\s", plain[p.end():] if p else plain):
            self._fl_flush(out)
            self.fl_grp = True
            if p:                                            # заголовок идёт сразу за строкой состояния — её оставить
                out.append(plain[:p.end()] + "\n")
            return
        if self.hide_map and not p and len(plain) == 29 and not plain.strip():     # пустые строки карты (она всегда 29 знаков шириной)
            return
        if self.hide_map and self.fl_block and not p and rs and set(rs) <= MAPCH:
            self.fl_block.append((raw, 0))
            return
        self._fl_flush(out)
        if self.hide_map and (is_map_line(rs) or (len(plain) - (p.end() if p else 0) == 29 and rs and set(rs) <= MAPCH and any(ch in rs for ch in "+|:"))):   # у края карты строка короче 9 знаков, но ширина всегда 29
            prev = out[-1] if out else None
            self.fl_open = (not prev.endswith("\n")) if prev else not self.last_nl
            self.fl_block.append((raw, p.end() if p else 0))
        else:
            out.append(raw + "\n")

    def map_filter(self, s):
        """Текст для окна игры: без блоков карты. Недописанная строка, похожая на карту, ждёт конца строки."""
        buf = self.fl_tail + s
        self.fl_tail = ""
        *full, tail = buf.split("\n")
        out = []
        for ln in full:
            self._fl_line(ln, out)
        plain = re.sub(r"\x1b(?:\[[0-9;]*)?$", "", ANSI.sub("", tail)).rstrip("\r")   # оборванный в середине ANSI-код не считаем
        p = PROMPT.match(plain)
        rs = (plain[p.end():] if p else plain).rstrip()
        half_prompt = (len(plain) < 100 and re.match(r"^\d+(H( |$)|$)", plain)
                       and (not p or (not rs and not plain.endswith(" "))))                # приглашение пришло не целиком
        half_prompt = half_prompt or bool(re.search(r"\x1b(?:\[[0-9;]*)?$", tail))         # оборван ANSI-код
        grp_tail = tail and time.time() >= self.grp_show and (self.fl_grp and not (p and not half_prompt)          # обрыв посреди таблицы группы
                             or (p and plain[p.end():].startswith("  ")))          # или посреди её заголовка (он идёт сразу за приглашением)
        if grp_tail or (self.hide_map and tail and ((rs and set(rs) <= MAPCH) or half_prompt or (not rs and not p and self.fl_block))):
            self.fl_tail = tail                             # возможно, середина строки карты — ждём конца строки
        elif tail:
            self._fl_flush(out)
            out.append(tail)
        res = "".join(out)
        if res:
            self.last_nl = res.endswith("\n")
        return res

    # ---------- текст ----------
    def text(self, s):
        shown = self.map_filter(s)
        if shown:
            self.emit("text", shown)
        self.partial += s
        *full, self.partial = self.partial.split("\n")
        if full:
            with open(LOG, "a", encoding="utf-8") as f:
                for ln in full:
                    plain = ANSI.sub("", ln).rstrip("\r")
                    f.write(plain + "\n")
                    self.lines.append(plain)
            for ln in full:
                self.parse_line(ln.rstrip("\r"))
                plain = ANSI.sub("", ln).rstrip("\r")
                self.check_bad_pw(plain)
                p = PROMPT.match(plain)
                self.run_triggers(self.unmorph(plain[p.end():] if p else plain))
                self.druid_line(plain, p)
                self.staf_line(plain, p)
                if getattr(self, "chek_q", None):
                    self.chek_q.put(self.unmorph(plain[p.end():] if p else plain))
                if getattr(self, "res_q", None):
                    self.res_q.put(plain)
        tail = ANSI.sub("", self.partial)
        if PROMPT.match(tail):
            self.on_prompt(PROMPT.match(tail))
            self.finish_room()
            self.finish_card()
            self.finish_group()
        self.autologin(tail)

    def check_bad_pw(self, plain):
        if "Неправильный пароль" in plain and self.pw_sent and not self.pw_bad:
            self.pw_bad = True                              # не повторять: иначе блокировка за перебор
            self.emit("sys", "Сохранённый пароль не подошёл — введите вручную (галочка «запомнить» обновит его).")

    def autologin(self, plain):
        if self.state == "charset" and "Enter Charset" in plain:
            self.state = "user"
            self.send_raw("1")
        elif self.state == "user" and "Введите имя" in plain:
            self.state = "wait_pass"
            if not USER and self.profile:                     # триггер профиля «Введите имя своего пользователя…» -> имя
                for t in self.profile.actions:
                    if t["pattern"].startswith("Введите имя своего пользователя") and not t["body"].startswith("#"):
                        remember_account(t["body"].strip())
                        break
            if USER:
                self.send_raw(USER)
                self.emit("sys", "Имя введено. Введите пароль в строке ввода.")
            else:
                self.emit("sys", "Введите имя аккаунта в строке ввода.")
        elif self.state == "wait_pass" and "Пароль" in plain:
            if PW and not self.pw_bad:                      # сохранённый пароль — вход сам (как триггер «Пароль:» в JMC)
                self.state = "game"
                self.pw_sent = True
                self.send_raw(PW)
                self.emit("sys", "Пароль введён автоматически.")
            else:
                self.state = "pass"
                self.emit("password", True)
                self.emit("alert", f"{NAME}: игра просит пароль — введите его в строке ввода")
        self.check_bad_pw(plain)
        m = re.search(r"Пользователь: \[(.+?)\], активный персонаж: \[(.+?)\]", plain)
        if m and m.group(1) and not USER_SAVED.get("v"):
            remember_account(m.group(1))
        if (self.state == "game" and not self.menu_sent and plain.rstrip().endswith("Ваш выбор:")
                and "Войти в игру" in "".join(self.lines[-10:])):
            self.menu_sent = True
            self.send_raw("1")                      # меню аккаунта: 1) Войти в игру (как триггер «Ваш выбор: » -> 1 в профиле)

    def on_prompt(self, p):
        hp, mp, mv = int(p["hp"]), int(p["mp"]), int(p["mv"])
        st = dict(self.st)
        st.update(hp=hp, mp=mp, mv=mv, exp=p["exp"], coins=int(p["coins"]), exits=p["exits"],
                  fight=[p["foe"], p["foecond"]] if p["foe"] else None)
        self.last_prompt = time.time()
        if not getattr(self, "res_resumed", False) and NAME:       # после перезапуска клиента вернуть прежний автореск
            self.res_resumed = True
            try:
                with open(os.path.join(HERE, f"реск_{NAME}.txt"), encoding="utf-8") as f:
                    r = f.read().strip()
            except OSError:
                r = ""
            if r:
                self.rescue_set(r)
            rows = self.chek_saved()                    # Слот18 из запомненного экипа
            if rows:
                self.chek_slot18(rows)
        self.presence.prompt()
        for k, mk in (("hp", "hpm"), ("mp", "mpm"), ("mv", "mvm")):
            st[mk] = max(st.get(mk, 0), st[k])
        if st != self.st:
            self.st = st
            self.emit("st", st)
        if self.state in ("wait_pass", "pass", "game") and not self.msdp_on:
            self.state = "game"
            self.request_msdp()

    def parse_line(self, raw):
        clean, cols = split_colored(raw, self.sgr)
        low = clean.lower()                                # исход проверки: по нему видно, поймали её или нет
        if "вы усердно помолились" in low:
            self.presence.dump("ответ на проверку: " + clean.strip()[:140])
        elif "прошли проверку на ботинг" in low:
            self.presence.dump("проверка пройдена: " + clean.strip()[:140])
        elif "не прошли автоматическую проверку" in low:
            self.presence.dump("проверка НЕ пройдена: " + clean.strip()[:140])
        # строка состояния в начале строки (после неё может идти миникарта)
        p = PROMPT.match(clean)
        raw_tail = raw
        if p:
            self.on_prompt(p)
            self.finish_room()
            self.finish_card()
            k = p.end()
            raw_tail = raw[len(cut_raw(raw, k)):]            # ANSI без приглашения — для лога тени
            clean, cols = clean[k:], cols[k:]
            if not clean.strip():
                return
        # таблица группы (команды гр / группа / пгр)
        if re.match(r"^\s+Имя\s+H\s", clean):
            self.grp = {"head": clean.rstrip(), "rows": [], "t": time.strftime("%H:%M:%S")}
            return
        if self.grp is not None:
            if clean.startswith("---"):
                return
            if re.match(GROW, clean) and len(clean) > 20:
                self.grp["rows"].append(clean.rstrip())
                return
            self.finish_group()
        # миникарта
        if is_map_line(clean.rstrip()) or (self.map_block and set(clean.rstrip()) <= MAPCH and clean.strip()):
            self.map_block.append((clean.rstrip(), cols[:len(clean.rstrip())]))
            return
        if self.map_block:
            self.finish_map()
        # карточка моба
        m = MOBHEAD.match(clean.strip())
        if m and first_color(cols, clean).startswith("b7"):
            self.finish_room()
            self.card_lines = [clean.strip()]
            return
        if self.card_lines is not None:
            self.card_lines.append(clean.rstrip())
            if re.search(r"состояни", clean) or len(self.card_lines) > 40:
                self.finish_card()
            return
        # комната
        fc = first_color(cols, clean)
        if (fc in ("6", "b6") and clean.strip() and not clean.startswith((" ", "[")) and len(clean.strip()) < 80
                and self.room_stage is None):            # игроки в комнате тоже бирюзовые — не путать с названием
            self.finish_room()
            self.room = {"name": clean.strip(), "desc": [], "exits": "", "items": [], "mobs": [], "cr": 0}
            self.room_stage = "desc"
            return
        if self.room_stage == "desc":
            if clean.strip().startswith("[ Exits:"):
                self.room["exits"] = clean.strip()[8:-1].strip()
                self.room_stage = "contents"
            else:
                self.room["desc"].append(clean.strip())
            return
        if self.room_stage == "contents":
            if not clean.strip():
                return
            txt = clean.strip()
            if ROOM_END.match(txt):     # событие после комнаты («Вы достигли пункта назначения.»), не моб
                self.finish_room()
                return
            if fc in ("3", "b3"):
                self.room["items"].append([txt, fc])
                if re.search(r" (летает|стоит|сидит|отдыхает|спит|лежит|сражается)[^.]*здесь", txt):
                    self.room["cr"] += 1                    # игрок/группа окрашены как предметы, но в игровой нумерации «N.» они считаются
            else:
                self.room["mobs"].append([txt, fc, None, self.room["cr"]])     # [строка, цвет, подпись из карточки, место среди существ]
                self.room["cr"] += 1
            return
        # проверка присутствия / опасное
        chk = self.presence.line(clean, cols, raw=raw_tail)
        if chk:
            self.emit("check", chk[-6:])
            if not (self.popup_p and self.popup_p.poll() is None):       # окно поверх всех: «мол тут» / «ок»
                auto = "1" if getattr(self.presence, "last_auto", False) else "0"
                self.popup_p = subprocess.Popen([sys.executable, "-X", "utf8", os.path.abspath(__file__), "--popup", NAME,
                                                 str(WEB_PORT), " | ".join(chk[-6:]), auto], creationflags=0x08000000)

    def track_polymorph(self, old, members):
        """Полиморф: в прошлом чеке на месте N был X, теперь на месте N другое имя (и больше ничего не изменилось) — это X."""
        al = self.alias = getattr(self, "alias", {})
        names = [re.sub(r"^\d+\s+", "", m["name"]) for m in members]      # без номера: он меняется при сортировке
        back = [k for k, v in al.items() if v in names]        # настоящее имя вернулось
        for k in back:
            del al[k]
        if back or not old:
            return
        prev = [re.sub(r"^\d+\s+", "", m["name"]) for m in old["members"]]
        import difflib     # группа может расти/сжиматься: сопоставляем по порядку, «замена» одинаковой длины = полиморф
        for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(None, prev, names, autojunk=False).get_opcodes():
            if tag == "replace" and i2 - i1 == j2 - j1:
                for a, b in zip(prev[i1:i2], names[j1:j2]):
                    if a in names or b in prev:     # таблица сортируется по хитам — перестановка не полиморф
                        continue
                    al[b.lower()] = al.get(a.lower(), a)
                    self.emit("sys", f"Полиморф: {b} = {al[b.lower()]}")

    def unmorph(self, ln):
        m = re.match(r"(\S+)( сказал\S* (?:группе|вам): )", ln)
        o = m and getattr(self, "alias", {}).get(m.group(1).lower())
        return o + ln[m.end(1):] if o else ln

    def finish_group(self):
        g, self.grp = self.grp, None
        if not g:
            return
        head = g["head"]
        cols = [(m.start(), m.group()) for m in re.finditer(r"\S+", head)]
        members = []
        for row in g["rows"]:
            pos_i = next((s for s, w in cols if w == "Позиция"), None)
            h_i = next((s for s, w in cols if w == "H"), 20)
            name = row[:h_i - 3].strip()
            ld = "*" in name                                  # красная «*» у имени — обрыв связи (ЛД), не часть имени
            m = {"name": name.replace("*", "").strip(), "cols": {}, "ld": ld}
            for s, w in cols[1:]:
                if w in ("H", "М", "M", "V"):
                    seg = row[max(0, s - 4):s + 3]
                    m["cols"][w] = seg.count("#") + seg.count("¦")
                elif w == "Позиция":
                    m["cols"][w] = next((t.group() for t in re.finditer(r"\S+", row)
                                         if t.end() > s and t.start() < s + 10), "")
                else:
                    seg = row[max(0, s - 1):s + len(w) + 1].strip()
                    m["cols"][w] = seg
            members.append(m)
        self.track_polymorph(getattr(self, "group", None), members)
        self.group = {"t": g["t"], "head": [w for _, w in cols[1:]], "members": members}
        self.emit("group", self.group)

    def finish_map(self):
        blk, self.map_block = self.map_block, []
        if len(blk) < 5:
            return
        self.minimap = [[s, c] for s, c in blk]
        self.emit("minimap", self.minimap)
        if self.cur:
            self.mobs = {k: v for k, v in mobs_to_rooms(parse_minimap(blk), self.cur["vnum"]).items()}
            self.emit("mobs", self.mobs)

    def finish_room(self):
        if self.room_stage == "contents" and self.room:      # без «[ Exits: …]» это не комната (бирюзовая реплика чата и т.п.)
            self.room["desc"] = " ".join(x for x in self.room["desc"] if x)
            self.room_seq = getattr(self, "room_seq", 0) + 1
            self.room["seq"] = self.room_seq
            self.room["vnum"] = (self.cur or {}).get("vnum")
            for m in self.room["mobs"]:
                m[2] = mob_label(m[0])
            self.emit("room", self.room)
            if self.autolook:
                self.queue_unknown(self.room["mobs"])
        self.room_stage = None

    # ---------- автоосмотр незнакомых мобов ----------
    def queue_unknown(self, mobs):
        kn = known_lines()
        self.look_queue = []
        self.looking.clear()
        # нумерация как в BotCore/MudParse.js: существа в комнате с 2 (1 — ты сам), игроки и чармисы тоже занимают номер;
        # слово из строки не годится — «Темный всадник сеет чуму» в карточке «Сеятель чумы»
        gnames = [re.sub(r"^\d+\s+", "", m["name"]).lower() for m in (self.group or {}).get("members", [])]
        for line, _c, _l, pos in mobs:
            if any(n and re.search(r"(?<![а-яё])" + re.escape(n) + r"(?![а-яё])", line.lower()) for n in gnames):
                continue                                     # свои из группы (по таблице пгр), в т.ч. без расы в строке: «Мряка летает здесь»
            core = re.sub(r"\s*\(.*?\)|\s*\.\.\..*$", "", line).strip()
            # игрок: «Орчиха Кимпи стоит здесь», «Подгорный гном Дакус летает здесь» — имя с большой буквы не в начале
            if re.search(r"\s[А-ЯЁ][а-яё]+(,| (стоит|сидит|летает|отдыхает|спит|лежит|сражается)\b)", core) and "здесь" in core:
                continue
            nl = norm_line(line)
            if nl and nl not in kn and time.time() - self.look_skip.get(nl, 0) > 300 and not mob_label(line):
                self.look_queue.append(("смотреть %d." % (pos + 2), line))
        if self.look_queue:
            self.emit("sys", "Незнакомых мобов: %d — осматриваю." % len(self.look_queue))
        self.pump_look()

    def pump_look(self):
        """По одному «смотреть»: следующий уходит сразу, как пришла карточка (или через 2 с без неё). Пачкой нельзя: стоит
        одной карточке не прийти — все следующие записываются под чужими строками."""
        if self.looking and time.time() - self.looking[0][1] > 3:        # карточки нет (игрок, моб ушёл)
            line = self.looking.popleft()[0]
            self.look_skip[norm_line(line)] = time.time()
            self.emit("sys", f"Осмотр не дал карточки: {line[:50]}")
        if self.looking or not self.look_queue or not self.autolook:
            return
        cmd, line = self.look_queue.pop(0)
        self.looking.append((line, time.time()))
        self.emit("echo", f"{cmd}   (автоосмотр: {re.sub(r' \.\.\..*$', '', line)[:50]})")
        self.send_raw(cmd)
        threading.Timer(3.1, self.pump_look).start()

    def finish_card(self):
        if self.card_lines is None:
            return
        ls, self.card_lines = self.card_lines, None
        m = MOBHEAD.match(ls[0])
        card = {"name": m[1], "level": int(m[2]), "cls": m[3], "flags": [], "hp": "", "mana": "", "skills": "",
                "desc": [], "race": "", "cond": ""}
        for s in ls[1:]:
            t = s.strip()
            if t.startswith("Особенности:"):
                card["flags"] = re.findall(r"\[([^\]]+)\]", t)
            elif t.startswith("Хиты:"):
                h = re.search(r"Хиты: (\d+)/(\d+)", t)
                mm = re.search(r"мана: (\d+)/(\d+)", t)
                card["hp"] = [int(h[1]), int(h[2])] if h else ""
                card["mana"] = [int(mm[1]), int(mm[2])] if mm else ""
            elif t.startswith("Навыки:"):
                card["skills"] = t[7:].strip()
            elif t.startswith("Вы видите перед собой"):
                card["race"] = t[21:].strip(" .")
            elif "состояни" in t:
                card["cond"] = t
            elif t:
                card["desc"].append(t)
        card["desc"] = " ".join(card["desc"])
        self.card = card
        self.emit("card", card)
        if self.looking:
            line = self.looking.popleft()[0]
            try:
                save_card(card, line, self.cur)
                self.emit("sys", f"Карточка записана: {card['name']} (ур. {card['level']}, {card['cls']}).")
                if self.room:                          # окно «Комната и моб» перерисовать: у нового моба теперь есть подпись
                    for m in self.room["mobs"]:
                        m[2] = mob_label(m[0])
                    self.emit("room", self.room)
            except OSError as e:
                self.emit("sys", f"Карточку не записал: {e}")
            threading.Timer(0.05, self.pump_look).start()

    # ---------- MSDP ----------
    def request_msdp(self):
        self.msdp_on = True
        self.raw(bytes([IAC, DO, MSDP]))
        self.msdp_send("REPORT", *MSDP_VARS)
        self.msdp_send("SEND", *MSDP_VARS)

    def msdp_send(self, var, *vals):
        b = bytes([IAC, SB, MSDP, M_VAR]) + var.encode()
        for v in vals:
            b += bytes([M_VAL]) + v.encode()
        self.raw(b + bytes([IAC, SE]))

    def on_msdp(self, payload):
        d = msdp_parse(payload)
        room = d.get("ROOM")
        if isinstance(room, dict) and room.get("VNUM"):
            ex = {}
            for k, v in (room.get("EXITS") or {}).items():
                k = str(k).strip().upper()[:1]
                if isinstance(v, dict):
                    v = v.get("VNUM") or next(iter(v.values()), "")
                if k in DIRW:
                    ex[k] = str(v)
            vn = str(room["VNUM"])
            moved = bool(self.cur) and self.cur["vnum"] != vn
            self.cur = {"vnum": vn, "area": room.get("AREA", ""), "name": room.get("NAME", ""), "exits": ex}
            w = load_world()
            known = w.get(vn)
            if not known or any(known[2].get(k) != v for k, v in ex.items()):
                LIVE[vn] = (self.cur["area"], self.cur["name"], ex)
                with _world_lock:
                    _world.clear()
                self.emit("rooms", True)
            if not self.trail or self.trail[-1][0] != vn:
                self.trail.append([vn, self.cur["area"], self.cur["name"], time.strftime("%H:%M:%S")])
            self.emit("pos", {**self.cur, "trail": list(self.trail)})
            if moved:
                self.poly_move()
        st, ch = dict(self.st), False
        for src, k in (("HEALTH", "hp"), ("HEALTH_MAX", "hpm"), ("MANA", "mp"), ("MANA_MAX", "mpm"),
                       ("MOVEMENT", "mv"), ("MOVEMENT_MAX", "mvm"), ("MONEY", "coins"), ("LEVEL", "level"),
                       ("EXPERIENCE", "xp"), ("EXPERIENCE_MAX", "xpm")):
            if src in d:
                try:
                    st[k] = int(d[src]); ch = True
                except (TypeError, ValueError):
                    pass
        if "AFFECTS" in d:
            a = d["AFFECTS"]
            st["affects"] = list(a.keys()) if isinstance(a, dict) else a if isinstance(a, list) else [str(a)]
            ch = True
        if ch and st != self.st:
            self.st = st
            self.emit("st", st)

    # ---------- соединение ----------
    def connect(self):
        """Подключение в фоне с повторами: связь с игрой бывает нестабильной (соединение то мгновенное, то 20 с, то обрыв)."""
        if self.connected or getattr(self, "connecting", False):
            return
        self.connecting = True
        threading.Thread(target=self._connect_retry, daemon=True).start()

    def _connect_retry(self):
        try:
            for k in range(1, 6):
                if self.connected:
                    return
                self.emit("sys", f"Подключаюсь к {HOST}:{PORT} (попытка {k} из 5) …")
                if self._connect_once():
                    t = time.time()                     # игра должна прислать приветствие; молчит — пробуем заново
                    while time.time() - t < 25 and self.connected and self.state == "charset":
                        time.sleep(0.3)
                    if not self.connected or self.state != "charset":
                        return
                    self.emit("sys", "Игра не ответила приветствием — переподключаюсь.")
                    self.disconnect()
                    time.sleep(1)
                else:
                    time.sleep(2)
            self.emit("sys", "Не удалось подключиться после 5 попыток. Проверьте связь и нажмите «Подключиться» снова.")
        finally:
            self.connecting = False

    def _connect_once(self):
        try:
            self.sock = socket.create_connection((HOST, PORT), 30)
            self.sock.settimeout(None)
            self.sock.setsockopt(socket.SOL_SOCKET, socket.SO_KEEPALIVE, 1)
            self.t_conn = time.time()
        except OSError as e:
            self.emit("sys", f"Не удалось подключиться: {e}")
            return False
        self.connected = True
        self.user_closed = False
        self.menu_sent = False
        self.msdp_on = False
        self.state = "charset"
        self.emit("status", "on")
        threading.Thread(target=self.reader, daemon=True).start()
        return True

    def disconnect(self):
        self.user_closed = True
        try:
            self.sock.close()
        except Exception:
            pass

    def raw(self, b):
        if self.connected:
            with self.lock:
                self.sock.sendall(b)

    def send_raw(self, s):
        self.raw(s.encode(ENC, "replace").replace(b"\xff", b"\xff\xff") + b"\r\n")

    def send_password(self, s, save=False):
        """Пароль из поля ввода окна (запрос /password); save — галочка «запомнить» -> аккаунт_<имя>.txt."""
        if self.state != "pass":
            return
        if save:
            remember_password(s)
            self.pw_bad = False
        self.state = "game"
        self.emit("password", False)
        self.emit("echo", "********")
        self.send_raw(s)

    def send_user(self, s):
        if self.state in ("pass", "charset", "user", "off"):
            self.emit("sys", "Команда не отправлена: идёт вход в игру (пароль вводит человек).")
            return
        if self.state == "wait_pass" and s.strip() and not USER:        # человек сам ввёл имя аккаунта — запомнить
            remember_account(s.strip())
        for ln in s.split("\n"):
            self.emit("echo", ln)
            if ln.strip().lower().startswith("мол"):
                plog("%s: в игру уходит «%s»" % (NAME, ln.strip()))
            if self.profile and re.match(r"^#(alias|action|unalias|unaction|hot|unhot|variable|group)\b", ln.strip(), re.I):
                self.emit("sys", self.profile.command(ln.strip()))      # как в JMC: #alias/#action из строки ввода -> в профиль
                self.emit("profile", True)
                continue
            if self.profile and self.state == "game" and ln.strip():
                notes = []
                self.sync_vars()
                cmds = self.profile.expand(ln, notes=notes)
                for n in notes:
                    self.emit("sys", n)
                if cmds != [ln.strip()]:
                    self.emit("sys", "→ " + "; ".join(cmds)[:300])
                for c in cmds:
                    self.send_cmd(c)
            else:
                self.send_raw(ln)

    # ---------- ЧЕК: чс (экипировка), чколб (расходники), проверка = оба, -сет, окей ----------
    CHEK_WORDS = ("чс", "чколб", "проверка", "-сет", "окей", "сетгр", "стафгр")
    CHEK_LEADERS = ("зорон", "тадия")                       # когда они лидеры, «груп сортв» / «груп номер обычн» запускает проверку стафа группы
    CHEK_EXPECT = {"зорон": 17, "тадия": 18, "кейб": 18}       # сколько вещей должно быть надето
    CHEK_ITEMS = [("панац", 5, "ПАНАЦЕИ"), ("камней", 5, "КАМНЕЙ"), ("охр", 10, "ОХРАНОК"),
                  ("освоб", 10, "ОСВОБОЖДЕНИЯ"), ("фляг", 4, "ФЛЯГ")]    # ключ для осм, порог, что МАЛО

    def send_cmd(self, c):
        """Команда из алиаса/триггера: слова ЧЕК делает клиент, остальное уходит в игру."""
        w = c.strip().lower()
        if w == "окей":
            self.chek("окей")
        elif NAME.lower() in self.DRUID and w.split(" ")[0] in ("поли", "морф") and " " in w:
            if self.cd_ready("поли"):                    # «!поли карл 2карл» от лидера: цели на следующий переход
                self.poly_targets = c.strip().split(None, 1)[1]
                self.chek_say("полиморф: цели запомнены — " + self.poly_targets)
            else:                                        # на кд — цели не ждут, лидеру сразу говорим
                self.send_raw("гг морф кд")
                self.chek_say("полиморф на кд — цели от лидера пропущены, «морф кд» в группу")
        elif w.split(" ")[0] == "реск":                 # реск 2 3 — автоспас номеров каждый раунд; реск — выключить
            r = " ".join(w.split()[1:])
            self.rescue_set("" if r in ("0", "выкл") else r)
        elif w in self.CHEK_WORDS:                      # по очереди, в порядке команд
            if getattr(self, "chek_jobs", None) is None:
                self.chek_jobs = queue.Queue()
                threading.Thread(target=self.chek_worker, daemon=True).start()
            self.chek_jobs.put(w)
        else:
            self.send_raw(c)
    # ---------- друид (Тадия): полиморф по целям лидера, землетрясение -> живые корни ----------
    DRUID = ("тадия",)
    CD_FALLBACK = {"корни": 30, "поли": 300}           # кд (с): корни 30 с, полиморф 5 мин; сообщение «Вы вновь можете…» сбрасывает раньше

    def cd_ready(self, k):
        return time.time() >= getattr(self, "cd_until", {}).get(k, 0)

    def cd_clear(self, k):
        getattr(self, "cd_until", {}).pop(k, None)

    def cd_start(self, k):
        if not hasattr(self, "cd_until"):
            self.cd_until = {}
        self.cd_until[k] = time.time() + self.CD_FALLBACK[k]

    # сбитые с ног враги из любых источников (землетрясение, удар, выстрел, течение, «завалить»): "(кому)" -> ключ из первых букв
    DOWN = re.compile(r"^(?:(.+?) упал[аио]? и больно ударил|(.+?) попытал\S* завалить .*, и (?:он|она|оно|они) упал"
                      r"|.* сби(?:л|ла|ло|ли|вает) (.+?) с ног)")
    UP = re.compile(r"^(.+?) встал[аио]? на ноги")

    @staticmethod
    def down_key(n):
        return re.sub(r"[^а-яёa-z]", "", n.lower())[:4]

    def is_ours(self, n):
        """Свой из таблицы группы (в том числе в падеже: «Кейба», «Штыру»)."""
        n = n.strip().lower()
        for g in (self.group or {}).get("members", []):
            m = re.sub(r"^\d+\s+", "", g["name"]).strip().lower()
            if m and (n == m or n.startswith(m) or (len(m) >= 4 and n.startswith(m[:-1]))):
                return True
        return False

    ROOTS = re.compile(r"^Множество ползучих корней вылезло из-под земли и обвилось вокруг (.+?)\.")

    def roots_report(self, auto):
        n, self.roots = self.roots, None
        self.emit("sys", f"ЧЕК: {'автокаст корней' if auto else 'корни'} — задело {n} целей")     # «ЧЕК: » — в окно «Проверки», где ты видишь «сбито врагов»

    def druid_line(self, plain, p):
        if NAME.lower() not in self.DRUID:
            return
        s = self.unmorph(plain[p.end():] if p else plain)
        if getattr(self, "roots", None) is not None and (m := self.ROOTS.match(s)) and not self.is_ours(m.group(1)):
            self.roots += 1
        if s.startswith("Вы произнесли магические слова 'живые корни'"):
            self.cd_start("корни")
            self.down = []
            self.roots = 0                                   # считаем «обвилось вокруг …» чужих и сообщаем итог
            threading.Timer(2, self.roots_report, (getattr(self, "roots_auto", False),)).start()
            self.roots_auto = False
        elif s.startswith("Вы произнесли магические слова 'полиморф'"):
            self.cd_start("поли")
        elif s.startswith("Вы вновь можете использовать заклинание "):
            if "'живые корни'" in s:
                self.cd_clear("корни")
                self.down = []
                self.chek_say("живые корни откатились — слежу за сбитыми врагами")
            elif "'полиморф'" in s:
                self.cd_clear("поли")
                self.send_raw("гг морф готов")
                self.chek_say("полиморф откатился — «морф готов» в группу")
        elif self.cd_ready("корни"):                    # на кд корней сбитых не считаем
            now = time.time()
            down = [(k, t) for k, t in getattr(self, "down", []) if now - t < 12]      # сбитый встаёт сам: старше 12 с не в счёте
            if m := self.UP.match(s):
                k = self.down_key(m.group(1))
                for e in down:
                    if e[0] == k:
                        down.remove(e)
                        break
            elif (m := self.DOWN.match(s)):
                n = next(g for g in m.groups() if g)
                if not self.is_ours(n) and n.strip().lower() != "вас":
                    down.append((self.down_key(n), now))
                    if len(down) > 3:
                        self.chek_say(f"сбито врагов: {len(down)} — живые корни")
                        self.cd_start("корни")
                        self.roots_auto = True
                        self.send_raw("к живы.корни")
                        down = []
            self.down = down

    def staf_line(self, plain, p):
        """Лидер (Зорон/Тадия) отсортировал группу — игра отвечает «Группа отсортирована…» только ему: проверяем стаф группы."""
        if NAME.lower() in self.CHEK_LEADERS and (plain[p.end():] if p else plain).startswith("Группа отсортирована")                 and time.time() - getattr(self, "staf_t", 0) > 60:
            self.staf_t = time.time()
            self.send_cmd("стафгр")

    def poly_move(self):
        """При переходе на другую клетку: цели лидера есть и полиморф готов — кастуем и сбрасываем."""
        t = getattr(self, "poly_targets", None)
        if NAME.lower() not in self.DRUID or not t:
            return
        self.poly_targets = None
        if not self.cd_ready("поли"):
            return
        self.cd_start("поли")
        self.send_raw("к полим " + t)
        self.chek_say("полиморф: к полим " + t)

    def rescue_set(self, r):
        """Включить/выключить автореск; список номеров запоминается в реск_<имя>.txt и поднимается после перезапуска клиента."""
        self.rescue = r
        try:
            with open(os.path.join(HERE, f"реск_{NAME}.txt"), "w", encoding="utf-8") as f:
                f.write(r)
        except OSError:
            pass
        self.chek_say("автореск: " + (f"спас {r}" if r else "выключен"))
        if r and not getattr(self, "res_loop", False):
            self.res_loop = True
            threading.Thread(target=self.rescue_loop, daemon=True).start()

    def rescue_round(self):
        """Раунд автореска: спас <номера>; нет ни одной строки про спасение -> рескать некого -> пом; яр х."""
        # Игра выполняет команды по очереди, и «молиться» во время проверки встаёт в хвост очереди. Поэтому в игре всегда
        # не больше одной нашей команды: следующую шлём только когда пришёл ответ на предыдущую (при задержке — пропускаем раунд).
        done = re.compile(r"Но никто не сражается|^(Вы|%s)\b.*спас|Вы не можете|Вы не видите здесь|Вы уже" % NAME, re.I)
        done_any = re.compile(r"^Вы |Кому именно|Но никто|не можете", re.I)

        def cmd(c, pat=done, wait=4.0):
            q = self.res_q = queue.Queue()
            self.send_raw(c)
            end, got = time.time() + wait, None
            while time.time() < end and got is None:
                try:
                    l = q.get(timeout=0.2)
                    got = l if pat.search(l) else None
                except queue.Empty:
                    pass
            self.res_q = None
            return got

        r = cmd("спас " + self.rescue)
        if r is None:                                   # ответа нет — игра отстаёт, ничего не добавляем в очередь
            return
        if re.search(r"^(Вы|%s)\b.*спас" % NAME, r, re.I):
            return                                      # спасли (или пытались)
        if cmd("пом", done_any) is None:                        # по списку рескать некого («Но никто не сражается с …») -> пом; яр х
            return
        if time.time() - getattr(self, "yar_t", 0) >= 10:           # яр х — не чаще раза в 5 раундов (~10 с)
            self.yar_t = time.time()
            cmd("яр х", done_any)

    def rescue_loop(self):
        """Автореск работает всегда, пока включён: раз в раунд (~2 с), в бою и вне боя, при смене клетки тоже."""
        while getattr(self, "rescue", "") and self.state != "off":
            t = time.time()
            self.rescue_round()
            time.sleep(max(0.0, 2.0 - (time.time() - t)))
        self.res_loop = False

    CHEK_BAD = re.compile(r"^(НЕТ|ЛИШНЕЕ|НОВОЕ|НАДЕТО|сбой|-сет не выполнен|нет запомненной)|^\S+: (НЕТ|ЛИШНЕЕ|НАДЕТО|нет сохранённой)|МАЛО|не прочитан")

    def chek_say(self, s):
        if self.CHEK_BAD.search(s):
            self.chek_bad = getattr(self, "chek_bad", 0) + 1
        self.emit("sys", "ЧЕК: " + s)

    def chek_cmd(self, cmd, until=None, quiet=0.8):
        """Послать команду и собрать строки ответа до until(строка) или до паузы quiet секунд."""
        q = self.chek_q = queue.Queue()
        self.send_raw(cmd)
        out = []
        while True:
            try:
                ln = q.get(timeout=quiet)
            except queue.Empty:
                break
            out.append(ln)
            if until and until(ln):
                break
        self.chek_q = None
        return out

    def chek_read_eq(self):
        rx = re.compile(r"^\s*<([^>]+)>\s+(.+?)(?:\s*\[[^\]]*\])?(?:\s*\.\.\..*)?\s*$")
        return ["<" + m.group(1).strip() + "> " + m.group(2).strip() for m in map(rx.match, self.chek_cmd("экип")) if m]

    def chek_diff(self, saved, rows):
        # парные вещи (запястья, пальцы, руки) надеваются на любую сторону: «левой/правой» в слоте при сверке не считаем
        norm = lambda r: re.sub(r"^<[^>]*>", lambda m: re.sub(r"\b(лев|прав)\w*\s*", "", m.group(0)), r)
        miss, extra = list(saved), list(rows)
        for r in saved:
            hit = next((x for x in extra if norm(x) == norm(r)), None)
            if hit is not None:
                extra.remove(hit)
                miss.remove(r)
        return miss, extra

    def chek_saved(self):
        try:
            with open(os.path.join(HERE, f"экип_{NAME}.txt"), encoding="utf-8") as f:
                return [x.strip() for x in f if x.strip()]
        except OSError:
            return None

    def chek_stuff(self):
        rows = self.chek_read_eq()
        if not rows:
            return self.chek_say("экипировка не прочитана (ничего не надето?) — запомненное не трогаю")
        want = self.CHEK_EXPECT.get(NAME.lower())
        if want and len(rows) < want:
            self.chek_say(f"НАДЕТО {len(rows)} ИЗ {want}")
        saved = self.chek_saved()
        if saved is not None:
            miss, extra = self.chek_diff(saved, rows)
            for r in miss:
                self.chek_say("НЕТ: " + r)
            for r in extra:
                self.chek_say("НОВОЕ: " + r)
            if not miss and not extra:
                self.chek_say(f"экипировка совпала с запомненной ({len(rows)})")
        with open(os.path.join(HERE, f"экип_{NAME}.txt"), "w", encoding="utf-8") as f:
            f.write("\n".join(rows) + "\n")
        self.chek_say(f"экипировка запомнена: {len(rows)} вещей (экип_{NAME}.txt)")
        self.chek_slot18(rows)

    def chek_slot18(self, rows):
        """Переменная Слот18 — слово-название вещи из 18-й строки экипа (для «сня $Слот18»)."""
        if len(rows) < 18 or not self.profile:
            return
        name = re.sub(r"^<[^>]*>\s*", "", rows[17])
        words = re.findall(r"[А-Яа-яЁёA-Za-z0-9-]+", name)
        if words:
            self.profile.vars["Слот18"] = ".".join(words).lower()          # название целиком, слова через точки
            self.chek_say(f"Слот18 = {self.profile.vars['Слот18']}")

    def chek_kolby(self):
        """Количество расходников — по инвентарю (`инв`: «название [N]»), без осмотра зарядов."""
        have, on = {}, False
        for l in self.chek_cmd("инв", quiet=1.2):
            if "Вы несете" in l:
                on = True
            elif on and (m := re.match(r"^\s+(.+?)(?:\s*\[(\d+)\])?\s*$", l)):
                words = re.findall(r"[а-яё]+", m.group(1).lower())
                for key, _, _ in self.CHEK_ITEMS:
                    if any(w.startswith(key) for w in words):
                        have[key] = have.get(key, 0) + int(m.group(2) or 1)
        if not on:
            return self.chek_say("инвентарь не прочитан (команда «инв»)")
        for key, need, word in self.CHEK_ITEMS:
            total = have.get(key, 0)
            self.chek_say(f"{key}: {total} (нужно {need})" + (f"   МАЛО {word}" if total < need else ""))

    def chek_do_unset(self, n):
        dept = self.profile.vars.get("СетОтдел")
        if not dept:
            return self.chek_say("не задан отдел сета: #variable {СетОтдел} {барб2}")
        sdai = self.profile.expand("сдай") if "сдай" in self.profile.aliases else []    # сначала расходники обратно на склад
        for c in sdai + ["сня все", f"кс :{dept} все{n}"]:
            self.send_raw(c)
        self.profile.vars["Сет"] = "0"
        self.chek_say(f"-сет: снял, {n} вещей в :{dept}")

    def chek_unset(self):
        if NAME.lower() in self.CHEK_LEADERS:
            self.chek_group_verify()
        time.sleep(1.5)
        rows, saved = self.chek_read_eq(), self.chek_saved()
        if not saved:
            self.chek_pending = len(rows)
            return self.chek_say("нет запомненной экипировки, -сет не выполнен. «окей» — раздеть всё равно")
        miss, extra = self.chek_diff(saved, rows)
        if not miss and not extra:
            return self.chek_do_unset(len(saved))
        for r in miss:
            self.chek_say("НЕТ: " + r)
        for r in extra:
            self.chek_say("ЛИШНЕЕ: " + r)
        self.chek_pending = len(saved)
        self.chek_say("-сет не выполнен. «окей» — раздеть всё равно")

    def at_storage(self):
        """Проверки группы — только на клетке со складом («Склад»): «груп сортв» в зоне их не запускает."""
        c = self.cur or {}
        name, zone = c.get("name", "").strip().lower(), c.get("area", "").lower()
        # «Склад» есть в Эрдере, Галене, Ривенделле, Элендоре, Геоланте…; в Артуанели, лагере гоблинов и Шиаре названия клеток
        # складов не видели — берём любую клетку со словом «склад» в этих зонах
        return name == "склад" or ("склад" in name and any(z in zone for z in ("артуанел", "гоблин", "шиар")))

    def chek_group_names(self):
        """Группа по таблице «гр»: имена игроков без меня (питомцы — со строчной буквы — не осматриваем)."""
        self.group = None
        self.send_raw("гр")
        time.sleep(1.5)
        names = [re.sub(r"^\d+\s+", "", m["name"]).strip() for m in (self.group or {}).get("members", [])]
        return [n for n in names if n[:1].isupper() and not NAME.lower().startswith(n.lower()[:4])]

    def chek_look(self, nm):
        return [m.group(0).strip() for m in (re.match(r"^\s*<[^>]+>.*$", l) for l in self.chek_cmd(f"осм {nm}")) if m]

    def chek_group_ref(self, nm):
        try:
            with open(os.path.join(HERE, f"экип_гр_{nm.lower()}.txt"), encoding="utf-8") as f:
                return [x.strip() for x in f if x.strip()]
        except OSError:
            return None

    def chek_group(self, wait=0):
        """Проверка стафа группы (как «!чекстаф» у других лидеров): осмотреть каждого, сказать в группу, каких слотов не хватает,
        запомнить надетое (экип_гр_<имя>.txt). wait — подождать, пока оденутся («гг !+сет»)."""
        from collections import Counter
        if not self.at_storage():
            c = self.cur or {}
            return self.chek_say(f"проверка стафа группы — только на складе, пропущена (клетка «{c.get('name', '?')}», зона «{c.get('area', '?')}»)")
        time.sleep(wait)
        names = self.chek_group_names()
        if not names:
            return self.chek_say("в группе никого, кроме меня" if self.group else "группа не прочитана (команда «гр»)")
        self.send_raw("гг Запускаю проверку стафа")
        slots = lambda rows: Counter(re.match(r"<([^>]+)>", r).group(1) for r in rows)
        own = self.chek_saved() or []
        for nm in names:
            rows = self.chek_look(nm)
            ref = self.chek_group_ref(nm)
            want = self.CHEK_EXPECT.get(nm.lower())
            base = ref or (own if want and len(own) == want else None)     # образец: прошлый осмотр, иначе мой комплект при том же числе вещей
            miss = (slots(base) - slots(rows)) if base else Counter()
            if not rows:
                self.chek_say(f"{nm}: ничего не видно")
                continue
            for sl, c in miss.items():                  # по строке на слот, как у остальных лидеров: «Съезо: <используется как обувь>»
                for _ in range(c):
                    self.send_raw(f"гг {nm}: <{sl}>")
                    self.chek_say(f"{nm}: НЕТ <{sl}>")
            if not miss and want and len(rows) < want:
                self.send_raw(f"гг {nm}: надето {len(rows)} из {want}")
                self.chek_say(f"{nm}: НАДЕТО {len(rows)} ИЗ {want}")
            elif not miss:
                self.chek_say(f"{nm}: надето {len(rows)}, всё на месте")
            if not miss or ref is None:                 # образец обновляем только полным комплектом
                with open(os.path.join(HERE, f"экип_гр_{nm.lower()}.txt"), "w", encoding="utf-8") as f:
                    f.write("\n".join(rows) + "\n")
        self.send_raw("гг Проверка стафа закончена")

    def chek_group_verify(self):
        """Перед -сет: экипировка группы сверяется с сохранённой (после проверки стафа). Только отчёт, -сет не задерживает."""
        if not self.at_storage():
            return
        names = self.chek_group_names()
        if not names:
            return self.chek_say("в группе никого, кроме меня" if self.group else "группа не прочитана — экипировку группы не сверить")
        ok = 0
        for nm in names:
            ref, rows = self.chek_group_ref(nm), self.chek_look(nm)
            if ref is None:
                self.chek_say(f"{nm}: нет сохранённой экипировки")
                continue
            miss, extra = self.chek_diff(ref, rows)
            for r in miss:
                self.chek_say(f"{nm}: НЕТ {r}")
            for r in extra:
                self.chek_say(f"{nm}: ЛИШНЕЕ {r}")
            ok += not (miss or extra)
        self.chek_say(f"экипировка группы совпала с сохранённой у {ok} из {len(names)}")

    def chek_worker(self):
        while True:
            what = self.chek_jobs.get()
            try:
                self.chek(what)
            except Exception as e:
                self.chek_say(f"сбой: {e!r}")

    def chek(self, what):
        if what == "окей":
            n, self.chek_pending = getattr(self, "chek_pending", None), None
            return self.chek_do_unset(n) if n else self.chek_say("нечего подтверждать")
        self.chek_bad = 0
        try:
            if what == "проверка":
                time.sleep(3)                          # после одевания дать вещам надеться
            if what in ("чс", "проверка"):
                self.chek_stuff()
            if what in ("чколб", "проверка"):
                self.chek_kolby()
            if what == "-сет":
                self.chek_unset()
            if what in ("сетгр", "стафгр"):
                self.chek_group(8 if what == "сетгр" else 0)
            self.chek_say(f"ИТОГ: проблем {self.chek_bad}" if self.chek_bad else "ИТОГ: всё в порядке")
        finally:
            self.chek_q = None

    def sync_vars(self):
        v = self.profile.vars
        if self.st.get("level"):
            v["MyLVL"] = str(self.st["level"])
        if self.cur:
            v["MsdpRoomVnum"], v["MsdpRoomName"], v["MsdpRoomArea"] = self.cur["vnum"], self.cur["name"], self.cur["area"]
        if self.st.get("hp") is not None:
            v["MsdpHealth"], v["MsdpHealthMax"] = str(self.st["hp"]), str(self.st.get("hpm", ""))

    def run_triggers(self, plain):
        if not self.profile or not self.profile.enabled or self.state != "game":
            return
        if re.search(r"парол|Enter Charset", plain, re.I):      # вход делает сервер сам; пароль — только человек
            return
        self.sync_vars()
        cmds, fired = self.profile.triggers(plain)
        if not cmds:
            return
        now = time.time()
        self.trig_times = [t for t in getattr(self, "trig_times", []) if now - t < 10] + [now] * len(cmds)
        if len(self.trig_times) > 40:
            self.profile.enabled = False
            try:    # что именно вызвало лавину — в файл, чтобы разобрать
                with open(os.path.join(HERE, f"обрывы_{NAME}.log"), "a", encoding="utf-8") as f:
                    f.write(f"{time.strftime('%d.%m %H:%M:%S')} триггеры выключены (>40 команд за 10 с): {plain[:80]!r} -> {cmds[:5]}\n")
            except Exception:
                pass
            self.emit("trigs", False)
            self.emit("alert", "Триггеры выключены: больше 40 команд за 10 с (зацикливание?)")
            return
        self.emit("sys", "⚡ " + "; ".join(cmds)[:200])
        for c in cmds:
            self.send_cmd(c)

    def safe_text(self, s):
        try:
            self.text(s)
        except Exception:
            import traceback
            try:
                with open(os.path.join(HERE, f"ошибки_{NAME}.log"), "a", encoding="utf-8") as f:
                    f.write(time.strftime("%d.%m %H:%M:%S") + chr(10) + traceback.format_exc() + chr(10))
            except Exception:
                pass

    def reader(self):
        mode, verb, sb = 0, 0, bytearray()
        try:
            while True:
                d = self.sock.recv(8192)
                if not d:
                    break
                out = bytearray()
                for b in d:
                    if mode == 0:
                        if b == IAC:
                            mode = 1
                        else:
                            out.append(b)
                    elif mode == 1:
                        if b == IAC:
                            out.append(255); mode = 0
                        elif b in (DO, DONT, WILL, WONT):
                            verb = b; mode = 2
                        elif b == SB:
                            sb = bytearray(); mode = 3
                        else:
                            mode = 0
                    elif mode == 2:
                        self.negotiate(verb, b); mode = 0
                    elif mode == 3:
                        if b == IAC:
                            mode = 4
                        else:
                            sb.append(b)
                    elif mode == 4:
                        if b == SE:
                            if out:
                                self.safe_text(bytes(out).decode(ENC, "replace")); out = bytearray()
                            if sb and sb[0] == MSDP:
                                try:
                                    self.on_msdp(bytes(sb[1:]))
                                except Exception as e:
                                    print("msdp:", e)
                            mode = 0
                        else:
                            if b == IAC:
                                sb.append(255)
                            mode = 3
                if out:
                    self.safe_text(bytes(out).decode(ENC, "replace"))
        except OSError as e:
            why = f"сбой сокета: {e!r}"
        else:
            why = "сервер игры закрыл соединение (EOF)"
        try:    # причина обрыва — в отдельный файл, чтобы потом разбирать
            with open(os.path.join(HERE, f"обрывы_{NAME}.log"), "a", encoding="utf-8") as f:
                f.write(f"{time.strftime('%d.%m %H:%M:%S')} {why}; жила {int(time.time() - getattr(self, 't_conn', time.time()))} с, state={self.state}\n")
        except Exception:
            pass
        was_game = self.state == "game"
        self.connected = False
        self.state = "off"
        self.emit("sys", "Соединение закрыто.")
        self.emit("status", "off")
        if not getattr(self, "user_closed", False) and was_game:     # обрыв связи -> переподключиться самому (до пароля)
            self.emit("alert", f"{NAME}: связь оборвалась, переподключаюсь через 1 с")
            threading.Timer(1, self.connect).start()

    def negotiate(self, verb, opt):
        if opt == MSDP and verb == WILL:
            if not self.msdp_on:
                self.request_msdp()
            return
        reply = DONT if verb == WILL else WONT if verb == DO else None
        if reply is not None:
            self.raw(bytes([IAC, reply, opt]))


MUD = Mud()


# ======================= HTTP =======================
class H(BaseHTTPRequestHandler):
    def log_message(self, *a):
        pass

    def _send(self, code, body, ctype="text/plain; charset=utf-8"):
        b = body.encode("utf-8") if isinstance(body, str) else body
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(b)))
        self.send_header("Cache-Control", "no-store")
        if self.path.startswith("/api/state"):          # окно второго персонажа читает точные хп
            self.send_header("Access-Control-Allow-Origin", "*")
        self.end_headers()
        self.wfile.write(b)

    def _json(self, obj):
        self._send(200, json.dumps(obj, ensure_ascii=False), "application/json; charset=utf-8")

    def do_GET(self):
        u = urlparse(self.path)
        q = {k: v[0] for k, v in parse_qs(u.query).items()}
        try:
            if u.path in ("/", "/index.html"):
                with open(os.path.join(HERE, "index.html"), "rb") as f:
                    self._send(200, f.read(), "text/html; charset=utf-8")
            elif u.path == "/events":
                self.events()
            elif u.path == "/log":
                n = int(q.get("from", 0))
                self._json({"next": len(MUD.lines), "lines": MUD.lines[n:], "partial": MUD.partial, "state": MUD.state})
            elif u.path == "/api/state":
                self._json(MUD.snapshot())
            elif u.path == "/api/hiz":                      # сообщение Хизмедара: гонг, не чаще раза в минуту
                if time.time() - MUD.hiz_t > 60:
                    MUD.hiz_t = time.time()
                    play(SOUND_HIZ)
                self._send(200, "ok")
            elif u.path == "/api/info":
                self._json({"name": NAME, "port": WEB_PORT, "autolook": MUD.autolook, "app": APP_NAME, "version": VERSION, "windows": len(MUD.subs),
                            "connected": MUD.connected})
            elif u.path == "/api/profiles":
                self._json({"current": NAME, "list": profiles_list()})
            elif u.path == "/api/gags":
                self._json(gag_list())
            elif u.path == "/api/profile":
                self._json(MUD.profile.summary() if MUD.profile else {})
            elif u.path == "/api/triggers":
                if MUD.profile and "on" in q:      # без on — только прочитать (раньше выключало триггеры)
                    MUD.profile.enabled = q.get("on") == "1"
                    MUD.emit("trigs", MUD.profile.enabled)
                self._json({"enabled": bool(MUD.profile and MUD.profile.enabled)})
            elif u.path == "/api/quit":                    # закрыть сервер, у которого нет окна (вызывает другое окно при выборе профиля)
                if MUD.subs:
                    self._json({"ok": False})
                else:
                    self._json({"ok": True})
                    MUD.disconnect()
                    threading.Timer(0.5, lambda: os._exit(0)).start()
            elif u.path == "/api/hidemap":
                MUD.hide_map = q.get("on") == "1"
                self._json({"hidemap": MUD.hide_map})
            elif u.path == "/api/autolook":
                MUD.autolook = q.get("on") == "1"
                MUD.emit("autolook", MUD.autolook)
                self._json({"autolook": MUD.autolook})
            elif u.path == "/api/zones":
                cnt = defaultdict(int)
                for r in load_world().values():
                    cnt[r[0]] += 1
                c = db()
                mobs = {r[0]: r[1] for r in c.execute("select zone,count(*) from mob_cards group by zone")}
                c.close()
                self._json([{"zone": z, "rooms": n, "mobs": mobs.get(z, 0)} for z, n in sorted(cnt.items(), key=lambda x: str(x[0]))])
            elif u.path == "/api/zone":
                self._json(layout(q["name"]))
            elif u.path == "/api/mobs":
                c = db()
                rows = c.execute("""select m.name,m.level,m.prof,m.hp,m.skills,
                    (select round(avg(exp)) from mob_kills k where k.zone=m.zone and k.name=m.name) as exp,
                    (select count(*) from mob_kills k where k.zone=m.zone and k.name=m.name) as kills
                    from mob_cards m where m.zone=? order by m.level,m.name""", (q["zone"],)).fetchall()
                c.close()
                self._json([dict(r) for r in rows])
            elif u.path == "/api/walks":
                c = db()
                rows = [dict(r) for r in c.execute("select name,path,end_vnum,note from speedwalks order by name")
                        if not r["name"].lstrip("﻿").startswith("#")]
                c.close()
                self._json(rows)
            elif u.path == "/api/path":
                p = find_path(q["a"], q["b"])
                self._json({"path": p, "words": [DIRW[d] for d in p] if p else None})
            else:
                self._send(404, "нет")
        except Exception as e:
            self._send(500, f"ошибка: {e!r}")

    def events(self):
        self.send_response(200)
        self.send_header("Content-Type", "text/event-stream")
        self.send_header("Cache-Control", "no-cache")
        self.end_headers()
        q = queue.Queue()
        MUD.subs.append(q)
        try:
            self.wfile.write(b"data: " + json.dumps({"t": "init", "d": MUD.snapshot()}, ensure_ascii=False).encode("utf-8") + b"\n\n")
            self.wfile.flush()
            while True:
                try:
                    msg = q.get(timeout=15)
                    self.wfile.write(b"data: " + msg.encode("utf-8") + b"\n\n")
                except queue.Empty:
                    self.wfile.write(b": ping\n\n")
                self.wfile.flush()
        except OSError:
            pass
        finally:
            MUD.subs.remove(q)

    def do_POST(self):
        ln = int(self.headers.get("Content-Length", 0))
        raw = self.rfile.read(ln)
        body = raw.decode("utf-8", errors="replace")
        u = urlparse(self.path)
        q = {k: v[0] for k, v in parse_qs(u.query).items()}
        self.path = u.path
        try:
            if self.path == "/grshow":
                MUD.grp_show = time.time() + 2.5; self._send(200, "ok")
            elif self.path == "/send":
                MUD.send_user(body); self._send(200, "ok")
            elif self.path == "/password":
                MUD.send_password(body, save=q.get("save") == "1"); self._send(200, "ok")
            elif self.path == "/api/newprofile":
                self._json(create_profile(q.get("name", ""), q.get("mode", "clean"), raw))
            elif self.path == "/connect":
                MUD.connect(); self._send(200, "ok")
            elif self.path == "/disconnect":
                MUD.disconnect(); self._send(200, "ok")
            elif self.path == "/api/restart":
                self._json({"ok": True})
                restart_self()
            elif self.path == "/api/pick":
                self._json(pick_profile(json.loads(body).get("name", "")))
            elif self.path == "/api/flag":
                d = json.loads(body)
                c = db()
                c.execute("CREATE TABLE IF NOT EXISTS room_flags (vnum TEXT, flag TEXT, PRIMARY KEY (vnum, flag))")
                if d.get("on", True):
                    c.execute("INSERT OR IGNORE INTO room_flags VALUES (?,?)", (str(d["vnum"]), d.get("flag", "hidden")))
                else:
                    c.execute("DELETE FROM room_flags WHERE vnum=? AND flag=?", (str(d["vnum"]), d.get("flag", "hidden")))
                c.commit(); c.close()
                self._json({"ok": True})
            elif self.path == "/api/profile":
                d = json.loads(body)
                MUD.profile.save_line(d.get("i"), d.get("line", ""))
                self._json(MUD.profile.summary())
            elif self.path == "/api/room_note":
                self._json(room_note(json.loads(body)))
            else:
                self._send(404, "нет")
        except Exception as e:
            self._send(500, f"ошибка: {e!r}")


def room_note(d):
    """Заметка к клетке/группе клеток: {"vnum"|"vnums", "text"} — добавить; {"del": id} — удалить."""
    c = db()
    ensure_notes(c)
    vn = [str(v) for v in (d.get("vnums") or ([d["vnum"]] if d.get("vnum") else []))]
    if d.get("del"):
        row = c.execute("select vnum,grp from room_notes where id=?", (int(d["del"]),)).fetchone()
        if row:
            vn = vn or [row["vnum"]]
            if row["grp"]:
                c.execute("DELETE FROM room_notes WHERE grp=?", (row["grp"],))
            else:
                c.execute("DELETE FROM room_notes WHERE id=?", (int(d["del"]),))
    elif d.get("text", "").strip() and vn:
        t = d["text"].strip()
        grp = ("g" + time.strftime("%y%m%d%H%M%S") + str(abs(hash(t)) % 1000)) if len(vn) > 1 else None
        ts = time.strftime("%d.%m.%Y %H:%M")
        for v in vn:
            c.execute("INSERT INTO room_notes (vnum,text,ts,grp) VALUES (?,?,?,?)", (v, t, ts, grp))
    c.commit()
    w = load_world()
    z = w.get(vn[0], [None])[0] if vn else None
    vset = {v for v, r in w.items() if r[0] == z} if z else set()
    out = notes_map(c, vset)
    c.close()
    return out


def restart_self():
    """Кнопка «Перезапуск»: отключиться от игры, запустить такой же сервер (тот же порт и профиль, сам зайдёт в игру), выйти.
    Окно (страница) то же: оно перезагрузится, когда новый сервер ответит."""
    import subprocess, sys
    args = [a for a in sys.argv[1:]]
    for k in ("--name",):                                    # профиль — тот, что сейчас открыт
        if k in args:
            i = args.index(k); del args[i:i + 2]
    args = [a for a in args if a not in ("--connect", "--restart")] + ["--restart"] + (["--name", NAME] if NAME else []) + (["--connect"] if NAME else [])
    flags = 0x00000008 | 0x08000000                          # DETACHED_PROCESS | CREATE_NO_WINDOW
    subprocess.Popen([sys.executable, "-X", "utf8", os.path.join(HERE, "server.py")] + args, cwd=HERE,
                     creationflags=flags, close_fds=True)
    MUD.disconnect()
    threading.Timer(1.0, lambda: os._exit(0)).start()


def auto_exit():
    """Режим отдельного окна: окна нет 30 с подряд -> отключиться от игры и выйти."""
    idle = 0
    while True:
        time.sleep(5)
        idle = idle + 5 if not MUD.subs else 0
        if idle >= 30:
            MUD.disconnect()
            time.sleep(1)
            os._exit(0)


USER_SAVED = {}
SET_KEEP = re.compile(r"^#(alias|action|variable|group|hot|substitute) ")
SET_SECRET = re.compile(r"парол|password|passw|\bpass\b|#con\b", re.I)


def profile_path(name):
    return os.path.join(HERE, f"профиль_{name}.txt")


def account_file(name=None):
    return os.path.join(HERE, f"аккаунт_{name or NAME}.txt")


def load_account(name):
    """Аккаунт профиля: аккаунт_<имя>.txt, строка 1 — имя пользователя, строка 2 — пароль (необязательно; хранится открытым текстом)."""
    try:
        ln = open(account_file(name), encoding="utf-8").read().splitlines()
    except OSError:
        return "", ""
    return (ln[0].strip() if ln else ""), (ln[1].strip() if len(ln) > 1 else "")


def save_account(name, user, pw):
    with open(account_file(name), "w", encoding="utf-8") as f:
        f.write(user + "\n" + (pw + "\n" if pw else ""))


def remember_account(name):
    """Имя аккаунта (не пароль) — чтобы в следующий раз ввести его самому."""
    global USER
    USER_SAVED["v"] = name
    if not USER:
        USER = name
        try:
            save_account(NAME, name, PW)
        except OSError:
            pass


def remember_password(pw):
    """Пароль, введённый человеком, по его галочке «запомнить» — в аккаунт_<имя>.txt."""
    global PW
    PW = pw
    try:
        save_account(NAME, USER, pw)
    except OSError:
        pass


def parse_set(text):
    """Файл .set JMC -> (строки профиля клиента, имя пользователя, пароль).
    Из .set берутся #alias/#action/#variable/#group/#hot/#substitute; триггеры входа («Введите имя…», «Пароль:»)
    уходят в аккаунт_<имя>.txt, а не в профиль."""
    keep, user, pw = [], "", ""
    for ln in text.splitlines():
        if not SET_KEEP.match(ln):
            continue
        m = re.match(r"^#action (?:TEXT )?\{(Введите имя своего пользователя|Пароль:)[^}]*\} \{([^}]*)\}", ln)
        if m:
            if m.group(1).startswith("Введите"):
                user = m.group(2).strip()
            else:
                pw = m.group(2).strip()
            continue
        if SET_SECRET.search(ln) and not ln.startswith("#substitute"):
            continue
        keep.append(ln)
    return keep, user, pw


def create_profile(name, mode, set_bytes=b""):
    """Новый профиль: mode 'clean' — пустой, 'set' — из файла .set JMC (cp1251)."""
    name = (name or "").strip()
    if not re.fullmatch(r"[\w\- ]{1,32}", name):
        return {"ok": False, "error": "имя: буквы, цифры, пробел, - и _ (до 32 знаков)"}
    if os.path.exists(profile_path(name)):
        return {"ok": False, "error": f"профиль {name} уже есть"}
    keep, user, pw = [], "", ""
    if mode == "set":
        keep, user, pw = parse_set(set_bytes.decode("cp1251", errors="replace"))
        if not keep:
            return {"ok": False, "error": "в файле нет алиасов и триггеров — это точно .set из JMC?"}
    with open(profile_path(name), "w", encoding="utf-8") as f:
        f.write(f"# Профиль клиента {name}: {'импорт из .set' if mode == 'set' else 'чистый'} {time.strftime('%d.%m.%Y %H:%M')}\n")
        if keep:
            f.write("\n".join(keep) + "\n")
    if user or pw:
        save_account(name, user, pw)
    return {"ok": True, "name": name, "lines": len(keep), "account": bool(user), "password": bool(pw)}


def other_windows():
    """Другие запущенные окна приложения: {имя профиля: порт} (порты 8765..8774)."""
    import urllib.request
    out = {}
    for p in range(8765, 8775):
        if p == WEB_PORT:
            continue
        try:
            with urllib.request.urlopen(f"http://127.0.0.1:{p}/api/info", timeout=0.4) as r:
                info = json.loads(r.read().decode("utf-8"))
            if info.get("name"):
                out[info["name"]] = (p, info.get("windows", 1))
        except Exception:
            pass
    return out


def profiles_list():
    """Доступные профили: профиль_<имя>.txt в папке клиента. busy — занят другим окном приложения."""
    names = [os.path.basename(f)[len("профиль_"):-len(".txt")] for f in sorted(glob.glob(os.path.join(HERE, "профиль_*.txt")))]
    busy = {n for n, (_p, w) in other_windows().items() if w > 0}       # сервер без окна (окно только что закрыли) — профиль свободен
    return [{"name": n, "busy": n in busy, "current": n == NAME} for n in names if n]


def pick_profile(name):
    """Выбрать профиль (персонажа) для этого окна: профиль клиента, аккаунт, лог. Только пока нет связи с игрой."""
    global NAME, USER, PW, LOG, MUD
    import jmcprofile as prof
    name = (name or "").strip()
    if not name or name not in [p["name"] for p in profiles_list()]:
        return {"ok": False, "error": "нет такого профиля"}
    others = other_windows()
    if name != NAME and name in others:
        port, wins = others[name]
        if wins > 0:
            return {"ok": False, "error": f"профиль {name} уже открыт в другом окне"}
        try:                                                 # старый сервер без окна ещё не закрылся сам — закрыть его (он отключится от игры)
            import urllib.request
            urllib.request.urlopen(f"http://127.0.0.1:{port}/api/quit", timeout=2).read()
        except Exception:
            pass
        time.sleep(1)
    if MUD.connected and name != NAME:
        return {"ok": False, "error": "сначала отключитесь от игры"}
    if name == NAME:
        return {"ok": True, "name": NAME}
    NAME = name
    USER, PW = load_account(NAME)
    USER_SAVED["v"] = USER
    LOG = os.path.join(HERE, f"game_{NAME}.log")
    new = Mud()                                           # чистое состояние; подписчики окна (SSE) те же
    new.subs = MUD.subs
    new.autolook = MUD.autolook
    new.profile = prof.Profile(NAME, profile_path(NAME), None)
    new.profile.enabled = MUD.profile.enabled if MUD.profile else TRIGGERS_DEFAULT
    MUD = new
    return {"ok": True, "name": NAME}


TRIGGERS_DEFAULT = False

def arg(name, default):
    import sys
    a = sys.argv
    return a[a.index(name) + 1] if name in a and a.index(name) + 1 < len(a) else default


if __name__ == "__main__":
    if "--popup" in sys.argv:                             # служебный режим: окно проверки (запускает сам клиент)
        i = sys.argv.index("--popup")
        popup_main(sys.argv[i + 1], sys.argv[i + 2], sys.argv[i + 3], sys.argv[i + 4] if len(sys.argv) > i + 4 else "0")
        sys.exit()
    if "--sounds" in sys.argv:                            # послушать все звуки по очереди
        for n in SOUNDS:
            print(n, flush=True)
            play(n)
            time.sleep(2.5)
        sys.exit()
    # python server.py [--port 8765] [--name Айлина] [--autolook] [--triggers] [--auto-exit]
    #   без --name профиль выбирается в окне (как в JMC)
    WEB_PORT = int(arg("--port", WEB_PORT))
    PORT = int(arg("--game-port", PORT))                  # порт игры (по умолчанию 5555; есть ещё 5190, 4000, 9000, 4662)
    if "--restart" in sys.argv:                           # ждём, пока старый сервер освободит порт (иначе он считает профиль занятым)
        import socket as _s
        for _ in range(60):
            with _s.socket() as c:
                if c.connect_ex(("127.0.0.1", WEB_PORT)) != 0:
                    break
            time.sleep(0.5)
    MUD.autolook = "--autolook" in sys.argv
    TRIGGERS_DEFAULT = "--triggers" in sys.argv
    if arg("--name", ""):
        r = pick_profile(arg("--name", ""))
        if not r["ok"]:
            print(r["error"])
            sys.exit(1)
        MUD.profile.enabled = TRIGGERS_DEFAULT
    print(f"{APP_NAME} {VERSION} ({NAME or 'профиль не выбран'}): http://localhost:{WEB_PORT}")
    threading.Thread(target=load_world, daemon=True).start()
    if "--auto-exit" in sys.argv:
        threading.Thread(target=auto_exit, daemon=True).start()
    for _ in range(60):                                   # после перезапуска старый сервер ещё может держать порт
        try:
            srv = ThreadingHTTPServer(("127.0.0.1", WEB_PORT), H)
            break
        except OSError:
            time.sleep(0.5)
    else:
        sys.exit("порт занят")
    if "--connect" in sys.argv and NAME:
        threading.Timer(1.5, MUD.connect).start()
    srv.serve_forever()