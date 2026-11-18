# -*- coding: utf-8 -*-
"""Алиасы, триггеры, переменные персонажа — подмножество синтаксиса JMC.

Файл профиля клиента: МАД ГРАФИКА\\профиль_<имя>.txt (строки как в .set JMC).
При первом запуске копируется из .set персонажа (#alias, #action, #variable, #group, #hot) — сам .set не меняется.

Умеет: #alias {имя} {тело}; #action [TEXT] {шаблон} {тело} {приоритет} {группа}; #variable {имя} {значение};
#group disable <группа>; в телах: ';', #N повтор, %0..%9, $переменные, #var/#variable, #if {условие} {то} {иначе}.
Не умеет (пропускает, показывает в закладке): #scr, #showme, #math, #loop, #con и прочие # кроме названных.
"""
import os
import re
import time

SUPPORTED_HASH = re.compile(r"^#(\d+|var|variable|if|unvar|unvariable)\b", re.I)


def braces(s, i):
    """s[i] == '{' -> (содержимое, индекс после '}') с учётом вложенности."""
    depth, j = 0, i
    while j < len(s):
        if s[j] == "{":
            depth += 1
        elif s[j] == "}":
            depth -= 1
            if depth == 0:
                return s[i + 1:j], j + 1
        j += 1
    return s[i + 1:], len(s)


def args_of(s):
    """'#alias {a} {b} {c}' -> ['a','b','c'] (слова вне скобок тоже, например TEXT)."""
    out, i = [], 0
    while i < len(s):
        if s[i] == "{":
            a, i = braces(s, i)
            out.append(a)
        elif s[i].isspace():
            i += 1
        else:
            j = i
            while j < len(s) and not s[j].isspace() and s[j] != "{":
                j += 1
            out.append(s[i:j])
            i = j
    return out


def split_cmds(s):
    """Разбить по ';' вне фигурных скобок."""
    out, depth, cur = [], 0, []
    for ch in s:
        if ch == "{":
            depth += 1
        elif ch == "}":
            depth -= 1
        if ch == ";" and depth == 0:
            out.append("".join(cur)); cur = []
        else:
            cur.append(ch)
    out.append("".join(cur))
    return [x.strip() for x in out if x.strip()]


def jmc_pattern(p):
    """Шаблон триггера JMC -> (regex, карта номер_%N -> номер_группы)."""
    if len(p) > 1 and p.startswith("/") and p.rstrip().endswith("/"):
        rx = re.compile(p.strip()[1:-1])
        return rx, {n: n + 1 for n in range(10)}
    anchored = p.startswith("^")
    body = p[1:] if anchored else p
    parts = [x for x in re.split(r"(%\d)", body) if x != ""]
    rx, gmap, g = "", {}, 0
    for k, part in enumerate(parts):
        if re.fullmatch(r"%\d", part):
            g += 1
            gmap[int(part[1])] = g
            rx += "(.*)" if k == len(parts) - 1 else "(.*?)"
        else:
            rx += re.escape(part)
    return re.compile(("^" if anchored else "") + rx), gmap


class Profile:
    def __init__(self, name, path, set_path):
        self.name, self.path, self.set_path = name, path, set_path
        self.vars = {}
        self.enabled = False            # триггеры выполняются только если включено в окне
        self.load()

    # ---------- файл ----------
    def load(self):
        if not os.path.exists(self.path) and self.set_path and os.path.exists(self.set_path):
            # строки с паролем не копируем и не читаем дальше (правило «пароли не трогаю»)
            keep = [ln.rstrip("\r\n") for ln in open(self.set_path, encoding="cp1251", errors="replace")
                    if re.match(r"^#(alias|action|variable|group|hot) ", ln)
                    and not re.search(r"парол|password|passw|\bpass\b|#con\b", ln, re.I)]
            with open(self.path, "w", encoding="utf-8") as f:
                f.write(f"# Профиль клиента {self.name}: скопирован {time.strftime('%d.%m.%Y %H:%M')} из {self.set_path}\n")
                f.write("\n".join(keep) + "\n")
        self.lines = open(self.path, encoding="utf-8").read().splitlines() if os.path.exists(self.path) else []
        self.parse()

    def save_line(self, i, line):
        """i — номер строки (-1 — добавить); пустая line — удалить."""
        if i is None or i < 0:
            if line.strip():
                self.lines.append(line.strip())
        elif 0 <= i < len(self.lines):
            if line.strip():
                self.lines[i] = line.strip()
            else:
                del self.lines[i]
        with open(self.path, "w", encoding="utf-8") as f:
            f.write("\n".join(self.lines) + "\n")
        self.parse()

    def shared_path(self):
        """Общие триггеры группы «фк» — один файл рядом с профилями, у всех персонажей одни и те же."""
        return os.path.join(os.path.dirname(self.path), "фк.txt")

    def save_shared(self, j, line):
        """j — номер строки в фк.txt (-1 — добавить); пустая line — удалить."""
        if j < 0:
            self.shared.append(line.strip())
        elif j < len(self.shared):
            if line.strip():
                self.shared[j] = line.strip()
            else:
                del self.shared[j]
        with open(self.shared_path(), "w", encoding="utf-8") as f:
            f.write("\n".join(self.shared) + "\n")
        self.parse()

    def parse(self):
        self.aliases, self.actions, self.hots, self.disabled = {}, [], {}, set()
        try:
            self.shared = [x.rstrip() for x in open(self.shared_path(), encoding="utf-8").read().splitlines() if x.strip()]
        except OSError:
            self.shared = []
        # строки фк.txt идут после строк профиля; их номер i = -2 - j (отрицательный: «лежит в общем файле»)
        for i, ln in list(enumerate(self.lines)) + [(-2 - j, x) for j, x in enumerate(self.shared)]:
            s = ln.strip()
            if i <= -2 and not s.startswith("#action"):
                continue
            if s.startswith("#group disable "):
                self.disabled.add(s.split()[2])
                continue
            a = args_of(s)
            if not a:
                continue
            kind = a[0].lower()
            if kind == "#alias" and len(a) >= 3:
                self.aliases[a[1]] = {"i": i, "name": a[1], "body": a[2], "group": a[3] if len(a) > 3 else "",
                                      "ok": self.body_ok(a[2])}
            elif kind == "#action":
                rest = a[1:]
                if rest and rest[0].upper() == "TEXT":
                    rest = rest[1:]
                if len(rest) >= 2:
                    try:
                        rx, gmap = jmc_pattern(rest[0])
                    except re.error:
                        rx, gmap = None, {}
                    self.actions.append({"i": i, "pattern": rest[0], "body": rest[1],
                                         "prio": rest[2] if len(rest) > 2 else "5",
                                         "group": rest[3] if len(rest) > 3 else "default",
                                         "rx": rx, "gmap": gmap, "ok": bool(rx) and self.body_ok(rest[1])})
            elif kind == "#variable" and len(a) >= 3:
                self.vars.setdefault(a[1], a[2])
            elif kind == "#hot" and len(a) >= 3:
                self.hots[a[1]] = {"i": i, "key": a[1], "body": a[2]}
        self.actions.sort(key=lambda x: int(x["prio"]) if str(x["prio"]).isdigit() else 5)

    def command(self, line):
        """#alias {имя} {тело} [{группа}] / #action {шаблон} {тело} [{приоритет}] [{группа}] / #hot {клавиша} {тело} —
        добавить или заменить (с тем же именем/шаблоном/клавишей); #unalias {имя} / #unaction {шаблон} / #unhot {клавиша} — удалить."""
        a = args_of(line)
        k = a[0].lower()
        if k in ("#alias", "#action", "#hot") and len(a) >= 3:
            rest = [x for x in a[1:] if x.upper() != "TEXT"]
            key, body = rest[0], rest[1]
            if k == "#alias":
                new = "#alias {%s} {%s} {%s}" % (key, body, rest[2] if len(rest) > 2 else "claude")
                old = self.aliases.get(key)
            elif k == "#hot":
                new = "#hot {%s} {%s} {%s}" % (key, body, rest[2] if len(rest) > 2 else "default")
                old = self.hots.get(key)
            else:
                new = "#action TEXT {%s} {%s} {%s} {%s}" % (key, body, rest[2] if len(rest) > 2 else "5", rest[3] if len(rest) > 3 else "claude")
                old = next((t for t in self.actions if t["pattern"] == key), None)
            if k == "#action":                    # группа «фк» — в общий файл фк.txt (для всех персонажей), остальное — в профиль
                to_shared = (rest[3] if len(rest) > 3 else "") == "фк"
                if old and old["i"] <= -2:
                    self.save_shared(-2 - old["i"], new if to_shared else "")
                    if not to_shared:
                        self.save_line(-1, new)
                elif to_shared:
                    if old:
                        self.save_line(old["i"], "")
                    self.save_shared(-1, new)
                else:
                    self.save_line(old["i"] if old else -1, new)
            else:
                self.save_line(old["i"] if old else -1, new)
            return ("заменён: " if old else "добавлен: ") + new
        if k in ("#unalias", "#unaction", "#unhot") and len(a) >= 2:
            key = a[1]
            old = (self.aliases.get(key) if k == "#unalias" else self.hots.get(key) if k == "#unhot"
                   else next((t for t in self.actions if t["pattern"] == key), None))
            if not old:
                return "не нашёл: " + key
            if old["i"] <= -2:
                self.save_shared(-2 - old["i"], "")
            else:
                self.save_line(old["i"], "")
            return "удалён: " + key
        if k in ("#variable", "#group") and len(a) >= 2:
            self.save_line(-1, line)
            return "добавлено: " + line
        return "не понял: " + line

    @staticmethod
    def body_ok(body):
        for c in split_cmds(body):
            if c.startswith("#") and not SUPPORTED_HASH.match(c):
                return False
        return True

    # ---------- выполнение ----------
    def subst(self, s, args=None):
        if args is not None:
            s = re.sub(r"%(\d)", lambda m: args.get(int(m.group(1)), ""), s)
        return re.sub(r"\$([A-Za-zА-Яа-я_]\w*)", lambda m: str(self.vars.get(m.group(1), m.group(0))), s)

    def cond(self, c):
        c = self.subst(c).strip()
        m = re.match(r"^(.*?)\s*(==|!=|>=|<=|<|>|=)\s*(.*)$", c)
        if not m:
            return c not in ("", "0")
        a, op, b = m.group(1).strip(), m.group(2), m.group(3).strip()
        try:
            a, b = float(a), float(b)
        except ValueError:
            pass
        try:
            return {"==": a == b, "=": a == b, "!=": a != b, ">=": a >= b, "<=": a <= b, "<": a < b, ">": a > b}[op]
        except TypeError:
            return False

    def expand(self, line, args=None, depth=0, notes=None):
        """Строка ввода/тело -> список команд для игры."""
        notes = notes if notes is not None else []
        out = []
        if depth > 8:
            notes.append("слишком глубокая вложенность алиасов")
            return out
        for c in split_cmds(line) if (";" in line or "{" in line) else [line.strip()]:
            if not c:
                continue
            m = re.match(r"^#(\d+)\s+(.*)$", c)
            if m:
                for _ in range(int(m.group(1))):
                    out += self.expand(m.group(2), args, depth + 1, notes)
                continue
            if c.startswith("#"):
                a = args_of(c)
                k = a[0].lower()
                if k in ("#var", "#variable") and len(a) >= 3:
                    self.vars[self.subst(a[1], args)] = self.subst(a[2], args)
                elif k in ("#unvar", "#unvariable") and len(a) >= 2:
                    self.vars.pop(a[1], None)
                elif k == "#if" and len(a) >= 3:
                    branch = a[2] if self.cond(self.subst(a[1], args)) else (a[3] if len(a) > 3 else "")
                    out += self.expand(branch, args, depth + 1, notes)
                else:
                    notes.append("не умею: " + c[:60])
                continue
            word, _, rest = c.partition(" ")
            al = self.aliases.get(word)
            if al:
                ws = rest.split()
                aa = {0: rest}
                for n, w in enumerate(ws[:9], 1):
                    aa[n] = w
                out += self.expand(self.subst(al["body"], aa), None, depth + 1, notes)
            else:
                r = self.subst(c, args)
                if args and r != c and not r.startswith("#"):     # «!фраг» -> «фраг»: подставленное из текста игры тоже может быть алиасом
                    out += self.expand(r, None, depth + 1, notes)
                else:
                    out.append(r)
        return out

    def triggers(self, plain):
        """Строка игры -> команды сработавших триггеров (только если включено)."""
        if not self.enabled:
            return [], []
        cmds, fired = [], []
        for t in self.actions:
            if not t["ok"] or t["group"] in self.disabled:
                continue
            m = t["rx"].search(plain)
            if m:
                args = {n: (m.group(g) or "") for n, g in t["gmap"].items() if g <= (m.re.groups or 0)}
                cmds += self.expand(t["body"], args)
                fired.append(t["pattern"])
        return cmds, fired

    def summary(self):
        ln = lambda i: self.lines[i] if 0 <= i < len(self.lines) else ""
        return {"enabled": self.enabled, "file": self.path, "disabled_groups": sorted(self.disabled),
                "aliases": [dict(a, line=ln(a["i"])) for a in self.aliases.values()],
                "actions": [dict({k: v for k, v in t.items() if k not in ("rx", "gmap")}, line=ln(t["i"])) for t in self.actions],
                "hots": [dict(h, line=ln(h["i"])) for h in self.hots.values()], "vars": self.vars}
