' Pogonyaem lysogo - graphic client in its own window.
' Each launch = a new window on the first free port (8765..8774). The profile (Ailina/Kimpi/...) is chosen in the window.
' Two launches = two windows with two different profiles.
Option Explicit
Dim sh, fso, dir, url, edge, i, p, port, ok
Set sh = CreateObject("WScript.Shell")
Set fso = CreateObject("Scripting.FileSystemObject")
dir = fso.GetParentFolderName(WScript.ScriptFullName)

Function Alive(u)
  Dim x
  Alive = False
  On Error Resume Next
  Set x = CreateObject("MSXML2.ServerXMLHTTP")
  x.setTimeouts 500, 500, 500, 500
  x.open "GET", u & "/api/info", False
  x.send
  If Err.Number = 0 Then
    If x.status = 200 Then Alive = True
  End If
  On Error GoTo 0
End Function

port = 0
For p = 8765 To 8774
  If Not Alive("http://localhost:" & p) Then
    port = p
    Exit For
  End If
Next
If port = 0 Then
  MsgBox "All ports 8765..8774 are busy.", 16, "Pogonyaem lysogo"
  WScript.Quit
End If
url = "http://localhost:" & port

sh.CurrentDirectory = dir
sh.Run "pythonw -X utf8 server.py --auto-exit --port " & port & " --autolook --triggers", 0, False
ok = False
For i = 1 To 160
  WScript.Sleep 250
  If Alive(url) Then ok = True : Exit For
Next
If Not ok Then
  MsgBox "Server did not start (python server.py --port " & port & "). Python 3.10+ must be installed and added to PATH (python.org).", 16, "Pogonyaem lysogo"
  WScript.Quit
End If

edge = sh.ExpandEnvironmentStrings("%ProgramFiles(x86)%") & "\Microsoft\Edge\Application\msedge.exe"
If Not fso.FileExists(edge) Then edge = sh.ExpandEnvironmentStrings("%ProgramFiles%") & "\Google\Chrome\Application\chrome.exe"
sh.Run """" & edge & """ --app=" & url & " --window-size=1500,900 --user-data-dir=""" & _
  sh.ExpandEnvironmentStrings("%LOCALAPPDATA%") & "\SferaMirovApp""", 1, False
