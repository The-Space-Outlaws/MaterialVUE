#!/usr/bin/env python3
"""MaterialVUE Backend: secure JSON proxy for the new StudentVUE mobile API, and host of the MaterialVUE web UI.
Stdlib only. Open http://127.0.0.1:8787/ after starting. Keep MaterialVUE.html next to this file.

Client flow:  GET /districts?zip=94127  ->  POST /login  ->  POST /api/<Method>  ->  POST /logout
Run:          python "MaterialVUE Backend.py"   (env: MV_HOST, MV_PORT, MV_ORIGIN)   |   --selftest
Debug log:    add --log (strings redacted, shapes kept) or --log-raw (everything) -> MaterialVUE_log.txt next to this file
"""
import base64, json, os, re, secrets, sys, threading, time, urllib.error, urllib.request
import xml.etree.ElementTree as ET
from collections import deque
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, urlparse
from xml.sax.saxutils import escape

HOST = os.environ.get("MV_HOST", "127.0.0.1")  # localhost only unless you opt in
PORT = int(os.environ.get("MV_PORT", "8787"))
ORIGIN = os.environ.get("MV_ORIGIN", "")  # CORS origin of the client; empty = no CORS
APP = "StudentVUE|Android|1.9.16"
MAX_BODY, MAX_RESP, MAX_SESSIONS, IDLE = 64 * 1024, 25 * 1024 * 1024, 200, 2 * 3600
PAGE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "MaterialVUE.html")
LOGFILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "MaterialVUE_log.txt")
LOGMODE = "raw" if "--log-raw" in sys.argv else "redacted" if "--log" in sys.argv else None
LOOKUP = "https://support.edupoint.com/Service/HDInfoCommunication.asmx"
LOOKUP_KEY = "5E4B7859-B805-474B-A833-FDB15D205D40"  # public, from the API docs

# Read-only calls only. Writes (absence, mail send, password, uploads...) are left out on purpose.
ALLOWED = {
    "GetChildListData", "StudentClassList", "GetStudentClasesForGivenDayResponse", "GetStudentClassTime",
    "Gradebook", "GetStudentAttendanceList", "GetStudentPastAttendanceData", "GetStudentInfoData",
    "GetCalendarData", "GetCalendarAssignmentDetails", "GetStudentDocuments", "GetStudentDocumentContent",
    "GetStudentHWNotes", "GetPXPContentMessage", "GetUserDefinedModule", "GetFlexScheduleData",
    "GetSchoolInformationData", "GetSchoologoResponse", "GetContentMyAccountData", "GetStudentDisciplineData",
    "GetStudentFeeData", "GetStudentSpecialEdData", "GetConferenceData", "GetHallPassData", "GetHallPassHistory",
    "GetHealthData", "GetLunchOrderInfoResponse", "GetSynergyMailGetConversations", "GetSynergyMailMessage",
    "GetSynergyMailIGetMessageBody", "GetSynergyMailGetAttachment", "GetSynergyMailInboxCount",
    "GetSynergyMailUnreadCount", "GetSynergyMailGetTeacherList",
}

# SSRF guard: client picks the district host, so only *.edupoint.com or hosts Edupoint's own lookup returned.
HOST_RE = re.compile(r"^(?=.{4,253}$)([a-z0-9]([a-z0-9-]{0,61}[a-z0-9])?\.)+[a-z]{2,}$")
known_hosts = set()  # shortcut: in-memory, lost on restart; re-run /districts after a restart for custom domains

sessions, slock, llock = {}, threading.Lock(), threading.Lock()
hits = {}
events = deque(maxlen=6)
stats = {"req": 0, "fail": 0, "limited": 0}  # shortcut: unlocked counters, may be off by one under load
started, stop, status = time.time(), threading.Event(), "STARTING"


class Bad(Exception):
    def __init__(self, code, msg):
        self.code, self.msg = code, msg


def valid_host(h):
    return isinstance(h, str) and bool(HOST_RE.match(h)) and (h.endswith(".edupoint.com") or h in known_hosts)


def limited(ip, bucket, n, per=60):
    now = time.time()
    q = hits.setdefault((ip, bucket), deque())
    while q and q[0] < now - per:
        q.popleft()
    if len(q) >= n:
        return True
    q.append(now)
    return False


GUID_RE = re.compile(r"^[0-9A-Fa-f]{8}-([0-9A-Fa-f]{4}-){3}[0-9A-Fa-f]{12}")
DATE_RE = re.compile(r"^\d{1,4}[-/]\d{1,2}[-/]\d{1,4}([T ].*)?$")


def redact(v):  # keeps keys, numbers, booleans, nulls and short enums; hides names, emails, text, ids
    if isinstance(v, dict):
        return {k: redact(x) for k, x in v.items()}
    if isinstance(v, list):
        return [redact(x) for x in v]
    if isinstance(v, str) and len(v) > 4:
        return "<guid>" if GUID_RE.match(v) else "<date>" if DATE_RE.match(v) else f"<str {len(v)}>"
    return v


def record(title, inner, status_, raw):
    """Append one request/response pair to the debug log. Only /api calls: never credentials, tokens or session ids."""
    if not LOGMODE:
        return
    try:
        try:
            resp = json.loads(raw)
            if LOGMODE == "redacted":
                resp = redact(resp)
        except ValueError:
            resp = f"<non-json, {len(raw)} bytes>"
        if LOGMODE == "redacted":
            inner = redact(inner)
        text = (f"=== {time.strftime('%Y-%m-%d %H:%M:%S')}  {title}  HTTP {status_} ===\nREQUEST:\n{json.dumps(inner, indent=2)}\n"
                f"RESPONSE:\n{json.dumps(resp, indent=2)}\n\n")[:300_000]  # shortcut: cut entries may end mid-JSON; no rotation, delete the file when done
        with llock, os.fdopen(os.open(LOGFILE, os.O_WRONLY | os.O_APPEND | os.O_CREAT, 0o600), "a", encoding="utf-8") as f:
            f.write(text)
    except OSError:
        pass  # logging must never break a request


class NoRedirect(urllib.request.HTTPRedirectHandler):  # redirects could leak credentials / hit internal hosts
    def redirect_request(self, *a, **k):
        return None


opener = urllib.request.build_opener(NoRedirect)


def upstream(url, headers, body):
    req = urllib.request.Request(url, data=body, headers=headers, method="POST")
    try:
        with opener.open(req, timeout=20) as r:
            status_, raw = r.status, r.read(MAX_RESP + 1)
    except urllib.error.HTTPError as e:
        status_, raw = e.code, e.read(MAX_RESP + 1)
    if len(raw) > MAX_RESP:
        raise ValueError("upstream too large")
    return status_, raw


def jcall(host, method, auth, inner=None, bare=False):
    h = {"Content-Type": "application/json", "User-Agent": "ksoap", "AppNameOSAndVersion": APP, "Authorization": auth}
    body = {} if bare else {"arguments": {"request": json.dumps(inner or {})}}
    return upstream(f"https://{host}/api/v1/mobile/PXPWebServices/{method}", h, json.dumps(body).encode())


def login(host, user, pw):
    basic = "Basic " + base64.b64encode(f"{user}:{pw}".encode()).decode()
    _, raw = jcall(host, "AttemptLogin", basic, {"userID": None, "password": None, "userType": "Student"})
    j = json.loads(raw)
    if not isinstance(j, dict) or not j.get("access_token"):
        raise Bad(401, "login failed")
    return j


def call(s, method, inner):
    used = s["access"]
    st, raw = jcall(s["host"], method, "Bearer " + used, inner)
    if st == 401 and s["refresh"]:
        with s["lock"]:  # one refresh at a time; others reuse the new token
            if s["access"] == used:
                st2, raw2 = jcall(s["host"], "RefreshToken", "Bearer " + s["refresh"], bare=True)
                j = json.loads(raw2) if st2 == 200 else {}
                if not isinstance(j, dict) or not j.get("access_token"):
                    raise Bad(401, "session expired")
                s["access"], s["refresh"] = j["access_token"], j.get("refresh_token") or s["refresh"]
        st, raw = jcall(s["host"], method, "Bearer " + s["access"], inner)
    record(method, inner, st, raw)
    if st == 401:
        raise Bad(401, "session expired")
    if st != 200:
        raise Bad(502, "upstream error")
    return json.loads(raw)  # envelope passes through as-is; check data.error client-side (docs: errors are HTTP 200)


def districts(zip_):
    param = f"<Parms><Key>{LOOKUP_KEY}</Key><MatchToDistrictZipCode>{zip_}</MatchToDistrictZipCode></Parms>"
    env = ('<soapenv:Envelope xmlns:soapenv="http://schemas.xmlsoap.org/soap/envelope/" xmlns:web="http://edupoint.com/webservices/">'
           "<soapenv:Header/><soapenv:Body><web:ProcessWebServiceRequestMultiWeb><web:userID></web:userID><web:password></web:password>"
           "<web:skipLoginLog>1</web:skipLoginLog><web:parent>0</web:parent><web:webDBName></web:webDBName>"
           "<web:webServiceHandleName>HDInfoServices</web:webServiceHandleName>"  # methodName below comes from memory, not the docs
           f"<web:methodName>GetMatchingDistrictList</web:methodName><web:paramStr>{escape(param)}</web:paramStr>"
           "</web:ProcessWebServiceRequestMultiWeb></soapenv:Body></soapenv:Envelope>")
    _, raw = upstream(LOOKUP, {"Content-Type": "text/xml; charset=utf-8"}, env.encode())
    inner = next((e.text for e in ET.fromstring(raw).iter() if e.tag.endswith("ProcessWebServiceRequestMultiWebResult")), None)
    out = []
    for d in (ET.fromstring(inner).iter("DistrictInfo") if inner else []):
        u = urlparse(d.get("PvueURL", ""))
        h = (u.hostname or "").lower()
        if u.scheme == "https" and HOST_RE.match(h):
            known_hosts.add(h)
            out.append({"id": d.get("DistrictID"), "name": d.get("Name"), "address": d.get("Address"), "host": h})
    return out


class Handler(BaseHTTPRequestHandler):
    timeout = 15  # drops slowloris connections
    server_version, sys_version = "MaterialVUE", ""

    def log_message(self, *a):  # never log request data
        pass

    def reply(self, code, obj):
        self.code = code
        b = json.dumps(obj).encode()
        self.send_response(code)
        hdr = {"Content-Type": "application/json", "Content-Length": str(len(b)), "Cache-Control": "no-store",
               "X-Content-Type-Options": "nosniff", "Referrer-Policy": "no-referrer"}
        if ORIGIN:
            hdr.update({"Access-Control-Allow-Origin": ORIGIN, "Vary": "Origin",
                        "Access-Control-Allow-Headers": "Authorization, Content-Type",
                        "Access-Control-Allow-Methods": "GET, POST, OPTIONS"})
        for k, v in hdr.items():
            self.send_header(k, v)
        self.end_headers()
        self.wfile.write(b)

    def page(self):
        try:
            with open(PAGE, encoding="utf-8") as f:
                html = f.read()
        except OSError:
            raise Bad(404, "MaterialVUE.html not found next to the backend")
        n = secrets.token_urlsafe(16)  # per-response nonce: only our own inline script may run
        b = html.replace("{{NONCE}}", n).encode()
        self.code = 200
        self.send_response(200)
        csp = (f"default-src 'none'; script-src 'nonce-{n}' https://esm.run https://cdn.jsdelivr.net; "
               "style-src 'unsafe-inline' https://fonts.googleapis.com; font-src https://fonts.gstatic.com; "
               "img-src 'self' data:; connect-src 'self'; base-uri 'none'; form-action 'none'; frame-ancestors 'none'")
        for k, v in {"Content-Type": "text/html; charset=utf-8", "Content-Length": str(len(b)), "Cache-Control": "no-store",
                     "Content-Security-Policy": csp, "X-Content-Type-Options": "nosniff", "Referrer-Policy": "no-referrer"}.items():
            self.send_header(k, v)
        self.end_headers()
        self.wfile.write(b)

    def body(self):
        try:
            n = int(self.headers.get("Content-Length") or 0)
        except ValueError:
            raise Bad(400, "bad length")
        if not 0 <= n <= MAX_BODY:
            raise Bad(413, "body too large")
        if n == 0:
            return {}
        try:
            j = json.loads(self.rfile.read(n))
        except ValueError:
            raise Bad(400, "bad json")
        if not isinstance(j, dict):
            raise Bad(400, "body must be a json object")
        return j

    def session(self):
        a = self.headers.get("Authorization", "")
        with slock:
            s = sessions.get(a[7:]) if a.startswith("Bearer ") else None
            if not s:
                raise Bad(401, "not logged in")
            s["seen"] = time.time()
        return s

    def route(self, verb):
        ip, p = self.client_address[0], urlparse(self.path)
        if limited(ip, "all", 120):
            stats["limited"] += 1
            raise Bad(429, "rate limited")
        if verb == "OPTIONS":
            return self.reply(204, {})
        if verb == "GET" and p.path in ("/", "/MaterialVUE"):
            return self.page()
        if verb == "GET" and p.path == "/health":
            return self.reply(200, {"ok": True})
        if verb == "GET" and p.path == "/districts":
            z = parse_qs(p.query).get("zip", [""])[0]
            if not re.fullmatch(r"\d{5}", z):
                raise Bad(400, "zip must be 5 digits")
            return self.reply(200, {"districts": districts(z)})
        if verb != "POST":
            raise Bad(404, "not found")
        if p.path == "/login":
            b = self.body()
            d, u, pw = str(b.get("district", "")).lower(), b.get("username"), b.get("password")
            if not (isinstance(u, str) and isinstance(pw, str) and 0 < len(u) <= 128 and 0 < len(pw) <= 128 and ":" not in u):
                raise Bad(400, "bad credentials format")
            # shared school/NAT IPs: generous per-IP cap, strict per-IP+username cap against guessing
            if limited(ip, "login", 30) or limited(ip, "login:" + u, 5):
                stats["limited"] += 1
                raise Bad(429, "too many logins")
            z = str(b.get("zip", ""))
            if not valid_host(d) and re.fullmatch(r"\d{5}", z):
                districts(z)  # custom-domain districts become known after a lookup; survives restarts if client sends zip
            if not valid_host(d):
                raise Bad(400, "unknown district")
            if len(sessions) >= MAX_SESSIONS:
                raise Bad(503, "server busy")
            t = login(d, u, pw)  # password is never stored or logged
            sid = secrets.token_urlsafe(32)
            with slock:
                sessions[sid] = {"host": d, "access": t["access_token"], "refresh": t.get("refresh_token"),
                                 "seen": time.time(), "lock": threading.Lock()}
            return self.reply(200, {"session": sid})
        if p.path == "/logout":
            s = self.session()
            with slock:
                sessions.pop(self.headers["Authorization"][7:], None)
            return self.reply(200, {"ok": True})
        if p.path.startswith("/api/") and p.path[5:] in ALLOWED:
            b = self.body()
            return self.reply(200, call(self.session(), p.path[5:], b))
        raise Bad(404, "not found")

    def handle_verb(self, verb):
        stats["req"] += 1
        self.code = 500
        try:
            self.route(verb)
        except Bad as e:
            self.reply(e.code, {"error": e.msg})
        except (OSError, ValueError, ET.ParseError):  # upstream down/garbage; never echo details to the client
            self.reply(502, {"error": "upstream unavailable"})
        except Exception:
            self.reply(500, {"error": "internal error"})
        if self.code >= 400:
            stats["fail"] += 1
        safe = re.sub(r"[^\w/.-]", "?", urlparse(self.path).path)[:40]  # strips terminal escape codes
        events.append(f"{time.strftime('%H:%M:%S')}  {self.client_address[0]:<15} {verb:<7} {safe:<40} {self.code}")

    do_GET = lambda self: self.handle_verb("GET")
    do_POST = lambda self: self.handle_verb("POST")
    do_OPTIONS = lambda self: self.handle_verb("OPTIONS")


def uptime():
    d, s = divmod(int(time.time() - started), 86400)
    h, s = divmod(s, 3600)
    m, s = divmod(s, 60)
    return f"{d}d {h:02}h {m:02}m {s:02}s"


def dashboard():
    G, R, Y, C, D, B, X = "\033[92m", "\033[91m", "\033[93m", "\033[96m", "\033[90m", "\033[1m", "\033[0m"
    while True:
        now = time.time()
        with slock:
            for k in [k for k, s in sessions.items() if now - s["seen"] > IDLE]:
                del sessions[k]
            n = len(sessions)
        for k, q in list(hits.items()):  # prune idle rate-limit buckets
            if not q or q[-1] < now - 60:
                hits.pop(k, None)
        col = {"ONLINE": G, "STARTING": Y}.get(status, R)
        lines = [f"{B}{C}  MaterialVUE Backend{X}", f"{D}  {'-' * 56}{X}",
                 f"  Status    {col}{B}* {status}{X}", f"  Uptime    {G}{uptime()}{X}",
                 f"  Address   {C}http://{HOST}:{PORT}{X}", f"  Sessions  {Y}{n}{X}/{MAX_SESSIONS}",
                 "  Logging   " + {"redacted": f"{Y}ON (redacted) -> {os.path.basename(LOGFILE)}{X}",
                                  "raw": f"{R}{B}ON (RAW, contains personal data) -> {os.path.basename(LOGFILE)}{X}"}.get(LOGMODE, f"{D}off (--log to enable){X}"),
                 f"  Requests  {G}{stats['req']}{X}   Failed {R if stats['fail'] else D}{stats['fail']}{X}"
                 f"   Rate-limited {Y if stats['limited'] else D}{stats['limited']}{X}",
                 f"{D}  {'-' * 56}{X}", f"{D}  Recent{X}", *[f"{D}  {e}{X}" for e in events],
                 f"{D}  Ctrl+C to stop{X}"]
        sys.stdout.write("\033[2J\033[3J\033[H" + "\n".join(lines) + "\n")
        sys.stdout.flush()
        if stop.wait(1):
            return


def selftest():
    assert valid_host("abc.edupoint.com") and not valid_host("edupoint.com.evil.com")
    assert not valid_host("127.0.0.1") and not valid_host("evil.com/.edupoint.com") and not valid_host("a.edupoint.com:99")
    assert not valid_host("evil.com") and not valid_host(None)
    known_hosts.add("sv.district.k12.us")
    assert valid_host("sv.district.k12.us")
    assert not any(m.startswith(("Update", "Upload", "ForceChange")) for m in ALLOWED)
    assert not any(limited("x", "t", 3) for _ in range(3)) and limited("x", "t", 3)
    r = redact({"subject": "Hi Mr Smith", "id": "248086D8-70A8-4582-A6EB-4E960722DFC7", "n": 3, "t": True, "x": None,
                "d": "2026-08-26T09:38:09Z", "e": ["a@b.com"], "short": "en"})
    assert r == {"subject": "<str 11>", "id": "<guid>", "n": 3, "t": True, "x": None, "d": "<date>", "e": ["<str 7>"], "short": "en"}
    print("selftest ok")


if __name__ == "__main__":
    if "--selftest" in sys.argv:
        sys.exit(selftest())
    os.system("")  # enables ANSI colors on Windows terminals
    srv = ThreadingHTTPServer((HOST, PORT), Handler)
    srv.daemon_threads = True
    threading.Thread(target=dashboard, daemon=True).start()
    status = "ONLINE"
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        pass
    status = "OFFLINE"
    stop.set()
    time.sleep(1.1)
    srv.server_close()
