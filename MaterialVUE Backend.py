#!/usr/bin/env python3
"""MaterialVUE Backend: proxy for talking to StudentVUE to a unoffical client.
Stdlib only. Open http://127.0.0.1:8787/ after starting. Keep MaterialVUE.html next to this file.

Client flow:  GET /remembered -> POST /login | POST /resume -> POST /api/<Method> (+ POST /ping) -> POST /logout
Run:          python MaterialVUE_Backend.py   |   --selftest
Debug log:    add --log (strings redacted, shapes kept) or --log-raw (everything) -> MaterialVUE_log.txt next to this file

Behind a reverse proxy / tunnel (all work; the backend speaks plain HTTP on 127.0.0.1 and the proxy does TLS):
  Cloudflare Tunnel:  cloudflared tunnel --url http://127.0.0.1:8787 OR configure url in cloudflare networking web.
  Caddy:              reverse_proxy 127.0.0.1:8787
  nginx:              location / { proxy_pass http://127.0.0.1:8787;
                                   proxy_set_header Host $host;
                                   proxy_set_header X-Forwarded-For $proxy_add_x_forwarded_for;
                                   proxy_set_header X-Forwarded-Proto $scheme; }
  Proxy in Docker / another machine: add its address with MV_TRUSTED_PROXIES (comma-separated CIDRs).

Environment (all optional):
  MV_HOST / MV_PORT        bind address (default 127.0.0.1:8787)
  MV_TRUST_PROXY=0         ignore X-Forwarded-* / CF-Connecting-IP completely (default 1: honoured only from trusted peers)
  MV_TRUSTED_PROXIES       peers allowed to set those headers (default 127.0.0.0/8,::1/128)
  MV_COOKIE_SECURE         auto (default: Secure when the proxy says https) | 1 (always) | 0 (never)
  MV_ALLOWED_HOSTS         comma-separated hostnames this site may be served under; anything else is refused
  MV_SECRET                secret for the remember-me cookie (default: random key stored in MaterialVUE_secret.key)
  MV_REMEMBER=0            disable the remember-me feature entirely
  MV_REMEMBER_DAYS         remember-me lifetime, default 30
  MV_IDLE                  idle logout in seconds, default 300 (5 min); a live hall pass is exempt
  MV_SESSION_MAX           hard session lifetime in seconds, default 43200 (12 h)
  MV_RATE_ALL / MV_RATE_LOGIN   per-IP requests per minute (default 900 / 60; generous because a school shares one IP)
  MV_MAX_CONN              concurrent requests, default 64
  MV_ORIGIN                only for a separately hosted client (CORS); remember-me needs same-origin
"""
import base64, hashlib, hmac, ipaddress, json, os, re, secrets, sys, threading, time, urllib.error, urllib.request
import xml.etree.ElementTree as ET
from collections import deque
from http.cookies import CookieError, SimpleCookie
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, urlparse
from xml.sax.saxutils import escape


def env_int(name, default, lo, hi):
    try:
        v = int(os.environ.get(name, default))
    except ValueError:
        v = default
    return min(max(v, lo), hi)


HOST = os.environ.get("MV_HOST", "127.0.0.1")  # localhost only unless you opt in
PORT = int(os.environ.get("MV_PORT", "8787"))
ORIGIN = os.environ.get("MV_ORIGIN", "")  # CORS origin of a separately hosted client; empty = same-origin only
APP = "StudentVUE|Android|1.9.16"
MAX_BODY, MAX_RESP, MAX_SESSIONS = 64 * 1024, 25 * 1024 * 1024, 200
IDLE = env_int("MV_IDLE", 300, 60, 3600)  # seconds without user activity before the session is dropped
MAX_AGE = env_int("MV_SESSION_MAX", 12 * 3600, 600, 7 * 86400)  # absolute session lifetime
HP_GRACE, HP_MAX = 600, 2 * 3600  # a live hall pass keeps the session alive: refreshed by each sighting, capped at 2 h
RATE_ALL, RATE_LOGIN = env_int("MV_RATE_ALL", 900, 30, 100000), env_int("MV_RATE_LOGIN", 60, 5, 10000)
MAX_CONN = env_int("MV_MAX_CONN", 64, 4, 1024)
REMEMBER_ON = os.environ.get("MV_REMEMBER", "1") != "0"
REMEMBER_DAYS = env_int("MV_REMEMBER_DAYS", 30, 1, 365)
TRUST_PROXY = os.environ.get("MV_TRUST_PROXY", "1") != "0"
COOKIE_SECURE = os.environ.get("MV_COOKIE_SECURE", "auto").strip().lower()
ALLOWED_HOSTS = {h.strip().lower() for h in os.environ.get("MV_ALLOWED_HOSTS", "").split(",") if h.strip()}
try:
    TRUSTED_NETS = [ipaddress.ip_network(x.strip(), strict=False)
                    for x in os.environ.get("MV_TRUSTED_PROXIES", "127.0.0.0/8,::1/128").split(",") if x.strip()]
except ValueError as _e:
    sys.exit(f"MV_TRUSTED_PROXIES is not a valid list of CIDRs: {_e}")
HERE = os.path.dirname(os.path.abspath(__file__))
PAGE = os.path.join(HERE, "MaterialVUE.html")
LOGFILE = os.path.join(HERE, "MaterialVUE_log.txt")
KEYFILE = os.path.join(HERE, "MaterialVUE_secret.key")
LOGMODE = "raw" if "--log-raw" in sys.argv else "redacted" if "--log" in sys.argv else None
LOOKUP = "https://support.edupoint.com/Service/HDInfoCommunication.asmx"
LOOKUP_KEY = "5E4B7859-B805-474B-A833-FDB15D205D40"  # public, from the API docs

# Read-only calls, plus UpdateHallPass (the student's own hall pass). Other writes (absence, mail send, password, uploads...) are left out on purpose.
ALLOWED = {
    "GetChildListData", "StudentClassList", "GetStudentClasesForGivenDayResponse", "GetStudentClassTime",
    "Gradebook", "GetStudentAttendanceList", "GetStudentPastAttendanceData", "GetStudentInfoData",
    "GetCalendarData", "GetCalendarAssignmentDetails", "GetStudentDocuments", "GetStudentDocumentContent",
    "GetStudentHWNotes", "GetUserDefinedModule", "GetFlexScheduleData",
    "GetSchoolInformationData", "GetSchoologoResponse", "GetContentMyAccountData", "GetStudentDisciplineData",
    "GetStudentFeeData", "GetStudentSpecialEdData", "GetConferenceData", "GetHallPassData", "GetHallPassHistory",
    "GetHealthData", "GetLunchOrderInfoResponse", "GetHallPassSetup",
    "UpdateHallPass",  # the ONLY write allowed: requests / ends the student's own hall pass
}
BG_OK = {"GetChildListData", "GetHallPassData"}  # calls the page may mark as background polling (they don't count as user activity)

# SSRF guard: client picks the district host, so only *.edupoint.com or hosts Edupoint's own lookup returned.
HOST_RE = re.compile(r"^(?=.{4,253}$)([a-z0-9]([a-z0-9-]{0,61}[a-z0-9])?\.)+[a-z]{2,}$")
known_hosts = set()  # shortcut: in-memory, lost on restart; the remember-me cookie keeps the ZIP so custom domains are re-verified

sessions, slock, llock = {}, threading.Lock(), threading.Lock()
hits = {}
events = deque(maxlen=6)
stats = {"req": 0, "fail": 0, "limited": 0}  # shortcut: unlocked counters, may be off by one under load
started, stop, status = time.time(), threading.Event(), "STARTING"
CONN = threading.BoundedSemaphore(MAX_CONN)
KEY, KEY_SRC = None, ""


class Bad(Exception):
    def __init__(self, code, msg, cookies=()):
        self.code, self.msg, self.cookies = code, msg, list(cookies)


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


# ---------- proxy awareness: real client IP and scheme, trusted only from known proxy peers ----------
def norm_ip(s):
    try:
        ip = ipaddress.ip_address(str(s).strip().strip("[]"))
    except ValueError:
        return None
    return ip.ipv4_mapped if ip.version == 6 and ip.ipv4_mapped else ip


def trusted(ip):
    return ip is not None and any(ip in n for n in TRUSTED_NETS)


def from_proxy(peer):
    return TRUST_PROXY and trusted(norm_ip(peer))


def client_ip(peer, get):
    """Peer address, unless the peer is a trusted proxy: then CF-Connecting-IP, else the right-most untrusted X-Forwarded-For entry."""
    p = norm_ip(peer)
    if p is None:
        return str(peer)
    if not (TRUST_PROXY and trusted(p)):
        return str(p)  # untrusted peer: forwarded headers are attacker-controlled, ignore them
    cf = norm_ip(get("CF-Connecting-IP") or "")
    if cf:
        return str(cf)
    for part in reversed([x for x in (get("X-Forwarded-For") or "").split(",") if x.strip()]):
        ip = norm_ip(part)
        if ip is None:
            break
        if not trusted(ip):
            return str(ip)
    xr = norm_ip(get("X-Real-IP") or "")
    return str(xr) if xr else str(p)


def is_https(peer, get):
    if COOKIE_SECURE in ("1", "true", "yes", "always"):
        return True
    if COOKIE_SECURE in ("0", "false", "no", "never") or not from_proxy(peer):
        return False
    xfp = (get("X-Forwarded-Proto") or "").split(",")[0].strip().lower()
    return xfp == "https" if xfp else '"https"' in (get("CF-Visitor") or "").lower()


# ---------- authenticated encryption for the remember-me cookie (stdlib only) ----------
# Encrypt-then-MAC: HMAC-SHA256 used as the PRF in counter mode for the keystream, HMAC-SHA256 over version|nonce|ciphertext as the tag.
def _sub(key, label):
    return hmac.new(key, label, hashlib.sha256).digest()


def seal(key, data):
    nonce = os.urandom(16)
    ek, mk = _sub(key, b"mv-enc"), _sub(key, b"mv-mac")
    ks = b"".join(hmac.new(ek, nonce + i.to_bytes(4, "big"), hashlib.sha256).digest() for i in range((len(data) + 31) // 32))
    ct = bytes(a ^ b for a, b in zip(data, ks))
    tag = hmac.new(mk, b"\x01" + nonce + ct, hashlib.sha256).digest()
    return base64.urlsafe_b64encode(b"\x01" + nonce + ct + tag).rstrip(b"=").decode()


def unseal(key, token):
    try:
        raw = base64.urlsafe_b64decode(token + "=" * (-len(token) % 4))
    except (ValueError, TypeError):
        return None
    if len(raw) < 49 or raw[0] != 1:
        return None
    nonce, ct, tag = raw[1:17], raw[17:-32], raw[-32:]
    ek, mk = _sub(key, b"mv-enc"), _sub(key, b"mv-mac")
    if not hmac.compare_digest(tag, hmac.new(mk, b"\x01" + nonce + ct, hashlib.sha256).digest()):
        return None
    ks = b"".join(hmac.new(ek, nonce + i.to_bytes(4, "big"), hashlib.sha256).digest() for i in range((len(ct) + 31) // 32))
    return bytes(a ^ b for a, b in zip(ct, ks))


def load_key():
    s = os.environ.get("MV_SECRET")
    if s:
        return hashlib.sha256(b"mv-secret-v1:" + s.encode()).digest(), "MV_SECRET"
    try:
        with open(KEYFILE, "rb") as f:
            k = f.read().strip()
        if len(k) >= 32:
            return hashlib.sha256(b"mv-secret-v1:" + k).digest(), os.path.basename(KEYFILE)
    except OSError:
        pass
    k = secrets.token_hex(32).encode()
    try:
        with os.fdopen(os.open(KEYFILE, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600), "wb") as f:
            f.write(k)
        return hashlib.sha256(b"mv-secret-v1:" + k).digest(), os.path.basename(KEYFILE) + " (new)"
    except OSError:
        return hashlib.sha256(b"mv-secret-v1:" + k).digest(), "memory only (remember-me resets on restart)"


CK_SECURE, CK_PLAIN = "__Host-mv_remember", "mv_remember"


def cookie_set(value, secure):
    parts = [f"{CK_SECURE if secure else CK_PLAIN}={value}", "Path=/", "HttpOnly", "SameSite=Strict", f"Max-Age={REMEMBER_DAYS * 86400}"]
    return "; ".join(parts + (["Secure"] if secure else []))


def cookies_clear(secure):
    out = [f"{CK_PLAIN}=; Path=/; HttpOnly; SameSite=Strict; Max-Age=0"]
    if secure:
        out.insert(0, f"{CK_SECURE}=; Path=/; HttpOnly; SameSite=Strict; Max-Age=0; Secure")
    return out


def remember_pack(d, u, pw, z, name):
    return seal(KEY, json.dumps({"d": d, "u": u, "p": pw, "z": z, "n": name,
                                 "exp": int(time.time()) + REMEMBER_DAYS * 86400}, separators=(",", ":")).encode())


def remember_read(cookie_header, key=None):
    key = key or KEY
    if not (REMEMBER_ON and key and cookie_header):
        return None
    c = SimpleCookie()
    try:
        c.load(cookie_header)
    except CookieError:
        return None
    for name in (CK_SECURE, CK_PLAIN):
        m = c.get(name)
        raw = unseal(key, m.value) if m else None
        if raw:
            try:
                j = json.loads(raw)
            except ValueError:
                continue
            if (isinstance(j, dict) and j.get("exp", 0) > time.time()
                    and all(isinstance(j.get(k), str) for k in ("d", "u", "p", "z", "n"))):
                return j
    return None


# ---------- hall pass awareness and idle policy ----------
HP_END = re.compile(r"\b(end|complet|return|cancel|expir|deni|reject|done|clos|void)", re.I)  # same words the page uses


def hp_live(child):
    """True when StudentVUE shows a pending or active hall pass for the student."""
    if not isinstance(child, dict) or not child.get("studentHallPassGU"):
        return False
    st = str(child.get("hallPassStatus") or "").strip()
    return bool(st) and not HP_END.search(st)


def exempt(s, now):
    since = s.get("hp_since") or 0
    return bool(since) and s.get("hp_until", 0) > now and now - since < HP_MAX


def expired(s, now):
    return now - s["born"] > MAX_AGE or (now - s["active"] > IDLE and not exempt(s, now))


def note_hp(s, j):
    try:
        c = j["data"]["children"]["childrenList"][0]
    except (KeyError, IndexError, TypeError):
        c = None
    live, now = hp_live(c), time.time()
    with slock:
        if live:
            s["hp_since"] = s.get("hp_since") or now
            s["hp_until"] = now + HP_GRACE
        elif s.get("hp_since"):  # pass just ended: the idle clock starts now, not when the user last clicked
            s["hp_since"] = s["hp_until"] = 0
            s["active"] = now


def sweep():
    now = time.time()
    with slock:
        for k in [k for k, s in sessions.items() if expired(s, now)]:
            del sessions[k]
        return len(sessions)


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
    """Append one request/response pair to the debug log. Only /api calls: never credentials, tokens, cookies or session ids."""
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


def child_name(host, token):
    """Display name for the 'Or continue as ...' button. Best effort: an empty string just means the button shows the username."""
    try:
        _, raw = jcall(host, "GetChildListData", "Bearer " + token, {"legacyAppRequest": False, "secondaryLogin": False})
        c = json.loads(raw)["data"]["children"]["childrenList"][0]
        n = c.get("childName") or c.get("childFirstName") or ""
        return n.strip()[:80] if isinstance(n, str) else ""
    except Exception:
        return ""


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
    out = json.loads(raw)  # envelope passes through as-is; check data.error client-side (docs: errors are HTTP 200)
    if method == "GetChildListData":
        note_hp(s, out)
    return out


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


def new_session(host, t):
    sid, now = secrets.token_urlsafe(32), time.time()
    with slock:
        sessions[sid] = {"host": host, "access": t["access_token"], "refresh": t.get("refresh_token"), "born": now,
                         "active": now, "hp_since": 0, "hp_until": 0, "lock": threading.Lock()}
    return sid


def strip_port(h):
    return re.sub(r":\d+$", "", (h or "").strip().lower())


class Handler(BaseHTTPRequestHandler):
    timeout = 15  # drops slowloris connections
    server_version, sys_version = "MaterialVUE", ""

    def log_message(self, *a):  # never log request data
        pass

    def sec_headers(self):
        h = {"Cache-Control": "no-store", "X-Content-Type-Options": "nosniff", "Referrer-Policy": "no-referrer",
             "X-Frame-Options": "DENY", "Cross-Origin-Opener-Policy": "same-origin",
             "Permissions-Policy": "camera=(), microphone=(), geolocation=(), payment=(), usb=()"}
        if self.https:
            h["Strict-Transport-Security"] = "max-age=15552000"
        return h

    def reply(self, code, obj, cookies=()):
        self.code = code
        b = b"" if code == 204 else json.dumps(obj).encode()
        self.send_response(code)
        hdr = {"Content-Type": "application/json", "Content-Length": str(len(b)), **self.sec_headers(),
               "Content-Security-Policy": "default-src 'none'; frame-ancestors 'none'"}
        if ORIGIN:
            hdr.update({"Access-Control-Allow-Origin": ORIGIN, "Vary": "Origin",
                        "Access-Control-Allow-Headers": "Authorization, Content-Type, X-MV-Bg",
                        "Access-Control-Allow-Methods": "GET, POST, OPTIONS"})
        for k, v in hdr.items():
            self.send_header(k, v)
        for c in cookies:
            self.send_header("Set-Cookie", c)
        self.end_headers()
        if b:
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
        for k, v in {"Content-Type": "text/html; charset=utf-8", "Content-Length": str(len(b)),
                     "Content-Security-Policy": csp, **self.sec_headers()}.items():
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

    def session(self, background=False):
        a = self.headers.get("Authorization", "")
        tok = a[7:] if a.startswith("Bearer ") else None
        now = time.time()
        with slock:
            s = sessions.get(tok) if tok else None
            if s and expired(s, now):
                del sessions[tok]  # idle too long (and no live hall pass), or past its hard lifetime
                s = None
            if not s:
                raise Bad(401, "not logged in")
            if not background:
                s["active"] = now  # only real user actions count as activity, not the page's own polling
        if limited("s:" + tok[:16], "sess", 200):  # per-session fairness, so one noisy client can't eat a school's shared IP budget
            stats["limited"] += 1
            raise Bad(429, "rate limited")
        return s

    def check_host(self):
        if not ALLOWED_HOSTS:
            return
        cands = [self.headers.get("Host")]
        if self.proxied:
            cands.append((self.headers.get("X-Forwarded-Host") or "").split(",")[0])
        if not any(strip_port(c) in ALLOWED_HOSTS for c in cands):
            raise Bad(421, "unknown host")

    def check_csrf(self):
        """POSTs must come from our own page. Sec-Fetch-Site works behind any proxy; the Origin/Host comparison covers older browsers."""
        h = self.headers
        o = h.get("Origin")
        if ORIGIN and o == ORIGIN:
            return
        sfs = (h.get("Sec-Fetch-Site") or "").lower()
        if sfs:
            if sfs in ("same-origin", "none"):
                return
            raise Bad(403, "cross-site request blocked")
        if o:
            hosts = {strip_port(h.get("Host"))}
            if self.proxied:
                hosts.add(strip_port((h.get("X-Forwarded-Host") or "").split(",")[0]))
            try:
                net = strip_port(urlparse(o).netloc)
            except ValueError:
                net = ""
            if net not in hosts:
                raise Bad(403, "cross-site request blocked")

    def route(self, verb):
        ip, p = self.cip, urlparse(self.path)
        if self.headers.get("Transfer-Encoding"):
            raise Bad(400, "unsupported transfer encoding")  # request-smuggling guard: only Content-Length bodies
        self.check_host()
        if limited(ip, "all", RATE_ALL):
            stats["limited"] += 1
            raise Bad(429, "rate limited")
        if verb == "OPTIONS":
            return self.reply(204, {})
        if verb == "POST":
            self.check_csrf()
        if verb == "GET" and p.path in ("/", "/MaterialVUE"):
            return self.page()
        if verb == "GET" and p.path == "/health":
            return self.reply(200, {"ok": True, "logging": LOGMODE or "off"})  # lets the page warn users when debug logging is on
        if verb == "GET" and p.path == "/remembered":
            r = remember_read(self.headers.get("Cookie", ""))
            return self.reply(200, {"remembered": True, "name": r["n"], "district": r["d"], "username": r["u"]} if r else {"remembered": False})
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
            # shared school/NAT IPs: generous per-IP cap, strict per-IP+username cap, plus a per-username cap that ignores the IP
            if limited(ip, "login", RATE_LOGIN) or limited(ip, "login:" + u.lower(), 5) or limited("*", "loginu:" + u.lower(), 20, 300):
                stats["limited"] += 1
                raise Bad(429, "too many logins")
            z = str(b.get("zip", ""))
            z = z if re.fullmatch(r"\d{5}", z) else ""
            if not valid_host(d) and z:
                districts(z)  # custom-domain districts become known after a lookup
            if not valid_host(d):
                raise Bad(400, "unknown district")
            if len(sessions) >= MAX_SESSIONS and sweep() >= MAX_SESSIONS:
                raise Bad(503, "server busy")
            t = login(d, u, pw)
            if REMEMBER_ON and b.get("remember") is True:
                cookies = [cookie_set(remember_pack(d, u, pw, z, child_name(d, t["access_token"])), self.https)]
            else:
                cookies = cookies_clear(self.https) if self.headers.get("Cookie") else []  # opted out: drop any older saved login
            return self.reply(200, {"session": new_session(d, t)}, cookies)
        if p.path == "/resume":
            if not REMEMBER_ON:
                raise Bad(404, "not found")
            if limited(ip, "resume", 10):
                stats["limited"] += 1
                raise Bad(429, "too many attempts")
            r = remember_read(self.headers.get("Cookie", ""))
            if not r:
                raise Bad(401, "saved login invalid", cookies_clear(self.https))
            d, u, pw, z = r["d"], r["u"], r["p"], r["z"]
            if limited("*", "loginu:" + u.lower(), 20, 300):
                stats["limited"] += 1
                raise Bad(429, "too many logins")
            if not valid_host(d) and re.fullmatch(r"\d{5}", z):
                districts(z)
            if not valid_host(d):
                raise Bad(401, "saved login invalid", cookies_clear(self.https))
            if len(sessions) >= MAX_SESSIONS and sweep() >= MAX_SESSIONS:
                raise Bad(503, "server busy")
            try:
                t = login(d, u, pw)
            except Bad as e:
                if e.code == 401:  # password changed or account gone: the saved login is useless, so drop it
                    raise Bad(401, "saved login invalid", cookies_clear(self.https))
                raise
            name = r["n"] or child_name(d, t["access_token"])
            return self.reply(200, {"session": new_session(d, t)}, [cookie_set(remember_pack(d, u, pw, z, name), self.https)])  # sliding expiry
        if p.path == "/forget":
            return self.reply(200, {"ok": True}, cookies_clear(self.https))
        if p.path == "/ping":
            self.session()  # counts as user activity
            return self.reply(200, {"ok": True})
        if p.path == "/logout":
            self.session()
            with slock:
                sessions.pop(self.headers["Authorization"][7:], None)
            return self.reply(200, {"ok": True})
        if p.path.startswith("/api/") and p.path[5:] in ALLOWED:
            m = p.path[5:]
            b = self.body()
            return self.reply(200, call(self.session(background=m in BG_OK and self.headers.get("X-MV-Bg") == "1"), m, b))
        raise Bad(404, "not found")

    def handle_verb(self, verb):
        stats["req"] += 1
        self.code = 500
        peer = self.client_address[0]
        self.cip = client_ip(peer, self.headers.get)
        self.https = is_https(peer, self.headers.get)
        self.proxied = from_proxy(peer)
        if not CONN.acquire(blocking=False):
            self.reply(503, {"error": "server busy"})
        else:
            try:
                self.route(verb)
            except Bad as e:
                self.reply(e.code, {"error": e.msg}, e.cookies)
            except (OSError, ValueError, ET.ParseError):  # upstream down/garbage; never echo details to the client
                self.reply(502, {"error": "upstream unavailable"})
            except Exception:
                self.reply(500, {"error": "internal error"})
            finally:
                CONN.release()
        if self.code >= 400:
            stats["fail"] += 1
        safe = re.sub(r"[^\w/.-]", "?", urlparse(self.path).path)[:40]  # strips terminal escape codes
        events.append(f"{time.strftime('%H:%M:%S')}  {self.cip[:15]:<15} {verb:<7} {safe:<40} {self.code}")

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
        n = sweep()
        for k, q in list(hits.items()):  # prune idle rate-limit buckets
            if not q or q[-1] < now - 300:
                hits.pop(k, None)
        col = {"ONLINE": G, "STARTING": Y}.get(status, R)
        proxy = f"{G}trusted {', '.join(str(x) for x in TRUSTED_NETS)}{X}" if TRUST_PROXY else f"{Y}off{X}"
        warn = []
        if HOST not in ("127.0.0.1", "::1", "localhost"):
            warn.append(f"{R}  ! Bound to {HOST}: put TLS in front of this (Caddy / nginx / tunnel){X}")
        if not ALLOWED_HOSTS:
            warn.append(f"{Y}  ! Set MV_ALLOWED_HOSTS=your.domain to refuse other Host headers{X}")
        lines = [f"{B}{C}  MaterialVUE Backend{X}", f"{D}  {'-' * 56}{X}",
                 f"  Status    {col}{B}* {status}{X}", f"  Uptime    {G}{uptime()}{X}",
                 f"  Address   {C}http://{HOST}:{PORT}{X}", f"  Sessions  {Y}{n}{X}/{MAX_SESSIONS}   Idle logout {Y}{IDLE // 60}m{X} (hall pass exempt)",
                 f"  Proxy     {proxy}   Cookies {Y}{'secure auto' if COOKIE_SECURE == 'auto' else COOKIE_SECURE}{X}",
                 "  Remember  " + (f"{G}on, {REMEMBER_DAYS}d, key: {KEY_SRC}{X}" if REMEMBER_ON else f"{D}off{X}"),
                 "  Logging   " + {"redacted": f"{Y}ON (redacted) -> {os.path.basename(LOGFILE)}{X}",
                                  "raw": f"{R}{B}ON (RAW, contains personal data) -> {os.path.basename(LOGFILE)}{X}"}.get(LOGMODE, f"{D}off (--log to enable){X}"),
                 f"  Requests  {G}{stats['req']}{X}   Failed {R if stats['fail'] else D}{stats['fail']}{X}"
                 f"   Rate-limited {Y if stats['limited'] else D}{stats['limited']}{X}",
                 *warn, f"{D}  {'-' * 56}{X}", f"{D}  Recent{X}", *[f"{D}  {e}{X}" for e in events],
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
    assert not any(m.startswith((("Update", "Upload", "ForceChange"))) for m in ALLOWED - {"UpdateHallPass"}) and "UpdateHallPass" in ALLOWED
    assert not any(limited("x", "t", 3) for _ in range(3)) and limited("x", "t", 3)
    r = redact({"subject": "Hi Mr Smith", "id": "248086D8-70A8-4582-A6EB-4E960722DFC7", "n": 3, "t": True, "x": None,
                "d": "2026-08-26T09:38:09Z", "e": ["a@b.com"], "short": "en"})
    assert r == {"subject": "<str 11>", "id": "<guid>", "n": 3, "t": True, "x": None, "d": "<date>", "e": ["<str 7>"], "short": "en"}
    # cookie crypto: round trip, per-message nonce, wrong key, tampering, truncation, junk
    k = hashlib.sha256(b"test").digest()
    t = seal(k, b"hello world" * 10)
    assert unseal(k, t) == b"hello world" * 10 and seal(k, b"a") != seal(k, b"a")
    assert unseal(hashlib.sha256(b"other").digest(), t) is None
    assert unseal(k, t[:-3]) is None and unseal(k, "") is None and unseal(k, "!!!") is None
    flipped = t[:30] + ("A" if t[30] != "A" else "B") + t[31:]
    assert unseal(k, flipped) is None
    # remember cookie: valid, expired, wrong shape
    ck = SimpleCookie()
    ck[CK_PLAIN] = seal(k, json.dumps({"d": "a.edupoint.com", "u": "u", "p": "p", "z": "", "n": "N", "exp": int(time.time()) + 60}).encode())
    assert remember_read(ck.output(header="").strip(), k)["n"] == "N"
    ck[CK_PLAIN] = seal(k, json.dumps({"d": "a", "u": "u", "p": "p", "z": "", "n": "N", "exp": 1}).encode())
    assert remember_read(ck.output(header="").strip(), k) is None
    ck[CK_PLAIN] = seal(k, json.dumps({"d": "a", "u": 5, "p": "p", "z": "", "n": "N", "exp": int(time.time()) + 60}).encode())
    assert remember_read(ck.output(header="").strip(), k) is None
    # proxy-aware client address: spoofed headers from untrusted peers and left-most XFF entries are ignored
    g = lambda d: {k_.lower(): v for k_, v in d.items()}
    get = lambda d: (lambda n: g(d).get(n.lower()))
    assert client_ip("8.8.8.8", get({"X-Forwarded-For": "1.1.1.1", "CF-Connecting-IP": "2.2.2.2"})) == "8.8.8.8"
    assert client_ip("127.0.0.1", get({"X-Forwarded-For": "6.6.6.6, 9.9.9.9"})) == "9.9.9.9"
    assert client_ip("127.0.0.1", get({"CF-Connecting-IP": "2001:db8::1"})) == "2001:db8::1"
    assert client_ip("::ffff:127.0.0.1", get({"X-Real-IP": "7.7.7.7"})) == "7.7.7.7"
    assert client_ip("127.0.0.1", get({})) == "127.0.0.1"
    assert not is_https("8.8.8.8", get({"X-Forwarded-Proto": "https"})) or COOKIE_SECURE in ("1", "true", "yes", "always")
    # hall pass keeps a session alive; idle and hard limits drop it
    live = {"studentHallPassGU": "g", "hallPassStatus": "Approved"}
    assert hp_live(live) and hp_live({**live, "hallPassStatus": "Pending"}) and not hp_live({**live, "hallPassStatus": "Ended"})
    assert not hp_live({"hallPassStatus": "Active"}) and not hp_live({**live, "hallPassStatus": ""}) and not hp_live(None)
    s = {"born": 0, "active": 0}
    assert expired(s, IDLE + 1) and not expired(s, IDLE - 1)
    s.update(hp_since=1, hp_until=IDLE * 3)
    assert not expired(s, IDLE + 1) and expired(s, HP_MAX + 5)
    s["hp_until"] = 5
    assert expired(s, IDLE + 1)
    print("selftest ok")


if __name__ == "__main__":
    if "--selftest" in sys.argv:
        sys.exit(selftest())
    KEY, KEY_SRC = load_key()
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
