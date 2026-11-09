#!/usr/bin/env python3
"""Build approach-sectors-data.js from the French eAIP (ENR 2.2.4.2).

Stdlib only. Run once per AIRAC cycle:

    py tools/build_approach_sectors.py --airac 2026-10-29 --folder eAIP_29_OCT_2026

Pages, OSM border ways and terrain samples are cached per AIRAC under --cache.
The build stops on any remark or lateral-limit wording it does not recognise,
so a new AIP phrasing can never be dropped silently.
"""
import argparse
import heapq
import json
import math
import re
import sys
import tempfile
import time
import urllib.error
import urllib.parse
import urllib.request
from collections import Counter
from html.parser import HTMLParser
from pathlib import Path

UA = "French-vACC-approach-map-build/1.0"
NM_M = 1852.0
R_NM = 3440.065
BORDER_TOL_M = 30  # Douglas-Peucker tolerance for border segments

COUNTRY_RELATIONS = {
    "ES": 1311341, "IT": 365331, "DE": 51477, "CH": 51701, "BE": 52411, "LU": 2171347,
}
BORDER_WORDS = {
    "franco-allemande": "DE", "franco-suisse": "CH", "franco-luxembourgeoise": "LU",
    "franco-belge": "BE", "franco-italienne": "IT", "franco-espagnole": "ES",
}

# Same callsign/colour/position as the markers in index.html.
APP_META = {
    "AJACCIO": ("Ajaccio", "Ajaccio Approach", "LFKJ_APP", 41.9239, 8.8025, "#C084FC"),
    "AQUITAINE": ("Bordeaux", "Aquitaine Approach", "LFBD_BW_APP", 44.8333, -0.6, "#00BCD4"),
    "BALE MULHOUSE": ("Bale-Mulhouse", "Bale Control", "LFSB_C_APP", 47.59, 7.5292, "#FFA726"),
    "BASTIA": ("Bastia", "Bastia Approach", "LFKB_APP", 42.6667, 9.5, "#FFC107"),
    "BEAUVAIS": ("Beauvais", "Beauvais Approach", "LFOB_APP", 49.4544, 2.1128, "#66BB6A"),
    "BIARRITZ": ("Biarritz", "Biarritz Approach", "LFBZ_APP", 43.4683, -1.5311, "#AB47BC"),
    "CLERMONT": ("Clermont-Ferrand", "Clermont Approach", "LFLC_CF_APP", 45.7667, 3.0667, "#8BC34A"),
    "IROISE": ("Brest", "Iroise Approach", "LFRB_APP", 48.4472, -4.4217, "#D946EF"),
    "LA ROCHELLE": ("La Rochelle", "La Rochelle Approach", "LFBH_APP", 46.1792, -1.1953, "#7E57C2"),
    "LILLE": ("Lille", "Lille Approach", "LFQQ_QE_APP", 50.6333, 3.05, "#9C27B0"),
    "LIMOGES": ("Limoges", "Limoges Approach", "LFBL_APP", 45.8608, 1.1803, "#EF5350"),
    "LYON": ("Lyon", "Lyon Approach", "LFLL_VW_APP", 45.75, 4.8333, "#FF5722"),
    "MONTPELLIER": ("Montpellier", "Montpellier Approach", "LFMT_FE_APP", 43.6167, 3.8667, "#009688"),
    "NANTES": ("Nantes", "Nantes Approach", "LFRS_APP", 47.2, -1.55, "#F44336"),
    "NICE": ("Nice", "Nice Approach", "LFMN_NO_APP", 43.7, 7.2333, "#673AB7"),
    "POITIERS": ("Poitiers", "Poitiers Approach", "LFBI_APP", 46.5876, 0.3067, "#26A69A"),
    "PROVENCE": ("Marseille", "Provence Approach", "LFML_ME_APP", 43.3, 5.3833, "#795548"),
    "PYRENEES": ("Pau", "Pyrenees Approach", "LFBT_APP", 43.1856, -0.0028, "#42A5F5"),
    "RENNES": ("Rennes", "Rennes Approach", "LFRN_APP", 48.1167, -1.6833, "#607D8B"),
    "SEINE": ("Seine", "Seine Approach", "LFPM_SJ_APP", 48.4333, 2.1667, "#E91E63"),
    "STRASBOURG": ("Strasbourg", "Strasbourg Control", "LFST_SU_APP", 48.5333, 7.6167, "#03A9F4"),
    "TOULOUSE": ("Toulouse", "Toulouse Approach", "LFBO_AE_APP", 43.6167, 1.45, "#FF9800"),
}

# Positions on the bandbox map that ENR 2.2.4.2 does not publish sectors for.
NOT_PUBLISHED = [
    "De Gaulle Approach (LFPG_N_APP)", "Orly Approach (LFPO_APP)",
    "Le Bourget Approach (LFPT_APP)", "Chambery Approach (LFLB_APP)",
]

CONDITIONS = {
    "app-landivisiau": "Landivisiau APP active",
    "app-lorient": "Lorient APP active",
    "cta-rhone-2": "CTA Rhône part 2 active",
    "cta-rhone-3": "CTA Rhône part 3 active",
    "cta-rhone-4": "CTA Rhône part 4 active",
    "channel-islands": "Jersey / Channel Islands airspace active",
    "ctr-lfrk": "CTR Caen (LFRK) active",
    "ctr-lfrg": "CTR Deauville (LFRG) active",
}


# ---------------------------------------------------------------- fetching

def fetch(url, dest, data=None):
    if dest.exists():
        return dest.read_bytes()
    req = urllib.request.Request(url, data=data, headers={"User-Agent": UA})
    for attempt in range(4):
        try:
            with urllib.request.urlopen(req, timeout=240) as r:
                body = r.read()
            break
        except urllib.error.HTTPError as e:  # Overpass answers 429/502/504 when busy
            if attempt == 3 or e.code not in (429, 502, 503, 504):
                raise
            time.sleep(30 * (attempt + 1))
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_bytes(body)
    return body


class Rows(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.rows, self.tr, self.td = [], None, None

    def handle_starttag(self, tag, attrs):
        if tag == "tr":
            self.tr = []
        elif tag in ("td", "th") and self.tr is not None:
            self.td = []
        elif tag == "br" and self.td is not None:
            self.td.append("\n")

    def handle_endtag(self, tag):
        if tag in ("td", "th") and self.td is not None:
            self.tr.append("".join(self.td).replace("\xa0", " "))
            self.td = None
        elif tag == "tr" and self.tr is not None:
            self.rows.append(self.tr)
            self.tr = None

    def handle_data(self, data):
        if self.td is not None:
            self.td.append(data)


def rows_of(html_text):
    p = Rows()
    p.feed(html_text)
    return p.rows


def squash(s):
    return re.sub(r"\s+", " ", s).strip()


# ---------------------------------------------------------------- geometry

def bearing_dist(c, p):
    """Spherical bearing (deg) and distance (NM) from c to p."""
    la1, lo1, la2, lo2 = map(math.radians, (c[0], c[1], p[0], p[1]))
    dl = lo2 - lo1
    h = math.sin((la2 - la1) / 2) ** 2 + math.cos(la1) * math.cos(la2) * math.sin(dl / 2) ** 2
    d = 2 * R_NM * math.asin(min(1, math.sqrt(h)))
    y = math.sin(dl) * math.cos(la2)
    x = math.cos(la1) * math.sin(la2) - math.sin(la1) * math.cos(la2) * math.cos(dl)
    return math.degrees(math.atan2(y, x)) % 360, d


def destination(c, brg, dist):
    la1, lo1, b, d = math.radians(c[0]), math.radians(c[1]), math.radians(brg), dist / R_NM
    la2 = math.asin(math.sin(la1) * math.cos(d) + math.cos(la1) * math.sin(d) * math.cos(b))
    lo2 = lo1 + math.atan2(math.sin(b) * math.sin(d) * math.cos(la1),
                           math.cos(d) - math.sin(la1) * math.sin(la2))
    return math.degrees(la2), math.degrees(lo2)


def arc_points(start, end, centre, clockwise, step=3.0):
    b0, d0 = bearing_dist(centre, start)
    b1, d1 = bearing_dist(centre, end)
    sweep = (b1 - b0) % 360 if clockwise else -((b0 - b1) % 360)
    n = max(2, int(abs(sweep) / step))
    return [destination(centre, b0 + sweep * i / n, d0 + (d1 - d0) * i / n) for i in range(1, n)]


def circle_points(centre, radius_nm, step=6.0):
    n = int(360 / step)
    pts = [destination(centre, i * step, radius_nm) for i in range(n)]
    return pts + [pts[0]]


def to_nm(val, unit):
    v = float(val.replace(",", "."))
    return {"NM": v, "km": v * 1000 / NM_M, "m": v / NM_M}[unit]


def metres_xy(a, ref_lat):
    return a[1] * 111320 * math.cos(math.radians(ref_lat)), a[0] * 110540


def dp_simplify(pts, tol_m):
    if len(pts) < 3:
        return pts
    keep = [False] * len(pts)
    keep[0] = keep[-1] = True
    stack = [(0, len(pts) - 1)]
    ref = pts[0][0]
    xy = [metres_xy(p, ref) for p in pts]
    while stack:
        a, b = stack.pop()
        ax, ay = xy[a]
        bx, by = xy[b]
        dx, dy = bx - ax, by - ay
        ln = math.hypot(dx, dy) or 1e-9
        best, idx = -1, None
        for i in range(a + 1, b):
            d = abs(dy * (xy[i][0] - ax) - dx * (xy[i][1] - ay)) / ln
            if d > best:
                best, idx = d, i
        if best > tol_m:
            keep[idx] = True
            stack += [(a, idx), (idx, b)]
    return [p for p, k in zip(pts, keep) if k]


class Borders:
    """Linear national borders, from OSM ways shared by France and a neighbour."""

    def __init__(self, cache):
        self.g, self.cache_paths, self.max_snap = {}, {}, 0.0
        for cc, rel in COUNTRY_RELATIONS.items():
            q = f"[out:json][timeout:120];rel(2202162);way(r)->.a;rel({rel});way(r)->.b;way.a.b;out geom;"
            body = fetch("https://overpass-api.de/api/interpreter", cache / f"border-{cc}.json",
                         urllib.parse.urlencode({"data": q}).encode())
            adj = {}
            for w in json.loads(body)["elements"]:
                pts = [(round(n["lat"], 7), round(n["lon"], 7)) for n in w["geometry"]]
                for u, v in zip(pts, pts[1:]):
                    if u != v:
                        adj.setdefault(u, set()).add(v)
                        adj.setdefault(v, set()).add(u)
            if not adj:
                sys.exit(f"no border geometry for {cc}")
            self.g[cc] = adj

    def _snap(self, adj, p):
        best = (1e18, None, None, None)
        kx = math.cos(math.radians(p[0]))
        seen = set()
        for u, nbrs in adj.items():
            for v in nbrs:
                if (v, u) in seen:
                    continue
                seen.add((u, v))
                ax, ay = (u[1] - p[1]) * kx, u[0] - p[0]
                bx, by = (v[1] - p[1]) * kx, v[0] - p[0]
                dx, dy = bx - ax, by - ay
                ll = dx * dx + dy * dy or 1e-18
                t = max(0, min(1, -(ax * dx + ay * dy) / ll))
                d = (ax + t * dx) ** 2 + (ay + t * dy) ** 2
                if d < best[0]:
                    q = (round(u[0] + t * (v[0] - u[0]), 7), round(u[1] + t * (v[1] - u[1]), 7))
                    best = (d, q, u, v)
        return best[1], best[2], best[3], math.sqrt(best[0]) * 110540

    def path(self, cc, a, b):
        key = (cc, a, b)
        if key in self.cache_paths:
            return self.cache_paths[key]
        adj = self.g[cc]
        qa, ua, va, da = self._snap(adj, a)
        qb, ub, vb, db = self._snap(adj, b)
        self.max_snap = max(self.max_snap, da, db)
        if max(da, db) > 2500:
            sys.exit(f"border snap too far ({cc}) {a}->{b}: {da:.0f} m / {db:.0f} m")
        extra = {qa: {ua, va}, qb: {ub, vb}}
        if {ua, va} == {ub, vb}:
            extra[qa].add(qb)
            extra[qb].add(qa)

        def nbrs(n):
            out = set(extra.get(n, ()))
            out |= adj.get(n, set())
            for q, e in extra.items():
                if n in e:
                    out.add(q)
            return out

        dist, prev, heap = {qa: 0.0}, {}, [(0.0, qa)]
        while heap:
            d, n = heapq.heappop(heap)
            if n == qb:
                break
            if d > dist[n]:
                continue
            for m in nbrs(n):
                nd = d + bearing_dist(n, m)[1]
                if nd < dist.get(m, 1e18):
                    dist[m], prev[m] = nd, n
                    heapq.heappush(heap, (nd, m))
        if qb not in dist:
            sys.exit(f"border path not found ({cc}) {a}->{b}")
        path = [qb]
        while path[-1] != qa:
            path.append(prev[path[-1]])
        path.reverse()
        out = dp_simplify(path, BORDER_TOL_M)
        self.cache_paths[key] = out
        return out


LAT = r"(\d\d)°(\d\d)'(\d\d(?:\.\d+)?)\"([NS])"
LON = r"(\d{3})°(\d\d)'(\d\d(?:\.\d+)?)\"([EW])"
PT = LAT + r"\s*,\s*" + LON
TOKEN = re.compile(
    r"(?P<arc>arc\s+(?P<dir>horaire|anti-horaire)\s+de\s+(?P<ar>[\d.,]+)\s*(?P<au>NM|km|m)\s+de\s+rayon\s+centré\s+sur\s+)?"
    r"(?P<circle>cercle\s+de\s+(?P<cr>[\d.,]+)\s*(?P<cu>NM|km|m)\s+de\s+rayon\s+centré\s+sur\s+)?"
    + PT +
    r"|Frontière\s+(?P<border>[\w-]+)"
)


def dms(g):
    lat = int(g[0]) + int(g[1]) / 60 + float(g[2]) / 3600
    lon = int(g[4]) + int(g[5]) / 60 + float(g[6]) / 3600
    return (-lat if g[3] == "S" else lat, -lon if g[7] == "W" else lon)


class Geo:
    def __init__(self, borders):
        self.borders = borders
        self.arc_worst = (0.0, None)

    def tokens(self, text, label):
        toks, pos, residue = [], 0, []
        for m in TOKEN.finditer(text):
            residue.append(text[pos:m.start()])
            pos = m.end()
            if m["border"]:
                if m["border"] not in BORDER_WORDS:
                    sys.exit(f"{label}: unknown border '{m['border']}'")
                toks.append(("border", BORDER_WORDS[m["border"]]))
                continue
            pt = self._pt(m)
            if m["circle"]:
                toks.append(("circle", pt, to_nm(m["cr"], m["cu"])))
            elif m["arc"]:
                toks.append(("arc", pt, m["dir"] == "horaire", to_nm(m["ar"], m["au"])))
            else:
                toks.append(("pt", pt))
        residue.append(text[pos:])
        for r in residue[1:]:
            if re.sub(r"[-,\s]", "", r):
                sys.exit(f"{label}: unparsed lateral text: {r!r}")
        return toks

    @staticmethod
    def _pt(m):
        s = m.group(0)
        mm = re.search(PT, s)
        return dms(mm.groups())

    def ring(self, text, label):
        toks = self.tokens(text, label)
        if len(toks) == 1 and toks[0][0] == "circle":
            return circle_points(toks[0][1], toks[0][2])
        pts = []
        snapped = {}  # token index -> border end point, so the ring lies on the border line
        for i, t in enumerate(toks):
            if t[0] == "pt":
                pts.append(snapped.get(i, t[1]))
            elif t[0] == "arc":
                nxt = next(x for x in toks[i + 1:] + toks if x[0] == "pt")[1]
                _, d = bearing_dist(t[1], pts[-1])
                if abs(d - t[3]) / t[3] > self.arc_worst[0]:
                    self.arc_worst = (abs(d - t[3]) / t[3], f"{label}: published {t[3]:.2f} NM, start point at {d:.2f} NM")
                pts += arc_points(pts[-1], nxt, t[1], t[2])
            elif t[0] == "border":
                j, nxt = next((k, x[1]) for k, x in enumerate(toks) if k > i and x[0] == "pt")
                path = self.borders.path(t[1], pts[-1], nxt)
                pts[-1] = path[0]
                pts += path[1:-1]
                snapped[j] = path[-1]
            else:
                sys.exit(f"{label}: circle inside a boundary")
        ends_equal = toks[0][0] == "pt" and toks[-1][0] == "pt" and toks[0][1] == toks[-1][1]
        if len(toks) - 1 in snapped and ends_equal:
            pts[0] = pts[-1]  # closing vertex was moved onto the border
        elif ends_equal or bearing_dist(pts[0], pts[-1])[1] <= 0.02:
            pts[-1] = pts[0]
        else:
            print(f"  note: {label} ring was open; closed it", file=sys.stderr)
            pts.append(pts[0])
        return pts


def round_ring(r):
    out = []
    for la, lo in r:
        p = [round(la, 5), round(lo, 5)]
        if not out or out[-1] != p:
            out.append(p)
    return out


def self_intersections(ring):
    n, hits = len(ring) - 1, 0
    if n > 3000:
        return -1
    def o(a, b, c):
        return (b[1] - a[1]) * (c[0] - a[0]) - (b[0] - a[0]) * (c[1] - a[1])
    for i in range(n):
        a, b = ring[i], ring[i + 1]
        for j in range(i + 2, n):
            if i == 0 and j == n - 1:
                continue
            c, d = ring[j], ring[j + 1]
            if min(a[1], b[1]) > max(c[1], d[1]) or max(a[1], b[1]) < min(c[1], d[1]):
                continue
            if o(a, b, c) * o(a, b, d) < 0 and o(c, d, a) * o(c, d, b) < 0:
                hits += 1
    return hits


def inside(p, ring):
    x, y, c = p[1], p[0], False
    for (y1, x1), (y2, x2) in zip(ring, ring[1:]):
        if (y1 > y) != (y2 > y) and x < (x2 - x1) * (y - y1) / (y2 - y1) + x1:
            c = not c
    return c


def terrain_range(ring, name, cache):
    f = cache / f"terrain-{name}.json"
    if f.exists():
        return json.loads(f.read_text())
    la = [p[0] for p in ring]
    lo = [p[1] for p in ring]
    pts = []
    n = 16
    while len(pts) < 280:
        pts = [(la0, lo0)
               for la0 in [min(la) + (max(la) - min(la)) * (i + .5) / n for i in range(n)]
               for lo0 in [min(lo) + (max(lo) - min(lo)) * (j + .5) / n for j in range(n)]
               if inside((la0, lo0), ring)]
        n += 4
    pts = pts[:300]
    els = []
    for i in range(0, len(pts), 100):
        loc = "|".join(f"{a:.4f},{o:.4f}" for a, o in pts[i:i + 100])
        req = urllib.request.Request(f"https://api.opentopodata.org/v1/srtm90m?locations={loc}",
                                     headers={"User-Agent": UA})
        with urllib.request.urlopen(req, timeout=60) as r:
            els += [x["elevation"] for x in json.load(r)["results"] if x["elevation"] is not None]
        time.sleep(1.2)
    out = {"minFt": round(min(els) * 3.28084), "maxFt": round(max(els) * 3.28084), "samples": len(els)}
    f.write_text(json.dumps(out))
    return out


# ---------------------------------------------------------------- limits

def parse_limit(s, label):
    s = squash(s)
    m = re.fullmatch(r"FL (\d+)", s)
    if m:
        return {"t": "FL", "v": int(m[1])}
    m = re.fullmatch(r"(\d+)\s*ft (AMSL|ASFC)", s)
    if m:
        return {"t": m[2], "v": int(m[1])}
    if s == "SFC":
        return {"t": "SFC", "v": 0}
    sys.exit(f"{label}: unknown vertical limit {s!r}")


def parse_vertical(cell, label):
    lines = [l.strip() for l in cell.split("\n") if l.strip()]
    idx = next(i for i, l in enumerate(lines) if re.fullmatch(r"-{4,}", l))
    up = [parse_limit(l, label) for l in lines[:idx]]
    lo = [parse_limit(l, label) for l in lines[idx + 1:]]
    return up, lo


# ---------------------------------------------------------------- remarks

def classify(rem, app, label):
    """Turn one AIP remark into structured rules. Unknown wording aborts the build."""
    out = {"rwy": None, "excl": [], "mil": False, "info": []}
    text = squash(rem)

    def ex(kind, ident, cond=None):
        out["excl"].append({"kind": kind, "id": ident, "cond": cond})

    def rm(pat, fn=None):
        nonlocal text
        def repl(m):
            if fn:
                fn(m)
            return " "
        text = re.sub(pat, repl, text)

    rm(r"RWY (\d+) en service / in use\.", lambda m: out.__setitem__("rwy", m[1]))
    rm(r"Défini à l'exclusion des secteurs (\w+) quand (\w+) APP est actif\.",
       lambda m: ex("sector", m[1], "app-" + m[2].lower()))
    rm(r"Defined excluding \w+ sectors when \w+ APP active\.")
    rm(r"A l'exclusion du secteur (\w+) \(TMA \d+ de SFC à FL\d+\)\.", lambda m: ex("sector", m[1]))
    rm(r"Excluding \w+ sector \(TMA \d+ from SFC to FL\d+\)\.")
    rm(r"A l'exclusion de la TMA PARIS de classe A\.", lambda m: ex("group", "tma-paris-a"))
    rm(r"Excluding class A PARIS TMA\.")

    def mil_sector(m):
        ex("sector", m[1])
        out["mil"] = True

    rm(r"Défini à l'exclusion des portions interférentes du secteur (\w+) et à l'exclusion des espaces aériens MIL quand ils sont actifs\.", mil_sector)
    rm(r"Defined except for overlapping portions of the \w+ sector and military airspaces when they are active\.")
    rm(r"Défini à l'exclusion des espaces aériens MIL quand ils sont actifs\.", lambda m: out.__setitem__("mil", True))
    rm(r"Defined except for military airspaces when they are active\.")

    def rhone(m):
        for n in re.findall(r"\d+", m[1]):
            ex("ref", f"cta-rhone-{n}", f"cta-rhone-{n}")

    rm(r"A l'exclusion (?:de la|des) CTA RHONE ([\d, et]+?) lorsqu'elles? (?:est|sont) actives?\.", rhone)
    rm(r"/?\s*Except for RHONE CTA [\d, and]+ when active\.")
    rm(r"Défini à l'exclusion des espaces de JERSEY ILES ANGLO NORMANDES lorsqu'ils sont actifs\.",
       lambda m: ex("group", "channel-islands", "channel-islands"))
    rm(r"Defined excluding JERSEY ILES ANGLO NORMANDES airspaces when active\.")
    rm(r"A l'exclusion de la CTR (LFR[KG]) lorsqu'elle est active\.",
       lambda m: ex("ref", "ctr-" + m[1].lower(), "ctr-" + m[1].lower()))
    rm(r"Excluding LFR[KG] CTR when active\.")

    def lfp(m):
        for n in re.findall(r"LF-P ([\d.]+)", m[1]):
            ex("ref", f"lf-p-{n}")

    rm(r"A l'exclusion (?:de la zone|des zones) (LF-P [\d.]+(?:, LF-P [\d.]+)*(?: et LF-P [\d.]+)?) interférentes?\.", lfp)
    rm(r"Excluding LF-P [\d.]+(?:, LF-P [\d.]+)*(?: and LF-P [\d.]+)? interfering parts?\.")

    rm(r"\bH24\b", lambda m: out["info"].append("H24"))
    rm(r"SIV [\d.]+ : plafond[./]ceiling FL \d+\.", lambda m: out["info"].append(squash(m[0]).replace("plafond.ceiling", "plafond/ceiling")))
    rm(r"SIV [\d/]+\.", lambda m: out["info"].append(m[0]))
    rm(r"TMA SEINE [\d./]+\.", lambda m: out["info"].append(m[0]))
    rm(r"TMA BIARRITZ partie [\d., et]+\d", lambda m: out["info"].append(m[0]))
    rm(r"TMA PYRENEES parties/parts 1 à/to 8\.", lambda m: out["info"].append(m[0]))

    if text.strip():
        sys.exit(f"{label}: unclassified remark text: {text.strip()!r}")
    return out


# ---------------------------------------------------------------- reference airspaces

COORD_START = re.compile(r"\d\d°\d\d'|cercle de|arc ")


def split_name(cell):
    m = COORD_START.search(cell)
    return (squash(cell[:m.start()]), cell[m.start():]) if m else (squash(cell), "")


def named_rows(rows, vcol, wanted):
    """Yield (name, lateral, cells) for rows of 'name then geometry' AIP tables."""
    current = None
    for r in rows:
        if len(r) <= vcol:
            continue
        name, lateral = split_name(r[0])
        if not lateral:
            if name and not any(c.strip() for c in r[1:]):
                current = name
            continue
        name = name or current
        if name and wanted.search(name) and re.search(r"-{4,}", r[vcol]):
            yield name, lateral, r
        if name == current:
            current = None


def build_refs(geo, cache, base, enr22):
    refs, groups = {}, {}

    def add(ident, group, name, lateral, vert, note=""):
        up, lo = parse_vertical(vert, ident)
        ring = round_ring(geo.ring(squash(lateral), ident))
        refs[ident] = {"name": name, "group": group, "upper": up, "lower": lo, "rings": [ring], "note": squash(note)}
        groups.setdefault(group, []).append(ident)

    enr21 = fetch(f"{base}/FR-ENR-2.1-fr-FR.html", cache / "FR-ENR-2.1-fr-FR.html").decode("utf-8")
    for name, lat, r in named_rows(rows_of(enr21), 2, re.compile(r"^(CTA RHONE partie [234]$|TMA PARIS partie|CTA ILES ANGLO-NORMANDES|TMA ILES ANGLO NORMANDES)")):
        # 5-column ENR 2.1 layout: lateral, class, vertical, service, remarks
        cls, vert, note = r[1].strip(), r[2], r[4]
        if name.startswith("CTA RHONE"):
            n = name.split()[-1]
            add(f"cta-rhone-{n}", f"cta-rhone-{n}", f"CTA Rhône part {n}", lat, vert, note)
        elif name.startswith("TMA PARIS"):
            if cls == "A":
                n = name.split()[-1]
                add(f"tma-paris-a-{n}", "tma-paris-a", f"TMA Paris part {n} (class A)", lat, vert, note)
        else:
            add("channel-" + re.sub(r"[^a-z0-9]+", "-", name.lower()).strip("-"), "channel-islands", name, lat, vert, note)

    for ad, label in (("LFRK", "CAEN"), ("LFRG", "DEAUVILLE")):
        page = fetch(f"{base}/FR-AD-2.{ad}-fr-FR.html", cache / f"AD-{ad}.html").decode("utf-8")
        found = [x for x in named_rows(rows_of(page), 2, re.compile(rf"^CTR {label}$"))]
        if len(found) != 1:
            sys.exit(f"CTR {label}: expected one row, got {len(found)}")
        name, lat, r = found[0]
        add(f"ctr-{ad.lower()}", f"ctr-{ad.lower()}", f"{name} ({ad})", lat, r[2], r[4])

    enr51 = fetch(f"{base}/FR-ENR-5.1-fr-FR.html", cache / "FR-ENR-5.1-fr-FR.html").decode("utf-8")
    p51 = rows_of(enr51)
    wanted = {"6.1", "6.2", "7", "81", "27", "28", "32"}
    for i, r in enumerate(p51):
        m = re.match(r"\s*LF\s+P\s+([\d]+)(?:\s*-\s*(\d+))?\s*$", r[0])
        if not m:
            continue
        n = m[1] + ("." + m[2] if m[2] else "")
        if n in wanted:
            g = p51[i + 1]
            # rowspan shifts columns: the name row can be followed by the geometry row directly
            add(f"lf-p-{n}", "lf-p", f"LF-P {n} {squash(r[1]).title()}", g[0], g[1], g[-1])
            wanted.discard(n)
    if wanted:
        sys.exit(f"LF-P zones not found: {sorted(wanted)}")

    a = enr22.rfind("ENR 2.2.7", 0, enr22.find("ENR 2.2.8"))
    siv_rows = rows_of(enr22[a:])
    for name, lat, r in named_rows(siv_rows, 1, re.compile(r"^SIV (LILLE|SEINE) partie")):
        city = name.split()[1].lower()
        n = name.split()[-1]
        svc = squash(r[2]) if len(r) > 2 else ""
        add(f"siv-{city}-{n}", f"siv-{city}", f"SIV {city.title()} part {n}", lat, r[1], svc + (" — " + r[3] if len(r) > 3 else ""))
    return refs, groups


# ---------------------------------------------------------------- main

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--airac", required=True, help="e.g. 2026-10-29")
    ap.add_argument("--folder", required=True, help="e.g. eAIP_29_OCT_2026")
    ap.add_argument("--cache", default=Path(tempfile.gettempdir()) / "french-vacc-aip-cache", type=Path)
    ap.add_argument("--out", default=Path(__file__).resolve().parent.parent / "approach-sectors-data.js", type=Path)
    a = ap.parse_args()
    a.cache = a.cache / a.airac
    a.cache.mkdir(parents=True, exist_ok=True)

    base = (f"https://www.sia.aviation-civile.gouv.fr/media/dvd/{a.folder}/FRANCE/AIRAC-{a.airac}/html/eAIP")
    enr22 = fetch(f"{base}/FR-ENR-2.2-fr-FR.html", a.cache / "FR-ENR-2.2-fr-FR.html").decode("utf-8")
    borders = Borders(a.cache)
    geo = Geo(borders)

    i0 = enr22.find("ENR 2.2.4.2")
    i1 = enr22.find("ENR 2.2.5", i0)
    if i0 < 0 or i1 < 0:
        sys.exit("ENR 2.2.4.2 section not found")
    rows = rows_of(enr22[i0:i1])

    apps, app, last, seen = [], None, None, set()
    stats = Counter()
    for r in rows:
        if len(r) == 1:
            m = re.search(r"APP\s+(.+)", squash(r[0]))
            if m:
                name = m[1].strip()
                if name not in APP_META:
                    sys.exit(f"unknown APP {name!r}: add it to APP_META")
                city, nm, cs, lat, lon, col = APP_META[name]
                app = {"id": name, "city": city, "name": nm, "callsign": cs, "lat": lat, "lon": lon,
                       "color": col, "sectors": []}
                apps.append(app)
            continue
        if len(r) != 4 or r[0].strip().startswith("IDENT"):
            continue
        if not r[0].strip() and not r[2].strip():
            # remark row: belongs to the row above
            remark = squash(r[3])
            if remark:
                c = classify(remark, app, last["code"])
                last["remark"] = remark
                last["rwy"] = c["rwy"]
                last["excl"] = c["excl"]
                last["mil"] = c["mil"]
                last["info"] = c["info"]
                stats["remarks"] += 1
            continue
        lines = [l.strip() for l in r[0].split("\n") if l.strip()]
        ident = lines[0]
        code = re.search(r"\(\s*(\w+)\s*\)", " ".join(lines))[1]
        if code in seen:
            sys.exit(f"duplicate code {code}")
        seen.add(code)
        up, lo = parse_vertical(r[2], code)
        ring = round_ring(geo.ring(squash(r[3]), code))
        n_si = self_intersections(ring)
        if n_si:
            print(f"  warn: {code} ring self-intersects x{n_si}", file=sys.stderr)
        part = {"code": code, "part": squash(r[1]), "upper": up, "lower": lo, "rings": [ring],
                "remark": "", "rwy": None, "excl": [], "mil": False, "info": []}
        sec = next((s for s in app["sectors"] if s["id"] == ident), None)
        if sec is None:
            sec = {"id": ident, "parts": []}
            app["sectors"].append(sec)
        sec["parts"].append(part)
        last = part
        stats["parts"] += 1
        stats["vertices"] += len(ring)

    refs, groups = build_refs(geo, a.cache, base, enr22)

    # every exclusion must resolve to something we actually have
    by_sector = {(ap_["id"], s["id"]) for ap_ in apps for s in ap_["sectors"]}
    for ap_ in apps:
        for s in ap_["sectors"]:
            for p in s["parts"]:
                for e in p["excl"]:
                    ok = {"sector": (ap_["id"], e["id"]) in by_sector, "group": e["id"] in groups, "ref": e["id"] in refs}[e["kind"]]
                    if not ok:
                        sys.exit(f"{p['code']}: unresolved exclusion {e}")
                    if e["cond"] and e["cond"] not in CONDITIONS:
                        sys.exit(f"{p['code']}: unknown condition {e['cond']}")
                if any(l["t"] == "ASFC" for l in p["lower"] + p["upper"]):
                    p["terrain"] = terrain_range(p["rings"][0], p["code"], a.cache)
                    stats["terrain"] += 1

    # sectors sharing identical geometry are worth knowing about
    twins = Counter()
    for ap_ in apps:
        for s in ap_["sectors"]:
            for p in s["parts"]:
                twins[json.dumps(p["rings"]) + json.dumps(p["upper"]) + json.dumps(p["lower"])] += 1

    data = {
        "airac": a.airac,
        "source": f"https://www.sia.aviation-civile.gouv.fr/media/dvd/{a.folder}/FRANCE/AIRAC-{a.airac}/html/index-fr-FR.html",
        "conditions": CONDITIONS,
        "notPublished": NOT_PUBLISHED,
        "apps": apps,
        "refs": refs,
        "groups": groups,
    }
    js = "/* Generated by tools/build_approach_sectors.py - do not edit by hand. */\nwindow.APPROACH_SECTORS = " + \
         json.dumps(data, ensure_ascii=False, separators=(",", ":")) + ";\n"
    a.out.write_text(js, encoding="utf-8")

    print(f"APPs {len(apps)}, sectors {sum(len(x['sectors']) for x in apps)}, {dict(stats)}")
    print(f"refs {len(refs)}: { {k: len(v) for k, v in groups.items()} }")
    print(f"border snap max {borders.max_snap:.0f} m over {len(borders.cache_paths)} segments")
    print(f"arc radius worst mismatch {geo.arc_worst[0] * 100:.2f}% ({geo.arc_worst[1]})")
    print(f"identical-geometry duplicates: {sum(1 for v in twins.values() if v > 1)}")
    print(f"wrote {a.out} ({len(js) / 1024:.0f} kB)")


if __name__ == "__main__":
    main()
