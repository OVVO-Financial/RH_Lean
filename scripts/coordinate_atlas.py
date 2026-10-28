#!/usr/bin/env python3
"""Coordinate atlas: one phenomenon, many repository coordinates.

The registry docs/coordinate-atlas.json lists the coordinate systems this
repository uses for the same square-root-scale prime/Mobius fluctuation, the
typed crosswalks between them (identities, offsets, projections, bound
equivalences, one-way implications, explicit barriers), notation collisions
and normalization pitfalls. This script validates it, regenerates the marked
blocks of docs/COORDINATE_ATLAS.md, and answers agent queries:

    lookup <term>   every coordinate a symbol, alias or Lean name can mean
    path <A> <B>    the shortest crosswalk chain between two coordinates
    expand <term>   alias list for grep or `proofq repo-search --expand`

A navigation path is not a proof: only the cited Lean declarations and their
hypotheses establish anything, and NOT_EQUIVALENT edges are never crossed.
"""

import argparse
import json
import re
import sys
import unicodedata
import heapq
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ATLAS = ROOT / "docs/coordinate-atlas.json"
REGISTRY = ROOT / "docs/proof-obligations.json"
SEARCH = ROOT / "docs/search"
DOC = ROOT / "docs/COORDINATE_ATLAS.md"
SCHEMA = "rhlean-coordinate-atlas/1"
ROUTE_IDS = ("VF-LOW", "SAT", "CODIV", "BLOCK", "OAI-NNS", "JOH",
             "FINITE-AC", "CORR4", "MU-LIFT", "NYMAN")
NEEDS_SOURCE = {"PAPER", "LITERATURE", "EXTERNAL", "AUDIT"}

sys.path.insert(0, str(ROOT / "scripts"))
from proof_obligation_dag import lean_declared  # noqa: E402


def load(path=ATLAS):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def fold(text):
    """Case-, accent- and spacing-insensitive form used for matching."""
    text = unicodedata.normalize("NFKC", text).replace("²", "^2").replace("−", "-")
    return re.sub(r"\s+", " ", text).strip().casefold()


def head(symbol):
    """Leading letters of a notation: 'D_R^can' -> 'D', 'C6(z)' -> 'C', 'Γ_R' -> 'Γ'."""
    match = re.match(r"[^\W\d_]+", unicodedata.normalize("NFKC", symbol))
    return match.group(0) if match else symbol


def graph(atlas):
    """Undirected navigation adjacency, excluding NOT_EQUIVALENT barriers."""
    adj = {c["id"]: [] for c in atlas["coordinates"]}
    for x in atlas["crosswalks"]:
        if x["relation"] == "NOT_EQUIVALENT":
            continue
        if x["from"] in adj and x["to"] in adj:
            adj[x["from"]].append((x["to"], x, "forward"))
            adj[x["to"]].append((x["from"], x, "reverse"))
    return adj


# Evidence-weighted navigation: prefer Lean-on-main links over literature,
# paper and external ones when several chains exist.
STEP_COST = {"LEAN_ON_MAIN": 1, "DEFINITIONAL": 1, "LITERATURE": 3, "PAPER": 4, "EXTERNAL": 6}
LEAN_ONLY = {"LEAN_ON_MAIN", "DEFINITIONAL"}


def bfs(adj, start, lean_only=False):
    """Cheapest-evidence predecessor tree (Dijkstra; ties broken by registry order)."""
    prev = {start: None}
    cost = {start: 0}
    heap = [(0, 0, start)]
    tick = 0
    while heap:
        c, _, node = heapq.heappop(heap)
        if c > cost[node]:
            continue
        for nxt, x, way in adj[node]:
            if lean_only and x["status"] not in LEAN_ONLY:
                continue
            nc = c + STEP_COST.get(x["status"], 10)
            if nc < cost.get(nxt, float("inf")):
                cost[nxt] = nc
                prev[nxt] = (node, x, way)
                tick += 1
                heapq.heappush(heap, (nc, tick, nxt))
    return prev


def validate(atlas, root=ROOT, registry=None):
    errors = []
    err = errors.append
    if atlas.get("schema") != SCHEMA:
        return [f"unsupported schema {atlas.get('schema')!r}"]
    vocab = atlas["vocabulary"]
    coords = {}
    for c in atlas["coordinates"]:
        if c["id"] in coords:
            err(f"duplicate coordinate {c['id']}")
        coords[c["id"]] = c
    xids = [x["id"] for x in atlas["crosswalks"]]
    for dup in sorted({i for i in xids if xids.count(i) > 1}):
        err(f"duplicate crosswalk {dup}")
    if errors:
        return errors
    nodes = set()
    if registry is not None:
        nodes = {n["id"] for n in registry["nodes"]}
    cache = {}
    for a in atlas["anchors"]:
        if coords.get(a, {}).get("family") != "anchor":
            err(f"anchor {a} must be a coordinate of family 'anchor'")
    for c in atlas["coordinates"]:
        i = c["id"]
        if c.get("family") not in vocab["families"]:
            err(f"{i}: invalid family {c.get('family')!r}")
        for f in ("name", "definition", "index", "measures"):
            if not c.get(f):
                err(f"{i}: missing {f}")
        if not c.get("aliases"):
            err(f"{i}: needs search aliases")
        for alias in c.get("aliases", []):
            if len(alias) < 3:
                err(f"{i}: alias {alias!r} too short to search reliably")
        for r in c.get("routes", []):
            if r not in ROUTE_IDS:
                err(f"{i}: unknown route {r}")
        for d in c.get("lean", []):
            if not lean_declared(d["file"], d["name"], cache):
                err(f"{i}: declaration {d['name']} not found in {d['file']}")
        for path in c.get("documents", []):
            if not (root / path).exists():
                err(f"{i}: missing document {path}")
        for n in c.get("proof_nodes", []):
            if registry is not None and n not in nodes:
                err(f"{i}: unknown proof-obligation node {n}")
    for x in atlas["crosswalks"]:
        i = x["id"]
        for end in (x["from"], x["to"]):
            if end not in coords:
                err(f"{i}: unknown coordinate {end}")
        if x["from"] == x["to"]:
            err(f"{i}: self-loop")
        if x["relation"] not in vocab["relations"]:
            err(f"{i}: invalid relation {x['relation']}")
        if x["status"] not in vocab["statuses"]:
            err(f"{i}: invalid status {x['status']}")
        if not x.get("formula"):
            err(f"{i}: missing formula")
        if x["status"] == "LEAN_ON_MAIN" and not x.get("lean"):
            err(f"{i}: LEAN_ON_MAIN crosswalk needs a declaration")
        for d in x.get("lean", []):
            if not lean_declared(d["file"], d["name"], cache):
                err(f"{i}: declaration {d['name']} not found in {d['file']}")
        if x["status"] in NEEDS_SOURCE and not x.get("source"):
            err(f"{i}: {x['status']} crosswalk needs a source document")
        for path in x.get("source", []):
            if not (root / path).exists():
                err(f"{i}: missing source {path}")
        if (x["relation"] == "NOT_EQUIVALENT") != (x["status"] == "AUDIT"):
            err(f"{i}: NOT_EQUIVALENT barriers (and only they) carry status AUDIT")
    if errors:
        return errors
    barriers = {frozenset((x["from"], x["to"])) for x in atlas["crosswalks"] if x["relation"] == "NOT_EQUIVALENT"}
    for x in atlas["crosswalks"]:
        if x["relation"] in vocab["invertible_relations"] and frozenset((x["from"], x["to"])) in barriers:
            err(f"{x['id']}: invertible crosswalk contradicts a NOT_EQUIVALENT barrier")
    adj = graph(atlas)
    anchors = set(atlas["anchors"])
    reach = bfs(adj, atlas["anchors"][0])
    for a in anchors - set(reach):
        err(f"anchor {a} is disconnected from {atlas['anchors'][0]}")
    for c in coords:
        if c not in reach:
            err(f"{c}: no crosswalk path to any anchor")
    # Notation collisions: a head symbol used by two coordinates must be declared.
    users = {}
    for c in atlas["coordinates"]:
        for s in c.get("symbols", []):
            users.setdefault(head(s), set()).add(c["id"])
    declared = {}
    for entry in atlas["collisions"]:
        ids = set()
        for m in entry["meanings"]:
            if "coordinate" in m:
                if m["coordinate"] not in coords:
                    err(f"collision {entry['symbol']}: unknown coordinate {m['coordinate']}")
                ids.add(m["coordinate"])
                if not m.get("as"):
                    err(f"collision {entry['symbol']}: {m['coordinate']} needs an 'as' reading")
            else:
                if not m.get("meaning") or not m.get("where"):
                    err(f"collision {entry['symbol']}: text meaning needs 'meaning' and 'where'")
                for path in m.get("where", []):
                    if not (root / path).exists():
                        err(f"collision {entry['symbol']}: missing {path}")
        if len(entry["meanings"]) < 2:
            err(f"collision {entry['symbol']}: a collision needs at least two meanings")
        declared[entry["symbol"]] = ids
    for symbol, ids in sorted(users.items()):
        if len(ids) > 1 and not ids <= declared.get(symbol, set()):
            missing = sorted(ids - declared.get(symbol, set()))
            err(f"undeclared notation collision {symbol!r}: {missing} also use it")
    for conv in atlas["conventions"]:
        for f in ("id", "title", "statement", "pitfall"):
            if not conv.get(f):
                err(f"convention {conv.get('id')}: missing {f}")
        for c in conv.get("coordinates", []):
            if c not in coords:
                err(f"convention {conv['id']}: unknown coordinate {c}")
        for path in conv.get("sources", []):
            if not (root / path).exists():
                err(f"convention {conv['id']}: missing source {path}")
    if set(atlas.get("route_terms", {})) != set(ROUTE_IDS):
        err("route_terms must cover exactly the ten route IDs")
    return errors


def check_entry_points(root=ROOT):
    """llms.txt is outside the Markdown link audit; its relative links must resolve."""
    path = root / "llms.txt"
    if not path.is_file():
        return ["llms.txt is missing"]
    return [f"llms.txt: missing relative target {t}"
            for t in re.findall(r"\]\(([^)\s]+)\)", path.read_text(encoding="utf-8"))
            if "://" not in t and not (root / t.split("#")[0]).exists()]


# ------------------------------------------------------------------ queries
def lookup(atlas, term):
    """Coordinates, collisions and conventions a term can refer to."""
    q = fold(term)
    hits = []
    for c in atlas["coordinates"]:
        why = []
        if q in (fold(c["id"]), fold(c["name"])):
            why.append("id/name")
        if any(q == fold(s) for s in c.get("symbols", [])):
            why.append("symbol")
        if any(q == fold(a) or (len(q) >= 4 and q in fold(a)) for a in c.get("aliases", [])):
            why.append("alias")
        if any(q == fold(d["name"]) for d in c.get("lean", [])):
            why.append("lean")
        if not why and len(q) >= 4 and (q in fold(c["name"]) or q in fold(c["definition"])):
            why.append("text")
        if why:
            hits.append((c, why))
    symbol = head(term)
    collisions = [e for e in atlas["collisions"] if e["symbol"] == symbol and
                  (fold(term) == fold(symbol) or any(fold(term) == fold(s) for c, _ in hits for s in c.get("symbols", [])))]
    conventions = [v for v in atlas["conventions"]
                   if any(c["id"] in v.get("coordinates", []) for c, _ in hits) or q in fold(v["title"] + " " + v["statement"])]
    return hits, collisions, conventions


def resolve(atlas, term):
    hits, _, _ = lookup(atlas, term)
    exact = [c for c, why in hits if fold(term) in (fold(c["id"]), fold(c["name"]))]
    if exact:
        return exact[0]["id"]
    if len(hits) == 1:
        return hits[0][0]["id"]
    choices = ", ".join(c["id"] for c, _ in hits) or "none"
    raise SystemExit(f"{term!r} is ambiguous or unknown; candidates: {choices}")


def path(atlas, a, b, lean_only=False):
    adj = graph(atlas)
    prev = bfs(adj, a, lean_only)
    if b not in prev:
        return None
    steps, node = [], b
    while prev[node] is not None:
        parent, x, way = prev[node]
        steps.append({"from": parent, "to": node, "direction": way, "crosswalk": x["id"],
                      "relation": x["relation"], "formula": x["formula"], "status": x["status"],
                      "invertible": x["relation"] in atlas["vocabulary"]["invertible_relations"],
                      "caveat": x.get("caveat", "")})
        node = parent
    return list(reversed(steps))


def expand(atlas, term):
    hits, collisions, _ = lookup(atlas, term)
    terms = []
    for c, _ in hits:
        for t in c.get("aliases", []) + [d["name"] for d in c.get("lean", [])]:
            if t not in terms:
                terms.append(t)
    return terms, [c["id"] for c, _ in hits], collisions


def load_rewrites(directory=SEARCH):
    """Proved-rewrite families from the committed shards written by search_catalog.py."""
    families = {}
    for shard in sorted(Path(directory).glob("rewrite-families-*.jsonl")):
        for line in shard.read_text(encoding="utf-8").splitlines():
            if line.strip():
                rec = json.loads(line)
                families[rec["definition"]] = rec
    return families


# ------------------------------------------------------------------ render
def cell(text):
    return str(text).replace("|", "\\|").replace("\n", " ")


def lean_links(entries, prefix="../"):
    return "<br/>".join(f"[`{d['name']}`]({prefix}{d['file']})" for d in entries)


def render(atlas):
    coords = {c["id"]: c for c in atlas["coordinates"]}
    out = {}
    lines = ["| Family | Coordinate | Notation | Definition | Index | Lean | Routes | DAG nodes |", "|" + " --- |" * 8]
    for fam in atlas["vocabulary"]["families"]:
        for c in atlas["coordinates"]:
            if c["family"] != fam:
                continue
            lines.append(f"| {fam} | `{c['id']}`<br/>{cell(c['name'])} | {cell(', '.join(c.get('symbols', []))) or '—'} | "
                         f"{cell(c['definition'])} | {cell(c['index'])} | {lean_links(c.get('lean', [])) or '—'} | "
                         f"{', '.join(c.get('routes', [])) or '—'} | {', '.join(f'`{n}`' for n in c.get('proof_nodes', [])) or '—'} |")
    out["coordinates"] = "\n".join(lines)

    lines = ["| From | Relation | To | Formula | Status | Evidence | Caveat |", "|" + " --- |" * 7]
    for x in atlas["crosswalks"]:
        ev = lean_links(x.get("lean", [])) or "<br/>".join(f"[{Path(p).name}](../{p})" for p in x.get("source", []))
        lines.append(f"| `{x['from']}` | {x['relation']} | `{x['to']}` | {cell(x['formula'])} | {x['status']} | {ev} | "
                     f"{cell(x.get('caveat', ''))} |")
    out["crosswalks"] = "\n".join(lines)

    adj = graph(atlas)
    lines = ["| Coordinate | Strongest-evidence chain to π − Li₂ | Strongest-evidence chain to M |", "| --- | --- | --- |"]
    for c in atlas["coordinates"]:
        cols = []
        for anchor in ("ANCHOR-PRIME-DISCREPANCY", "ANCHOR-MERTENS"):
            steps = path(atlas, c["id"], anchor) if c["id"] != anchor else []
            if steps is None:
                cols.append("unreachable")
            elif not steps:
                cols.append("(anchor)")
            else:
                chain = " → ".join(f"{s['relation']}{'' if s['direction'] == 'forward' else '⁻¹'} [{s['status']}] `{s['to']}`" for s in steps)
                flag = "" if all(s["invertible"] for s in steps) else " *(navigation only)*"
                cols.append(chain + flag)
        lines.append(f"| `{c['id']}` | {cols[0]} | {cols[1]} |")
    out["anchor-paths"] = "\n".join(lines)

    order = {c["id"]: k for k, c in enumerate(atlas["coordinates"])}
    rows = ["```mermaid", "flowchart LR"]
    for c in atlas["coordinates"]:
        shape = ('(["', '"])') if c["family"] == "anchor" else ('["', '"]')
        rows.append(f"  k{order[c['id']]}{shape[0]}{c['id']}{shape[1]}")
    for x in atlas["crosswalks"]:
        a, b = f"k{order[x['from']]}", f"k{order[x['to']]}"
        if x["relation"] == "NOT_EQUIVALENT":
            rows.append(f"  {a} --x|NOT_EQUIVALENT| {b}")
        elif x["relation"] in atlas["vocabulary"]["invertible_relations"]:
            rows.append(f"  {a} <-->|{x['relation']}| {b}")
        elif x["status"] == "LEAN_ON_MAIN":
            rows.append(f"  {a} -->|{x['relation']}| {b}")
        else:
            rows.append(f"  {a} -.->|{x['relation']}| {b}")
    out["mermaid"] = "\n".join(rows + ["```"])

    lines = ["| Symbol | Meanings in this repository |", "| --- | --- |"]
    for e in atlas["collisions"]:
        parts = []
        for m in e["meanings"]:
            if "coordinate" in m:
                parts.append(f"`{m['coordinate']}`: {cell(m['as'])}")
            else:
                parts.append(f"{cell(m['meaning'])} ({', '.join(f'[{Path(p).name}](../{p})' for p in m['where'])})")
        lines.append(f"| **{e['symbol']}** | " + "<br/>".join(parts) + " |")
    out["collisions"] = "\n".join(lines)

    lines = ["| Convention | Statement | Pitfall | Coordinates |", "| --- | --- | --- | --- |"]
    for v in atlas["conventions"]:
        lines.append(f"| `{v['id']}` {cell(v['title'])} | {cell(v['statement'])} | {cell(v['pitfall'])} | "
                     f"{', '.join(f'`{c}`' for c in v.get('coordinates', []))} |")
    out["conventions"] = "\n".join(lines)

    families = load_rewrites()
    lines = ["| Coordinate | Lean definition | Proved rewrites (`<def>_eq_…` / `<def>_iff_…`) |", "| --- | --- | --- |"]
    for c in atlas["coordinates"]:
        for d in c.get("lean", []):
            rec = families.get(d["name"])
            if not rec:
                continue
            count = sum(len(v) for v in rec["rewrites"].values())
            names = [n for v in rec["rewrites"].values() for n in v][:6]
            more = f" … (+{count - len(names)})" if count > len(names) else ""
            lines.append(f"| `{c['id']}` | [`{d['name']}`](../{d['file']}) | {count}: "
                         + ", ".join(f"`{n}`" for n in names) + more + " |")
    out["rewrites"] = "\n".join(lines)
    return out


def splice(text, name, body):
    begin, end = f"<!-- BEGIN GENERATED: {name} -->", f"<!-- END GENERATED: {name} -->"
    pattern = re.compile(re.escape(begin) + r".*?" + re.escape(end), re.S)
    if not pattern.search(text):
        raise ValueError(f"missing generated block {name}")
    return pattern.sub(lambda _: f"{begin}\n{body}\n{end}", text)


def sync(atlas, write, doc=DOC):
    text = doc.read_text(encoding="utf-8")
    new = text
    for name, body in render(atlas).items():
        new = splice(new, name, body)
    if new != text and write:
        doc.write_text(new, encoding="utf-8")
    return new != text


# ------------------------------------------------------------------ CLI
def print_lookup(atlas, term, as_json):
    hits, collisions, conventions = lookup(atlas, term)
    families = load_rewrites()
    if as_json:
        print(json.dumps({"term": term, "coordinates": [dict(c, matched_by=why) for c, why in hits],
                          "collisions": collisions, "conventions": conventions}, indent=2, ensure_ascii=False))
        return
    if not hits and not collisions:
        print(f"No atlas coordinate matches {term!r}. Try `python3 scripts/proofq.py repo-search {term!r}`.")
        return
    for e in collisions:
        print(f"NOTATION COLLISION '{e['symbol']}': {len(e['meanings'])} meanings")
        for m in e["meanings"]:
            print(f"  - {m.get('coordinate', '(text)')}: {m.get('as') or m.get('meaning')}")
    for c, why in hits:
        print(f"\n{c['id']} — {c['name']}  [{c['family']}; matched by {', '.join(why)}]")
        print(f"  definition: {c['definition']}")
        print(f"  index:      {c['index']}")
        print(f"  measures:   {c['measures']}")
        for d in c.get("lean", []):
            rec = families.get(d["name"])
            extra = f"  ({sum(len(v) for v in rec['rewrites'].values())} proved rewrites)" if rec else ""
            print(f"  lean:       {d['name']}  {d['file']}{extra}")
        for p in c.get("documents", []):
            print(f"  document:   {p}")
        if c.get("proof_nodes"):
            print(f"  DAG nodes:  {', '.join(c['proof_nodes'])}")
        for x in atlas["crosswalks"]:
            if c["id"] in (x["from"], x["to"]):
                other = x["to"] if x["from"] == c["id"] else x["from"]
                print(f"  crosswalk:  {x['relation']} {other}: {x['formula']} [{x['status']}]")
    for v in conventions:
        print(f"\nCONVENTION {v['id']}: {v['statement']}\n  pitfall: {v['pitfall']}")


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = parser.add_subparsers(dest="cmd", required=True)
    sub.add_parser("check", help="validate and fail if generated blocks are stale")
    sub.add_parser("write", help="validate and rewrite generated blocks")
    p = sub.add_parser("lookup", help="what a symbol, alias or Lean name can mean")
    p.add_argument("term")
    p.add_argument("--json", action="store_true")
    p = sub.add_parser("path", help="strongest-evidence crosswalk chain between two coordinates")
    p.add_argument("a")
    p.add_argument("b")
    p.add_argument("--lean-only", action="store_true", help="use only Lean-on-main and definitional crosswalks")
    p.add_argument("--json", action="store_true")
    p = sub.add_parser("expand", help="aliases and Lean names for a term")
    p.add_argument("term")
    p.add_argument("--grep", action="store_true", help="print one extended regex for git grep -E")
    args = parser.parse_args()
    atlas = load()
    if args.cmd in ("check", "write"):
        registry = json.loads(REGISTRY.read_text(encoding="utf-8"))
        errors = validate(atlas, registry=registry) + check_entry_points()
        if errors:
            raise SystemExit("coordinate atlas invalid:\n  " + "\n  ".join(errors))
        stale = sync(atlas, write=args.cmd == "write")
        if stale and args.cmd == "check":
            raise SystemExit("docs/COORDINATE_ATLAS.md is stale; run python3 scripts/coordinate_atlas.py write")
        print(f"PASS: {len(atlas['coordinates'])} coordinates, {len(atlas['crosswalks'])} crosswalks, "
              f"{len(atlas['collisions'])} notation collisions; every coordinate reaches an anchor")
    elif args.cmd == "lookup":
        print_lookup(atlas, args.term, args.json)
    elif args.cmd == "path":
        a, b = resolve(atlas, args.a), resolve(atlas, args.b)
        steps = path(atlas, a, b, args.lean_only)
        if args.json:
            print(json.dumps({"from": a, "to": b, "steps": steps}, indent=2, ensure_ascii=False))
        elif steps is None:
            print(f"No {'Lean-only ' if args.lean_only else ''}crosswalk path from {a} to {b}.")
        else:
            print(f"{a} → {b}: {len(steps)} step(s)")
            for s in steps:
                arrow = "→" if s["direction"] == "forward" else "← (reverse)"
                print(f"  {s['from']} {arrow} {s['to']}: {s['relation']} [{s['status']}] {s['formula']}")
                if s["caveat"]:
                    print(f"      caveat: {s['caveat']}")
            if not all(s["invertible"] for s in steps):
                print("  NOTE: navigation only — at least one step is not an equivalence; do not transfer bounds backwards.")
    elif args.cmd == "expand":
        terms, ids, collisions = expand(atlas, args.term)
        if collisions:
            print(f"# '{args.term}' collides: {', '.join(m.get('coordinate', m.get('meaning', '')) for e in collisions for m in e['meanings'])}",
                  file=sys.stderr)
        if args.grep:
            print("|".join(re.escape(t) for t in terms))
        else:
            print(f"# {', '.join(ids) or 'no coordinate'}", file=sys.stderr)
            print("\n".join(terms))


if __name__ == "__main__":
    main()
