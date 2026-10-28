#!/usr/bin/env python3
"""Committed, static search corpus for agents that can read files but not run code.

Writes docs/search/:
  catalog-<shard>.jsonl  one record per tracked source file: title, date, PRs,
      coordinate-atlas tags, routes, proof-obligation nodes, Lean declaration
      counts/headlines, status words present
  rewrite-families-<range>.jsonl  every Lean definition with its proved
      alternative representations (theorems `<def>_eq_...` / `<def>_iff_...`)
  coordinates/<ID>.md, routes/<ROUTE>.md, INDEX.md  small per-topic pages
  MANIFEST.json  schema, counts and the input fingerprint

Every generated file stays far below GitHub code search's 384 KB per-file
limit and is small enough for an agent to fetch one topic at a time.

Tags come from docs/coordinate-atlas.json aliases and Lean names, route terms
and literal proof-obligation IDs. They are search hints, never mathematical
claims. `--check` reports staleness (and fails only with --strict); `--write`
regenerates. Runs with the standard library in a few seconds.
"""

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "docs/search"
SCHEMA = "rhlean-search-catalog/1"
SOURCE_EXT = {".md", ".lean", ".py", ".cpp", ".c", ".tex"}
SHARDS = (
    ("research-lean-vf", lambda p: p.startswith("research/VF") and p.endswith(".lean")),
    ("research-lean", lambda p: p.startswith("research/") and p.endswith(".lean")),
    ("research-notes", lambda p: p.startswith("research/")),
    ("library-proof", lambda p: p.startswith("RHLean/Proof/")),
    ("library-core", lambda p: p.startswith("RHLean/")),
    ("docs", lambda p: p.endswith((".md", ".tex")) and not p.startswith(("scripts/", "experiments/", "numerics/"))),
    ("code", lambda p: p.startswith(("scripts/", "experiments/", "numerics/"))),
)
# Fixed initial-letter ranges keep every rewrite shard small as the library grows.
REWRITE_SHARDS = (("a-k", "abcdefghijk"), ("l", "l"), ("m-r", "mnopqr"), ("s", "s"), ("t-z", "tuvwxyz"))
TOPIC_DIRS = ("coordinates", "routes")
STATUS_WORDS = ("PROVED_IN_LEAN_ON_MAIN", "PROVED_IN_LEAN_PR_GREEN_UNMERGED", "INDEPENDENTLY_REVIEWED_PAPER_PROOF",
                "PAPER_PROOF_NEEDS_REVIEW", "PAPER_PROOF", "FINITE_COMPUTATION", "CONDITIONAL", "TARGET_EQUIVALENT",
                "REFUTED", "IDENTITY_ONLY", "NO_NEW_THEOREM_TO_FORMALIZE", "HISTORICAL", "SUPERSEDED")
DECL = re.compile(r"(?m)^[ \t]*(?:@\[[^\]\n]*\][ \t]*)?(?:(?:private|protected|noncomputable|nonrec|partial)[ \t]+)*"
                  r"(theorem|lemma|def|abbrev|structure|instance|inductive)[ \t]+([^\s(:{\[]+)")


def tracked(root=ROOT):
    out = subprocess.check_output(["git", "ls-files", "-z", "--cached", "--others", "--exclude-standard"],
                                  cwd=root).decode().split("\0")
    paths = [p for p in out if p and Path(p).suffix in SOURCE_EXT and not p.startswith("docs/search/")]
    return sorted(p for p in set(paths) if (root / p).is_file() and any(rule(p) for _, rule in SHARDS))


COMMENT_TOKEN = re.compile(r"/-|-/|--|\n")


def strip_lean_comments(text):
    """Drop nested /- -/ blocks (incl. docstrings) and -- line comments, keeping line breaks.

    As in Lean, `--` starts a line comment only outside block comments, so a
    docstring containing `Mobius--rough` still closes at its `-/`.
    """
    out, depth, pos, scan = [], 0, 0, 0
    while True:
        m = COMMENT_TOKEN.search(text, scan)
        if m is None:
            break
        tok, scan = m.group(0), m.end()
        if depth == 0:
            out.append(text[pos:m.start()])
        if tok == "/-":
            depth += 1
        elif tok == "-/" and depth:
            depth -= 1
        elif tok == "--" and depth == 0:
            end = text.find("\n", scan)
            scan = len(text) if end < 0 else end
        elif tok == "\n":
            out.append("\n")
        pos = scan
    if depth == 0:
        out.append(text[pos:])
    return "".join(out)


def title_of(path, text):
    if path.endswith((".md", ".tex")):
        for line in text.splitlines():
            m = re.match(r"\s*(?:#+\s+|\\(?:title|section)\{)(.+?)\}?\s*$", line)
            if m:
                return m.group(1).strip()[:160]
    if path.endswith(".lean"):
        m = re.search(r"/-!\s*(.*?)-/", text, re.S)
        block = m.group(1) if m else ""
        if not block:
            m = re.search(r"/--\s*(.*?)-/", text, re.S)
            block = m.group(1) if m else ""
        for line in block.splitlines():
            line = line.strip().lstrip("#").strip()
            if line:
                return line[:160]
    if path.endswith(".py"):
        m = re.search(r'^(?:#![^\n]*\n)?(?:#[^\n]*\n)*\s*[rRbB]?("""|\'\'\')\s*(.*?)\s*(?:\n|\1)', text, re.S)
        if m:
            return m.group(2).strip()[:160]
    if path.endswith((".cpp", ".c")):
        m = re.search(r"(?://\s*(.+)|/\*+\s*(.+?)\s*(?:\*/|\n))", text)
        if m:
            return (m.group(1) or m.group(2)).strip()[:160]
    return ""


def date_of(path, text):
    m = re.search(r"(20\d\d)[-_]?(0\d|1[0-2])[-_]?([0-3]\d)", path)
    if not m and path.endswith(".md"):
        m = re.search(r"(20\d\d)-(0\d|1[0-2])-([0-3]\d)", text[:600])
    return "-".join(m.groups()) if m else None


def fold(text):
    return text.casefold()


def word(term):
    return re.compile(r"(?<![A-Za-z0-9_])" + re.escape(term) + r"(?![A-Za-z0-9_])")


IDENTIFIER = re.compile(r"^[A-Za-z][A-Za-z0-9_']*$")


def alternation(terms, flags=0):
    body = "|".join(re.escape(t) for t in sorted(terms, key=len, reverse=True))
    return re.compile(r"(?<![A-Za-z0-9_])(" + body + r")(?![A-Za-z0-9_])", flags)


class Tagger:
    """One combined regex per vocabulary; tags are lexical hints only."""

    def __init__(self, atlas, registry):
        # Lean names (weight 3) and identifier-like aliases (weight 1) match whole
        # tokens, case-sensitively, so `vfMid` does not fire inside `vfMidFoo`.
        # Phrase aliases match case-insensitively from a word start.
        self.lean_owner, self.token_owner, self.alias_owner, self.coord_routes = {}, {}, {}, {}
        for c in atlas["coordinates"]:
            self.coord_routes[c["id"]] = c.get("routes", [])
            for d in c.get("lean", []):
                self.lean_owner.setdefault(d["name"], set()).add(c["id"])
            for a in c.get("aliases", []):
                if IDENTIFIER.match(a):
                    self.token_owner.setdefault(a, set()).add(c["id"])
                else:
                    self.alias_owner.setdefault(fold(a), set()).add(c["id"])
        self.lean_re = alternation(self.lean_owner)
        self.token_re = alternation(self.token_owner)
        body = "|".join(re.escape(t) for t in sorted(self.alias_owner, key=len, reverse=True))
        self.alias_re = re.compile(r"(?<![a-z0-9_])(?:" + body + ")")
        self.route_owner = {t: r for r, terms in atlas["route_terms"].items() for t in terms}
        self.route_re = alternation(self.route_owner)
        # "RH" alone matches nearly every file; tag only specific registry IDs.
        self.node_re = alternation(n["id"] for n in registry["nodes"] if n["id"] != "RH")

    def coordinates(self, text):
        lean_hits, alias_hits = Counter(), Counter()
        for name in self.lean_re.findall(text):
            for cid in self.lean_owner[name]:
                lean_hits[cid] += 1
        for token in self.token_re.findall(text):
            for cid in self.token_owner[token]:
                alias_hits[cid] += 1
        for alias in self.alias_re.findall(fold(text)):
            for cid in self.alias_owner[alias]:
                alias_hits[cid] += 1
        scores = {}
        for cid in set(lean_hits) | set(alias_hits):
            hits = 3 * lean_hits[cid] + alias_hits[cid]
            if lean_hits[cid] or hits >= 2:
                scores[cid] = hits
        return scores

    def route_scores(self, text, coord_scores):
        scores = Counter(self.route_owner[t] for t in self.route_re.findall(text))
        for cid in sorted(coord_scores, key=lambda c: (-coord_scores[c], c))[:3]:
            for r in self.coord_routes[cid]:
                scores[r] += 1
        return dict(scores)

    def proof_nodes(self, text):
        return Counter(self.node_re.findall(text))


def ranked(scores, limit):
    return [k for k, _ in sorted(scores.items(), key=lambda kv: (-kv[1], kv[0]))[:limit]]


def record(path, text, tagger, stripped=None):
    coord_scores = tagger.coordinates(text)
    route_scores = tagger.route_scores(text, coord_scores)
    prs = Counter(int(n) for n in re.findall(r"(?:#|/pull/)(\d{3,4})\b", text) if 100 <= int(n) <= 5000)
    rec = {
        "path": path,
        "kind": Path(path).suffix.lstrip("."),
        "title": title_of(path, text),
        "date": date_of(path, text),
        "prs": [n for n, _ in sorted(prs.items(), key=lambda kv: (-kv[1], kv[0]))[:8]],
        "coordinates": ranked(coord_scores, 8),
        "routes": ranked(route_scores, 5),
        "proof_nodes": ranked(tagger.proof_nodes(text), 10),
    }
    if path.endswith(".lean"):
        decls = DECL.findall(stripped if stripped is not None else strip_lean_comments(text))
        kinds = Counter(k for k, _ in decls)
        rec["lean"] = {"theorems": kinds["theorem"] + kinds["lemma"],
                       "definitions": kinds["def"] + kinds["abbrev"] + kinds["structure"] + kinds["inductive"],
                       "headline_definitions": [n.split(".")[-1] for k, n in decls
                                                if k in ("def", "abbrev", "structure")][:6]}
    if path.endswith((".md", ".tex")):
        rec["status_words"] = [w for w in STATUS_WORDS if word(w).search(text)]
    return rec, coord_scores, route_scores


def rewrite_families(stripped):
    """Definition -> files defining it, and theorems `<def>_eq_...`/`<def>_iff_...` grouped by file."""
    defined, theorems = {}, []
    for path, text in stripped.items():
        for kind, name in DECL.findall(text):
            short = name.split(".")[-1]
            if kind in ("def", "abbrev", "structure"):
                defined.setdefault(short, set()).add(path)
            elif kind in ("theorem", "lemma"):
                theorems.append((short, path))
    families = {}
    for short, path in theorems:
        # `<def>_eq_...`, `<def>_iff_...`, optionally after one short lowercase
        # qualifier such as `_zero_`, `_succ_` or `_sq_`; `<def>_otherQuantity_eq_...`
        # is about a different object and is excluded.
        m = re.match(r"([A-Za-z][A-Za-z0-9']*)(?:_[a-z0-9']{1,8})?_(?:eq|iff)(?:_|$)", short)
        if m and m.group(1) in defined:
            fam = families.setdefault(m.group(1), {})
            fam.setdefault(path, set()).add(short)
    return [{"definition": d, "defined_in": sorted(defined[d]),
             "rewrites": {p: sorted(ns) for p, ns in sorted(families[d].items())}}
            for d in sorted(families)]


def table(rows, depth):
    up = "../" * depth
    lines = ["| Score | File | Title |", "| --- | --- | --- |"]
    lines += [f"| {score} | [{p}]({up}{p}) | {title.replace('|', '/') or '—'} |" for score, p, title in rows]
    return lines


def coordinate_page(c, atlas, scores_by_path, titles, fam):
    up = "../../../"
    lines = [f"# {c['id']} — {c['name']}", "",
             f"*Generated by `python3 scripts/search_catalog.py --write`; edit [coordinate-atlas.json](../../coordinate-atlas.json) "
             f"instead. Tags are lexical search hints, not mathematical claims.*", "",
             f"- **Family:** {c['family']}",
             f"- **Notation:** {', '.join(c.get('symbols', [])) or '—'}",
             f"- **Definition:** {c['definition']}",
             f"- **Index:** {c['index']}",
             f"- **Measures:** {c['measures']}",
             f"- **Routes:** {', '.join(c.get('routes', [])) or '—'}",
             f"- **Proof-DAG nodes:** {', '.join(c.get('proof_nodes', [])) or '—'}",
             f"- **Search aliases:** {', '.join(f'`{a}`' for a in c.get('aliases', []))}"]
    if c.get("normalization"):
        lines.append(f"- **Normalization:** {c['normalization']}")
    lines += ["", "## Crosswalks", ""]
    for x in atlas["crosswalks"]:
        if c["id"] in (x["from"], x["to"]):
            other = x["to"] if x["from"] == c["id"] else x["from"]
            ev = ", ".join(f"[`{d['name']}`]({up}{d['file']})" for d in x.get("lean", [])) or \
                ", ".join(f"[{Path(q).name}]({up}{q})" for q in x.get("source", []))
            lines.append(f"- **{x['relation']}** [{other}]({other}.md) [{x['status']}]: {x['formula']}"
                         + (f" — {ev}" if ev else "") + (f" *Caveat: {x['caveat']}*" if x.get("caveat") else ""))
    lines += ["", "## Lean definitions and their proved rewrites", ""]
    for d in c.get("lean", []):
        rec = fam.get(d["name"])
        names = [(q, n) for q, ns in rec["rewrites"].items() for n in ns] if rec else []
        lines.append(f"- [`{d['name']}`]({up}{d['file']}): {len(names)} rewrite theorem(s)"
                     + (": " + ", ".join(f"[`{n}`]({up}{q})" for q, n in names) if names else ""))
    rows = sorted(((s_[c["id"]], p, titles[p]) for p, s_ in scores_by_path.items() if c["id"] in s_),
                  key=lambda t: (-t[0], t[1]))[:30]
    lines += ["", "## Files using this coordinate (top 30 by tag score)", ""] + table(rows, 3)
    return "\n".join(lines) + "\n"


def route_page(route, atlas, route_by_path, titles):
    coords = [c["id"] for c in atlas["coordinates"] if route in c.get("routes", [])]
    rows = sorted(((s_[route], p, titles[p]) for p, s_ in route_by_path.items() if route in s_),
                  key=lambda t: (-t[0], t[1]))[:60]
    lines = [f"# Route {route}", "",
             "*Generated by `python3 scripts/search_catalog.py --write`. Route tags count literal route terms plus the routes "
             "of each file's top atlas coordinates; the mathematics of the route is in the "
             "[proof-dependency DAG](../../PROOF_DEPENDENCY_DAG.md).*", "",
             "Coordinates: " + (", ".join(f"[`{c}`](../coordinates/{c}.md)" for c in coords) or "—"), "",
             "## Files (top 60 by tag score)", ""] + table(rows, 3)
    return "\n".join(lines) + "\n"


def index_page(atlas, counts):
    lines = ["# Static search index", "",
             "*Generated by `python3 scripts/search_catalog.py --write`. How to use these files: [README.md](README.md).*", "",
             "## Coordinates", "", "| Coordinate | Family | Name | Tagged files |", "| --- | --- | --- | --- |"]
    for c in atlas["coordinates"]:
        lines.append(f"| [{c['id']}](coordinates/{c['id']}.md) | {c['family']} | {c['name']} | {counts['coord'].get(c['id'], 0)} |")
    lines += ["", "## Routes", "", "| Route | Tagged files |", "| --- | --- |"]
    for r in atlas["route_terms"]:
        lines.append(f"| [{r}](routes/{r}.md) | {counts['route'].get(r, 0)} |")
    lines += ["", "## Machine-readable shards", ""]
    lines += [f"- [{name}]({name}) — {n} records" for name, n in counts["files"].items()]
    return "\n".join(lines) + "\n"


def build(root=ROOT):
    atlas = json.loads((root / "docs/coordinate-atlas.json").read_text(encoding="utf-8"))
    registry = json.loads((root / "docs/proof-obligations.json").read_text(encoding="utf-8"))
    tagger = Tagger(atlas, registry)
    paths = tracked(root)
    texts = {p: (root / p).read_text(encoding="utf-8", errors="replace") for p in paths}
    stripped = {p: strip_lean_comments(t) for p, t in texts.items() if p.endswith(".lean")}
    shards = {name: [] for name, _ in SHARDS}
    scores_by_path, route_by_path, titles = {}, {}, {}
    digest = hashlib.sha256()
    for name in ("docs/coordinate-atlas.json", "docs/proof-obligations.json", "scripts/search_catalog.py"):
        digest.update(name.encode() + b"\0" + hashlib.sha256((root / name).read_bytes()).digest())
    for p in paths:
        digest.update(p.encode() + b"\0" + hashlib.sha256(texts[p].encode()).digest())
        rec, cs, rs = record(p, texts[p], tagger, stripped.get(p))
        shards[next(n for n, rule in SHARDS if rule(p))].append(rec)
        scores_by_path[p], route_by_path[p], titles[p] = cs, rs, rec["title"]
    families = rewrite_families(stripped)
    files = {f"catalog-{n}.jsonl": "".join(json.dumps(r, ensure_ascii=False, sort_keys=True) + "\n" for r in recs)
             for n, recs in shards.items()}
    for name, letters in REWRITE_SHARDS:
        part = [f for f in families if f["definition"][0].lower() in letters]
        files[f"rewrite-families-{name}.jsonl"] = "".join(json.dumps(f, ensure_ascii=False, sort_keys=True) + "\n" for f in part)
    fam = {f["definition"]: f for f in families}
    for c in atlas["coordinates"]:
        files[f"coordinates/{c['id']}.md"] = coordinate_page(c, atlas, scores_by_path, titles, fam)
    for r in atlas["route_terms"]:
        files[f"routes/{r}.md"] = route_page(r, atlas, route_by_path, titles)
    counts = {"coord": Counter(c for s_ in scores_by_path.values() for c in s_),
              "route": Counter(r for s_ in route_by_path.values() for r in s_),
              "files": {n: body.count("\n") for n, body in files.items() if n.endswith(".jsonl")}}
    files["INDEX.md"] = index_page(atlas, counts)
    manifest = {"schema": SCHEMA, "generator": "scripts/search_catalog.py",
                "input_fingerprint": digest.hexdigest(),
                "counts": {**counts["files"], "rewrite_families": len(families),
                           "rewrite_theorems": sum(len(ns) for f in families for ns in f["rewrites"].values())}}
    files["MANIFEST.json"] = json.dumps(manifest, indent=2) + "\n"
    too_big = {n: len(b.encode()) for n, b in files.items() if len(b.encode()) > 300_000}
    if too_big:
        raise SystemExit(f"generated search file exceeds 300 KB (GitHub code search skips >384 KB): {too_big}")
    return files


def expected_on_disk(files):
    present = set()
    for d in TOPIC_DIRS:
        present |= {f"{d}/{p.name}" for p in (OUT / d).glob("*.md")} if (OUT / d).is_dir() else set()
    present |= {p.name for p in OUT.glob("*.jsonl")} | ({"MANIFEST.json", "INDEX.md"} & {p.name for p in OUT.glob("*")})
    return present - set(files)


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    parser.add_argument("--strict", action="store_true", help="with --check, fail when outputs are stale")
    args = parser.parse_args()
    files = build()
    if args.write:
        for name, body in files.items():
            (OUT / name).parent.mkdir(parents=True, exist_ok=True)
            (OUT / name).write_text(body, encoding="utf-8")
        for name in expected_on_disk(files):
            (OUT / name).unlink()
        print(json.dumps(json.loads(files["MANIFEST.json"])["counts"]))
        return
    missing = [n for n in files if not (OUT / n).is_file()]
    if missing:
        raise SystemExit(f"missing generated search files: {missing}; run python3 scripts/search_catalog.py --write")
    for name in files:
        if name.endswith(".jsonl"):
            for k, line in enumerate((OUT / name).read_text(encoding="utf-8").splitlines(), 1):
                try:
                    json.loads(line)
                except json.JSONDecodeError as exc:
                    raise SystemExit(f"{name}:{k}: invalid JSON ({exc})")
    stale = [n for n, body in files.items() if (OUT / n).read_text(encoding="utf-8") != body]
    stale += sorted(expected_on_disk(files))
    if stale:
        msg = f"static search corpus is stale ({', '.join(stale)}); run python3 scripts/search_catalog.py --write"
        if args.strict:
            raise SystemExit(msg)
        print(("::warning::" if os.environ.get("GITHUB_ACTIONS") else "WARNING: ") + msg)
    else:
        print("PASS: static search corpus is current")


if __name__ == "__main__":
    sys.exit(main())
