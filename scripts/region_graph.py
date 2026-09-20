#!/usr/bin/env python3
"""Regional geometry layer: where on [1, x] does a declaration actually work?

The declaration graph in `decl_graph.py` says what depends on what. It says
nothing about *location*: that `squareRootTransportTopFibreBlock` lives on
`x/2 < q <= x` while `primeDilatedLowCofactorMass` lives on `c < R`, and that
those are different parts of the number line which only an exact bridge theorem
may be used to connect.

This module adds that axis. For every declaration it reads the statement text,
finds the variables the statement itself pins to the square-root scale (via
`squareRootEndpoint v` or `v ^ 2 - 1`, both definitional in compiled source),
and then matches the actual index ranges and inequalities against the region
vocabulary in `scripts/region_facets.json`.

Two graphs come out of that:

  containment   the exact geometry. `mid-band` sits inside `above-root` because
                `(R, x/2]` is a subset of `(R, x]`, not because anything in this
                repository says so. These edges are arithmetic.

  dependency    the measured overlay. Region A -> region B carries a weight when
                some declaration located in A depends on a declaration located
                in B. These edges are evidence about how the library is wired,
                and they can and do run in both directions between two regions.

The interesting objects are the declarations tagged with two or more span
regions at once. Those are the theorems that actually transport between parts
of the line -- the bridges AGENTS.md rule 5 demands before any two regional
quantities may be identified. `--gaps` reports the region pairs that have no
such theorem.

Evidence grades are never mixed. A `direct` tag means a cut was found in the
statement text. A `lexical` tag means a name contained a word. Only direct tags
count toward coverage, and an untagged declaration is reported as untagged
rather than assigned a plausible region.
"""

from __future__ import annotations

import argparse
import collections
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import decl_graph  # noqa: E402
import rhlean_kg as kg  # noqa: E402

FACETS_PATH = Path(__file__).resolve().parent / "region_facets.json"

# A Lean identifier used as a *term*. The trailing lookahead stops `Nat` in
# `Nat.sqrt R` being read as a bound variable: without it the fragment
# `Nat.sqrt X < Nat.sqrt R` matches "some variable is below Nat", and a plain
# monotonicity lemma about `Nat.sqrt` gets filed as regional work. That was a
# real false positive on `sqrt_endpoint_root_boundary_dichotomy`.
VAR = r"[A-Za-z_][A-Za-z0-9_']*\b(?!\s*\.)"

# The same, as the *left* operand of a comparison. The lookbehinds stop a match
# starting in the middle of someone else's term: in `Nat.sqrt X < Nat.sqrt R`
# the tail `X < Nat.sqrt R` is not a comparison the statement makes.
LVAR = (
    r"(?<![\w'.])(?<!Nat\.sqrt )(?<!Real\.sqrt )"
    r"[A-Za-z_][A-Za-z0-9_']*\b(?!\s*\.)"
)


def load_facets(path: Path | None = None) -> dict:
    return json.loads((path or FACETS_PATH).read_text(encoding="utf-8"))


def root_variables(statement: str) -> set[str]:
    """Variables this statement pins to the square-root scale.

    A variable `R` is a root-scale variable exactly when the statement spells
    the span as `squareRootEndpoint R` or as `R ^ 2 - 1`. Both are the same
    number by the definition cited in `region_facets.json`, so a range written
    against `R` is a range written against `sqrt(x + 1)`.

    Without this step `Finset.Ico 1 N` would have to be guessed at: for a free
    `N` it is simply the whole range, and only the presence of the span makes it
    the below-root region. Guessing there is the difference between a located
    theorem and a scale-generic one, so the layer refuses to guess.
    """

    found: set[str] = set()
    for match in re.finditer(rf"squareRootEndpoint\s+({VAR})", statement):
        found.add(match.group(1))
    for match in re.finditer(rf"\b({VAR})\s*\^\s*2\s*-\s*1", statement):
        found.add(match.group(1))
    return found


def _span_forms(root: str) -> list[str]:
    escaped = re.escape(root)
    return [rf"squareRootEndpoint\s+{escaped}", rf"{escaped}\s*\^\s*2\s*-\s*1"]


def _expand(pattern: str, root: str | None, span: str | None) -> str:
    out = pattern.replace("{lvar}", LVAR).replace("{var}", VAR)
    if root is not None:
        out = out.replace("{root}", re.escape(root))
    if span is not None:
        # The span may itself be parenthesised in source.
        out = out.replace("{span}", rf"(?:\(\s*)?(?:{span})(?:\s*\))?")
    return out


def _evidence(statement: str, match: re.Match) -> str:
    """The matched cut plus enough context to check it.

    A bare match can read as the opposite of what the statement says: the
    below-root cut inside `squareRootEndpoint R / q < R` matches as `q < R`,
    which looks like the negation of the hypothesis `R < q` sitting next to it.
    Anything printed as evidence has to be checkable against source without
    opening the file, so the surrounding term comes with it.
    """

    lo = max(0, match.start() - 24)
    hi = min(len(statement), match.end() + 12)
    text = " ".join(statement[lo:hi].split())
    return ("..." if lo else "") + text + ("..." if hi < len(statement) else "")


def detect_direct(statement: str, facets: dict) -> dict[str, list[str]]:
    """Region tags backed by a cut in the statement text."""

    hits: dict[str, set[str]] = collections.defaultdict(set)
    roots = root_variables(statement)

    for region, spec in facets["regions"].items():
        for pattern in spec.get("scale_free", ()):
            match = re.search(_expand(pattern, None, None), statement)
            if match:
                hits[region].add(_evidence(statement, match))
        if not spec.get("root_relative"):
            continue
        for root in roots:
            for span in _span_forms(root):
                for pattern in spec["root_relative"]:
                    match = re.search(_expand(pattern, root, span), statement)
                    if match:
                        hits[region].add(_evidence(statement, match))

    return {region: sorted(ev) for region, ev in hits.items()}


def detect_lexical(name: str, module: str, facets: dict) -> dict[str, list[str]]:
    """Region hints from naming only. Always reported as the weaker grade.

    Names in this repository have been wrong before -- a file called
    `PRIME_WHEEL_TRUNCATED_MOBIUS_KERNEL` turned out to be the draft of
    `PrimeWheelRoughSeatCorrelation` -- so a name is a place to look, never a
    place to conclude.
    """

    tokens = set(kg.name_tokens(name)) | set(kg.name_tokens(module.split(".")[-1]))
    joined = "".join(sorted(tokens))
    hits: dict[str, list[str]] = {}
    for region, spec in facets["regions"].items():
        found = []
        for word in spec.get("lexical", ()):
            if word in tokens:
                found.append(f"name token {word!r}")
            elif word in joined and len(word) > 6:
                found.append(f"name contains {word!r}")
        if found:
            hits[region] = found
    return hits


def span_regions(facets: dict) -> set[str]:
    return {r for r, s in facets["regions"].items() if s.get("axis") == "span"}


def containment_closure(facets: dict) -> set[tuple[str, str]]:
    """Transitive subset pairs `(sub, sup)` over the region cuts."""

    pairs = {(e["sub"], e["sup"]) for e in facets["containment"]}
    changed = True
    while changed:
        changed = False
        for a, b in list(pairs):
            for c, d in list(pairs):
                if b == c and (a, d) not in pairs:
                    pairs.add((a, d))
                    changed = True
    return pairs


def incomparable_pairs(facets: dict) -> set[frozenset[str]]:
    """Span regions that neither contains the other.

    Only these can be *crossed*. A declaration mentioning both `below-root` and
    `full-span` has not transported anything: `[1, R)` is part of `[1, x]`, so
    naming both is the containment restating itself. A declaration mentioning
    `below-root` and `above-root`, or `mid-band` and `top-fibre`, has put two
    disjoint stretches of the line in one statement, and that is the thing
    worth finding.
    """

    spans = sorted(span_regions(facets))
    closure = containment_closure(facets)
    out = set()
    for i, a in enumerate(spans):
        for b in spans[i + 1 :]:
            if (a, b) in closure or (b, a) in closure:
                continue
            out.add(frozenset((a, b)))
    return out


DEFINITION_KINDS = {"def", "abbrev", "structure", "instance", "inductive"}


def locating_text(kind: str, statement: str, value: str) -> str:
    """The text that says where a declaration works.

    For a definition the body *is* the object, so the cut in it is the cut of
    the thing being defined. For a theorem only the statement counts: a proof
    may travel through any region it likes on its way to the conclusion, and
    reading proof bodies would tag nearly everything with nearly everything.
    """

    if kind in DEFINITION_KINDS:
        return f"{statement}\n{value}"
    return statement


def build(facets: dict | None = None, graph: dict | None = None) -> dict:
    """Tag every declaration and condense the dependency graph by region."""

    facets = facets or load_facets()
    graph = graph or decl_graph.build_graph(include_docs=False)
    declarations = graph["declarations"]

    # Statement previews in the graph are truncated, and a region cut can sit
    # anywhere in a long binder list, so the text comes from a fresh source
    # parse rather than from the graph.
    source: dict[str, tuple[str, str]] = {}
    for path, text in kg.load_sources():
        for decl in kg.parse_module(path, text):
            source[decl.decl_id] = (decl.statement or "", decl.value or "")

    spans = span_regions(facets)
    crossable = incomparable_pairs(facets)

    # --- grade 1: a cut written in this declaration itself ------------------
    direct: dict[str, dict[str, list[str]]] = {}
    for node_id, entry in declarations.items():
        statement, value = source.get(node_id, ("", ""))
        kind = str(entry.get("kind", ""))
        found = detect_direct(locating_text(kind, statement, value), facets)
        if found:
            direct[node_id] = found

    # --- grade 2: named after an object that is defined by a cut ------------
    # `squareRootTopFibreBlock` is a `def` whose body ranges over
    # `Ioc (x/2) x`. A theorem whose statement mentions it is working in the
    # top fibre, even though the theorem never spells the interval. That is not
    # a guess: the definition is the cut. Definitions inherit from definitions
    # to a fixpoint, then theorems take one hop from their statement.
    derived: dict[str, dict[str, list[str]]] = {}

    def def_refs(entry: dict) -> set[str]:
        # For a definition the body is definitional, not incidental, so both
        # halves of its reference set locate it.
        return set(entry.get("statement_refs", ())) | set(entry.get("proof_refs", ()))

    definitions = [
        n for n, e in declarations.items() if str(e.get("kind", "")) in DEFINITION_KINDS
    ]
    changed = True
    rounds = 0
    while changed and rounds < 12:
        changed = False
        rounds += 1
        for node_id in definitions:
            have = set(direct.get(node_id, {})) | set(derived.get(node_id, {}))
            for ref in def_refs(declarations[node_id]):
                for region in set(direct.get(ref, {})) | set(derived.get(ref, {})):
                    if region in have:
                        continue
                    derived.setdefault(node_id, {}).setdefault(region, []).append(
                        f"defined from {ref}"
                    )
                    have.add(region)
                    changed = True

    for node_id, entry in declarations.items():
        if str(entry.get("kind", "")) in DEFINITION_KINDS:
            continue
        have = set(direct.get(node_id, {}))
        for ref in entry.get("statement_refs", ()):
            for region in set(direct.get(ref, {})) | set(derived.get(ref, {})):
                if region in have:
                    continue
                derived.setdefault(node_id, {}).setdefault(region, []).append(
                    f"statement mentions {ref}"
                )
                have.add(region)

    # --- grade 3: a word in a name ------------------------------------------
    tags: dict[str, dict] = {}
    for node_id, entry in declarations.items():
        d = direct.get(node_id, {})
        v = {r: sorted(set(ev))[:3] for r, ev in derived.get(node_id, {}).items()}
        lex = detect_lexical(
            str(entry.get("name", "")), str(entry.get("module", "")), facets
        )
        # A weaker grade that a stronger one already covers is not extra
        # information; drop it so the weak grades never pad the report.
        lex = {r: ev for r, ev in lex.items() if r not in d and r not in v}
        if d or v or lex:
            tags[node_id] = {
                "direct": d,
                "derived": v,
                "lexical": lex,
                "module": entry.get("module", ""),
                "status": entry.get("status", ""),
                "line": entry.get("line", 0),
                "path": entry.get("path", ""),
                "kind": entry.get("kind", ""),
            }

    located = {
        n: t for n, t in tags.items() if t["direct"] or t["derived"]
    }

    # Dependency overlay. Located declarations only: a lexical guess is not a
    # basis for claiming the library wires one region into another.
    region_of: dict[str, set[str]] = {
        n: set(t["direct"]) | set(t["derived"]) for n, t in located.items()
    }
    dep_edges: dict[tuple[str, str], int] = collections.Counter()
    dep_witness: dict[tuple[str, str], list[str]] = collections.defaultdict(list)
    for node_id, entry in declarations.items():
        src = region_of.get(node_id)
        if not src:
            continue
        refs = set(entry.get("statement_refs", ())) | set(entry.get("proof_refs", ()))
        for ref in refs:
            dst = region_of.get(ref)
            if not dst:
                continue
            for a in src:
                for b in dst:
                    if a == b:
                        continue
                    dep_edges[(a, b)] += 1
                    if len(dep_witness[(a, b)]) < 3:
                        dep_witness[(a, b)].append(f"{node_id} -> {ref}")

    # Crossing declarations: one statement carrying two span regions at once.
    # This is where a transport between parts of the line is written down.
    crossings: list[dict] = []
    for node_id, tag in located.items():
        combined = {**tag["direct"], **tag["derived"]}
        here = sorted(set(combined) & spans)
        crossed = sorted(
            {p for p in crossable if p <= set(here)}, key=lambda p: sorted(p)
        )
        if not crossed:
            continue
        direct_here = set(tag["direct"]) & spans
        grade = (
            "direct"
            if any(p <= direct_here for p in crossed)
            else "derived"
        )
        crossings.append(
            {
                "declaration": node_id,
                "regions": here,
                "crosses": [sorted(p) for p in crossed],
                "grade": grade,
                "status": tag["status"],
                "module": tag["module"],
                "path": tag["path"],
                "line": tag["line"],
                "evidence": {r: combined[r] for r in here},
            }
        )
    crossings.sort(
        key=lambda c: (c["grade"] == "direct", len(c["crosses"]), c["declaration"]),
        reverse=True,
    )

    census_direct = collections.Counter()
    census_derived = collections.Counter()
    census_lexical = collections.Counter()
    modules: dict[str, set[str]] = collections.defaultdict(set)
    for tag in tags.values():
        for region in tag["direct"]:
            census_direct[region] += 1
            modules[region].add(tag["module"])
        for region in tag["derived"]:
            census_derived[region] += 1
            modules[region].add(tag["module"])
        for region in tag["lexical"]:
            census_lexical[region] += 1

    all_modules = {str(e.get("module", "")) for e in declarations.values()}

    return {
        "schema": "rhlean-region-graph/1",
        "provenance": {
            "producer": "scripts/region_graph.py",
            "vocabulary": str(FACETS_PATH.name),
            "status": facets["status"],
            "grades": {
                "direct": "a cut written in this declaration (a theorem's statement, a definition's body)",
                "derived": "this declaration's statement names an object that a cut defines",
                "lexical": "a word in a name; a place to look, never evidence of location",
            },
            "authority": (
                "A region tag records a cut found in statement or definition text. "
                "It is not a claim that two declarations sharing a region are about "
                "the same quantity; AGENTS.md rule 5 still requires an exact bridge "
                "theorem."
            ),
        },
        "regions": {
            region: {
                "axis": spec["axis"],
                "cut": spec["cut"],
                "description": spec["description"],
                "declarations_direct": census_direct.get(region, 0),
                "declarations_derived": census_derived.get(region, 0),
                "declarations_lexical_only": census_lexical.get(region, 0),
                "modules": len(modules.get(region, ())),
            }
            for region, spec in facets["regions"].items()
        },
        "containment": facets["containment"],
        "partitions": facets["partitions"],
        "crossable_pairs": [sorted(p) for p in sorted(crossable, key=sorted)],
        "dependency_edges": [
            {
                "from": a,
                "to": b,
                "weight": w,
                "witnesses": dep_witness[(a, b)],
            }
            for (a, b), w in sorted(dep_edges.items(), key=lambda kv: -kv[1])
        ],
        "crossings": crossings,
        "tags": tags,
        "declaration_ids": sorted(declarations),
        "stats": {
            "declarations": len(declarations),
            "tagged_direct": len(direct),
            "tagged_derived_only": len(located) - len(direct),
            "located": len(located),
            "tagged_lexical_only": len(tags) - len(located),
            "untagged": len(declarations) - len(tags),
            "modules": len(all_modules),
            "modules_located": len(set().union(*modules.values()) if modules else set()),
            "crossing_declarations": len(crossings),
            "definition_closure_rounds": rounds,
        },
    }


def module_profiles(data: dict) -> dict[str, dict]:
    """Per-module region profile -- the granularity the modules themselves have.

    A helper lemma usually carries no cut, but the module it sits in does. This
    is aggregation of direct evidence, not propagation of a guess: a module is
    listed under a region because some declaration *in it* states that cut.
    """

    profile: dict[str, dict[str, int]] = collections.defaultdict(collections.Counter)
    for tag in data["tags"].values():
        for region in set(tag["direct"]) | set(tag["derived"]):
            profile[tag["module"]][region] += 1
    return {m: dict(c) for m, c in sorted(profile.items())}


def _located_count(data: dict, region: str) -> int:
    info = data["regions"][region]
    return info["declarations_direct"] + info["declarations_derived"]


def region_gaps(data: dict) -> list[dict]:
    """Region pairs with no theorem that states both, and no dependency edge.

    A gap is not a defect. Two regions may have nothing to say to each other.
    It is a place to look: if a route needs to move a quantity from one of these
    regions to the other, nothing in the library currently does it, and the
    bridge would have to be proved rather than assumed.
    """

    crossed = {frozenset(p) for c in data["crossings"] for p in c["crosses"]}
    wired = {(e["from"], e["to"]) for e in data["dependency_edges"]}
    crossable = {frozenset(p) for p in data["crossable_pairs"]}

    gaps = []
    for pair in sorted(crossable, key=sorted):
        a, b = sorted(pair)
        if pair in crossed:
            continue
        if (a, b) in wired or (b, a) in wired:
            continue
        if True:
            size_a = _located_count(data, a)
            size_b = _located_count(data, b)
            populated = size_a > 0 and size_b > 0
            if not populated:
                continue
            gaps.append({"regions": [a, b], "sizes": [size_a, size_b]})
    return gaps


def census_ranges() -> list[tuple[int, str]]:
    """Re-derive the raw index-range census the vocabulary was built from.

    Run this after the library grows. If a frequent range shape here has no
    region in `region_facets.json`, the vocabulary has gone stale and is
    silently under-reporting rather than being wrong out loud.
    """

    counts: collections.Counter = collections.Counter()
    pattern = re.compile(r"Finset\.(Ico|Icc|Ioc|Ioo|range)\s+")

    def argument(text: str, index: int) -> tuple[str | None, int]:
        if index >= len(text):
            return None, index
        if text[index] == "(":
            depth = 0
            for j in range(index, len(text)):
                if text[j] == "(":
                    depth += 1
                elif text[j] == ")":
                    depth -= 1
                    if depth == 0:
                        return text[index : j + 1], j + 1
            return None, index
        match = re.match(rf"{VAR}|\d+", text[index:])
        if match:
            return match.group(0), index + match.end()
        return None, index

    for path, text in kg.load_sources():
        for decl in kg.parse_module(path, text):
            statement = decl.statement or ""
            for match in pattern.finditer(statement):
                kind = match.group(1)
                first, pos = argument(statement, match.end())
                if first is None:
                    continue
                if kind == "range":
                    counts[f"range {first}"] += 1
                    continue
                pos += len(statement[pos:]) - len(statement[pos:].lstrip())
                second, _ = argument(statement, pos)
                if second is None:
                    continue
                counts[f"{kind} {first} {second}"] += 1
    return [(n, k) for k, n in counts.most_common()]


def check_vocabulary(facets: dict) -> list[str]:
    """Problems visible in the vocabulary file alone, without touching sources.

    Runs before the graph is built. A pattern that does not compile would
    otherwise take down `build()` with a traceback, and the traceback would
    hide every other problem in the file behind the first one.
    """

    problems: list[str] = []
    known = set(facets["regions"])

    for region, spec in facets["regions"].items():
        if spec.get("axis") not in {"span", "factor"}:
            problems.append(f"{region}: unknown axis {spec.get('axis')!r}")
        for group in ("root_relative", "scale_free"):
            for pattern in spec.get(group, ()):
                try:
                    re.compile(_expand(pattern, "R", "squareRootEndpoint R"))
                except re.error as exc:
                    problems.append(
                        f"{region}/{group}: {pattern!r} does not compile: {exc}"
                    )

    for a, b in containment_closure(facets):
        if a == b:
            problems.append(f"containment is cyclic at {a}")

    for edge in facets["containment"]:
        for side in ("sub", "sup"):
            if edge[side] not in known:
                problems.append(f"containment names unknown region {edge[side]!r}")

    closure = containment_closure(facets)
    for part in facets["partitions"]:
        if part["whole"] not in known:
            problems.append(f"partition names unknown region {part['whole']!r}")
        for piece in part["parts"]:
            if piece not in known:
                problems.append(f"partition names unknown region {piece!r}")
            elif (piece, part["whole"]) not in closure:
                problems.append(
                    f"partition claims {piece} is part of {part['whole']}, "
                    "but containment does not record it"
                )

    return problems


def check_against_library(data: dict, facets: dict) -> list[str]:
    """Problems only the library can reveal: a vocabulary that has gone stale.

    The failure this guards against is silent. A region file that still claims
    a partition whose witness theorem has been renamed, or a cut the library no
    longer writes that way, keeps producing a clean-looking report while
    measuring less and less.
    """

    problems: list[str] = []
    declarations = set(data.get("declaration_ids", ()))

    for part in facets["partitions"]:
        witness = part.get("witness")
        # Checked against every declaration, not just the tagged ones: a
        # witness may legitimately carry no region of its own, and reporting it
        # missing then would be a false alarm that trains people to ignore the
        # gate.
        if witness and witness not in declarations:
            problems.append(
                f"partition witness {witness} is not a declaration in the graph "
                "(renamed or removed?)"
            )

    for region, info in data["regions"].items():
        spec = facets["regions"][region]
        has_patterns = bool(spec.get("root_relative")) or bool(spec.get("scale_free"))
        if has_patterns and info["declarations_direct"] == 0:
            problems.append(
                f"{region}: has detection patterns but matches nothing; "
                "the library may have changed how it writes this cut"
            )

    return problems


def report(data: dict, verbose: bool = False) -> None:
    stats = data["stats"]
    print("REGIONAL GEOMETRY OF THE LIBRARY")
    print("=" * 72)
    print(data["provenance"]["status"])
    print()
    total = max(stats["declarations"], 1)
    print(
        f"{stats['located']} of {stats['declarations']} declarations are located "
        f"({100 * stats['located'] / total:.1f}%): "
        f"{stats['tagged_direct']} state a cut themselves, "
        f"{stats['tagged_derived_only']} name an object a cut defines."
    )
    print(
        f"{stats['modules_located']} of {stats['modules']} modules contain a located "
        "declaration."
    )
    print(
        f"{stats['untagged']} declarations give no location at all and are reported "
        "as untagged, not placed."
    )
    print()

    print("REGIONS")
    print("-" * 72)
    for region, info in sorted(
        data["regions"].items(),
        key=lambda kv: -(kv[1]["declarations_direct"] + kv[1]["declarations_derived"]),
    ):
        print(f"  {region:<14} {info['cut']}")
        print(
            f"  {'':<14} {info['declarations_direct']:>5} direct "
            f"+ {info['declarations_derived']:>5} derived, "
            f"{info['modules']:>3} modules"
            + (
                f"   (+{info['declarations_lexical_only']} name-only, not counted)"
                if info["declarations_lexical_only"]
                else ""
            )
        )
    print()

    print("CONTAINMENT (exact, from the cut definitions)")
    print("-" * 72)
    for edge in data["containment"]:
        print(f"  {edge['sub']:<14} ⊂ {edge['sup']:<14}  {edge['why']}")
    for part in data["partitions"]:
        print(
            f"  {part['whole']:<14} = {' ⊎ '.join(part['parts'])}"
        )
        print(f"  {'':<14}   {part['why']}")
        print(f"  {'':<14}   witness: {part['witness']}")
    print()

    print("DEPENDENCY OVERLAY (measured, from the declaration graph)")
    print("-" * 72)
    if not data["dependency_edges"]:
        print("  no cross-region dependency edges")
    for edge in data["dependency_edges"]:
        print(f"  {edge['from']:<14} -> {edge['to']:<14} {edge['weight']:>6} edges")
        if verbose:
            for witness in edge["witnesses"]:
                print(f"  {'':<14}    {witness}")
    pairs = {(e["from"], e["to"]) for e in data["dependency_edges"]}
    both = sorted({tuple(sorted(p)) for p in pairs if (p[1], p[0]) in pairs})
    if both:
        print()
        print(
            "  Not acyclic, and that is expected: these pairs depend on each other "
            "in both directions."
        )
        for a, b in both:
            print(f"    {a} <-> {b}")
    print()

    direct_cross = [c for c in data["crossings"] if c["grade"] == "direct"]
    print(
        f"REGION-CROSSING DECLARATIONS ({len(direct_cross)} direct, "
        f"{len(data['crossings']) - len(direct_cross)} derived)"
    )
    print("-" * 72)
    print("  A declaration covering two regions that neither contains: where the")
    print("  library actually puts disjoint stretches of the line in one statement.")
    print("  Nested pairs are excluded -- naming both [1, R) and [1, x] transports")
    print("  nothing, it restates the containment.")
    print()
    by_pair = collections.Counter()
    for cross in data["crossings"]:
        for pair in cross["crosses"]:
            by_pair[" + ".join(pair)] += 1
    for pair, count in by_pair.most_common():
        print(f"    {pair:<34} {count:>5} declarations")
    print()
    shown = data["crossings"] if verbose else direct_cross[:20]
    for cross in shown:
        crosses = "; ".join(" + ".join(p) for p in cross["crosses"])
        print(f"  [{cross['status']:<10}] {crosses}   ({cross['grade']})")
        print(f"      {cross['declaration']}")
        print(f"      {cross['path']}:{cross['line']}")
        if verbose:
            for region, evidence in cross["evidence"].items():
                print(f"        {region}: {'; '.join(evidence)}")
    if not verbose and len(direct_cross) > 20:
        print(f"  ... {len(direct_cross) - 20} more direct (--verbose for all)")
    print()

    gaps = region_gaps(data)
    print(f"REGION PAIRS WITH NO BRIDGE ({len(gaps)} of {len(data['crossable_pairs'])})")
    print("-" * 72)
    if not gaps:
        print("  every crossable pair of populated span regions is crossed or wired")
    for gap in gaps:
        a, b = gap["regions"]
        print(
            f"  {a} ({gap['sizes'][0]}) <-> {b} ({gap['sizes'][1]}): "
            "no crossing declaration, no dependency edge"
        )
    print()
    print("  A gap is a place to look, not a defect. If a route needs to move a")
    print("  quantity across one of these, nothing in the library does it yet and")
    print("  the bridge has to be proved rather than assumed.")


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Regional geometry layer over the RHLean declaration graph."
    )
    parser.add_argument("--verbose", action="store_true", help="show evidence and all crossings")
    parser.add_argument("--json", type=Path, help="write the region graph as JSON")
    parser.add_argument("--dot", type=Path, help="write the region graph as Graphviz DOT")
    parser.add_argument("--region", help="list declarations located in one region")
    parser.add_argument("--module", help="region profile of one module (substring match)")
    parser.add_argument("--modules", action="store_true", help="region profile of every module")
    parser.add_argument(
        "--census",
        action="store_true",
        help="re-derive the raw index-range census the vocabulary was built from",
    )
    parser.add_argument(
        "--min-census", type=int, default=5, help="census cutoff (default 5)"
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="verify the vocabulary against the library; nonzero exit on a problem",
    )
    args = parser.parse_args()

    if args.census:
        facets = load_facets()
        print("RAW INDEX-RANGE CENSUS")
        print("=" * 72)
        print("Shapes occurring at least", args.min_census, "times in statement text.")
        print("A frequent shape with no region below means the vocabulary is stale.")
        print()
        for count, shape in census_ranges():
            if count < args.min_census:
                break
            print(f"  {count:>5}  {shape}")
        print()
        print("Regions currently in the vocabulary:", ", ".join(sorted(facets["regions"])))
        return 0

    if args.check:
        facets = load_facets()
        problems = check_vocabulary(facets)
        if problems:
            print("region vocabulary problems:")
            for problem in problems:
                print(f"  {problem}")
            return 1
        data = build(facets)
        problems = check_against_library(data, facets)
        if problems:
            print("region vocabulary problems:")
            for problem in problems:
                print(f"  {problem}")
            return 1
        print(
            f"region vocabulary OK: {len(data['regions'])} regions, "
            f"{data['stats']['tagged_direct']} declarations state a cut, "
            f"{data['stats']['located']} located, "
            f"{len(data['crossings'])} crossings"
        )
        return 0

    data = build()

    if args.json:
        args.json.write_text(json.dumps(data, indent=2, sort_keys=True), encoding="utf-8")
        print(f"wrote {args.json}")

    if args.dot:
        lines = ["digraph regions {", "  rankdir=BT;", "  node [shape=box];"]
        for region, info in data["regions"].items():
            located = info["declarations_direct"] + info["declarations_derived"]
            label = f"{region}\\n{info['cut']}\\n{located} decls"
            style = "" if located else ' style=dashed'
            lines.append(f'  "{region}" [label="{label}"{style}];')
        for edge in data["containment"]:
            lines.append(
                f'  "{edge["sub"]}" -> "{edge["sup"]}" [color=black penwidth=2 label="subset of"];'
            )
        for edge in data["dependency_edges"]:
            lines.append(
                f'  "{edge["from"]}" -> "{edge["to"]}" '
                f'[color=gray50 style=dashed label="{edge["weight"]}"];'
            )
        lines.append("}")
        args.dot.write_text("\n".join(lines) + "\n", encoding="utf-8")
        print(f"wrote {args.dot}")

    if args.region:
        region = args.region
        if region not in data["regions"]:
            print(f"unknown region {region!r}; known: {', '.join(sorted(data['regions']))}")
            return 2
        info = data["regions"][region]
        print(f"{region}: {info['cut']}")
        print(info["description"])
        print("-" * 72)
        rows = [(n, t) for n, t in data["tags"].items() if region in t["direct"]]
        if not rows:
            print("  no declaration states this cut")
        for node_id, tag in sorted(rows):
            print(f"  [{tag['status']:<10}] {node_id}")
            print(f"      {tag['path']}:{tag['line']}")
            if args.verbose:
                print(f"      evidence: {'; '.join(tag['direct'][region])}")
        inherited = [(n, t) for n, t in data["tags"].items() if region in t["derived"]]
        if inherited:
            print()
            print(f"  {len(inherited)} further declarations name an object this cut")
            print("  defines:")
            limit = len(inherited) if args.verbose else 20
            for node_id, tag in sorted(inherited)[:limit]:
                print(f"      [{tag['status']:<10}] {node_id}")
                if args.verbose:
                    print(f"          {'; '.join(tag['derived'][region])}")
            if not args.verbose and len(inherited) > 20:
                print(f"      ... {len(inherited) - 20} more (--verbose)")
        lexical = [n for n, t in data["tags"].items() if region in t["lexical"]]
        if lexical:
            print()
            print(f"  {len(lexical)} further declarations match by name only, which is")
            print("  a place to look and not evidence of location:")
            for node_id in sorted(lexical)[: 20 if not args.verbose else len(lexical)]:
                print(f"      {node_id}")
        return 0

    if args.module or args.modules:
        profiles = module_profiles(data)
        if args.module:
            profiles = {m: p for m, p in profiles.items() if args.module.lower() in m.lower()}
            if not profiles:
                print(f"no module matching {args.module!r} states a region cut")
                print("That is not the same as the module having no location: most")
                print("declarations inherit their region from a caller and state no cut.")
                return 0
        for module, counts in profiles.items():
            parts = ", ".join(f"{r} x{n}" for r, n in sorted(counts.items(), key=lambda kv: -kv[1]))
            print(f"{module}")
            print(f"    {parts}")
        return 0

    report(data, verbose=args.verbose)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
