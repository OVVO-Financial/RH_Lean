#!/usr/bin/env python3
"""Query the RHLean mathematical knowledge graph.

The repository is large enough (9,819 declarations, 6,616 named proofs, 189k
lines) that ordinary text search no longer finds the interesting structure.
This tool answers the questions that actually drive the research:

    proofq show      <theorem>              what is it, and what does it touch
    proofq ancestors <theorem>              everything it transitively depends on
    proofq descendants <theorem>            everything that transitively uses it
    proofq path      <A> <B>                a concrete dependency chain
    proofq common-ancestors <A> <B>         shared machinery
    proofq diff      <A> <B>                what A's cone has that B's lacks
    proofq terminal-cone                    what does / does not feed the terminal theorem
    proofq dominators                       choke points every route must cross
    proofq bridges   [--carrier C]          compatible pairs with no connecting path
    proofq duplicates                       propositions of identical shape proved twice
    proofq nogos     [--related X]          recorded no-go results near a topic
    proofq orphans   [--near X]             strong results outside the terminal cone
    proofq search    <pattern>              find declarations by name or facet

The graph is read from a JSON file produced by `scripts/decl_graph.py` (either
the cheap syntactic graph or, via `--from-lean`, the exact elaborated one).  If
no graph file is given and none is found, one is built in memory from source.

## What this tool can and cannot tell you

It reports *structure*: which declaration references which, and which names use
the same vocabulary.  A `bridges` hit means two declarations share a carrier tag
and have no dependency path between them.  That is a place to look, not a claim
that a bridge theorem exists or is true.  `AGENTS.md` is explicit that two
quantities must never be treated as equal because their descriptions sound
similar, and nothing here is evidence of equality.  Confirm every candidate
against compiled Lean source before acting on it.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path

import rhlean_kg as kg

DEFAULT_GRAPH = Path("decl-graph.json")
DEFAULT_TERMINAL = "RHLean.Proof.TerminalMertensForward.riemannHypothesis_of_squarePrefixEnergy"


class KnowledgeGraph:
    """Declaration graph plus the semantic facet layer, with reachability."""

    def __init__(self, data: dict) -> None:
        self.data = data
        self.nodes: dict[str, dict] = data["declarations"]
        self.provenance: dict = data.get("provenance", {})
        self.edges: dict[str, list[str]] = {
            name: sorted(set(e["statement_refs"]) | set(e["proof_refs"]))
            for name, e in self.nodes.items()
        }
        # Drop edges to declarations the graph does not contain.
        for name, deps in self.edges.items():
            self.edges[name] = [d for d in deps if d in self.nodes]
        self.rev = kg.invert(self.edges)
        self.facets = kg.load_facets()
        self._tags: dict[str, dict] | None = None
        self._closure: dict[str, int] | None = None
        self._order: list[str] | None = None

    # -- loading -----------------------------------------------------------

    @classmethod
    def load(cls, path: Path | None) -> "KnowledgeGraph":
        if path is not None:
            return cls(json.loads(path.read_text(encoding="utf-8")))
        if DEFAULT_GRAPH.is_file():
            return cls(json.loads(DEFAULT_GRAPH.read_text(encoding="utf-8")))
        sys.stderr.write(
            f"note: no {DEFAULT_GRAPH} found; building the syntactic graph in memory\n"
        )
        import decl_graph

        return cls(decl_graph.build_graph())

    # -- semantic layer ----------------------------------------------------

    @property
    def tags(self) -> dict[str, dict]:
        if self._tags is None:
            self._tags = kg.tag_all(self.nodes, self.facets)
        return self._tags

    def carriers(self, name: str) -> set[str]:
        return set(self.tags[name]["facets"].get("carrier", ()))

    def roles(self, name: str) -> set[str]:
        return set(self.tags[name]["roles"])

    # -- name resolution ---------------------------------------------------

    def resolve(self, query: str) -> list[str]:
        """Map a user-typed name to declaration ids, most specific first."""

        if query in self.nodes:
            return [query]
        short = query.rsplit(".", 1)[-1]
        exact = [n for n in self.nodes if n.split("#", 1)[0].rsplit(".", 1)[-1] == short]
        if exact:
            return sorted(exact)
        suffix = [n for n in self.nodes if n.split("#", 1)[0].endswith("." + query)]
        if suffix:
            return sorted(suffix)
        lowered = query.lower()
        return sorted(n for n in self.nodes if lowered in n.lower())

    def require(self, query: str) -> str:
        hits = self.resolve(query)
        if not hits:
            raise SystemExit(f"error: no declaration matches {query!r}")
        if len(hits) > 1:
            sys.stderr.write(f"note: {query!r} matches {len(hits)} declarations:\n")
            for h in hits[:10]:
                sys.stderr.write(f"  {h}\n")
            if len(hits) > 10:
                sys.stderr.write(f"  ... and {len(hits) - 10} more\n")
            sys.stderr.write(f"using {hits[0]}\n\n")
        return hits[0]

    # -- reachability ------------------------------------------------------

    @property
    def order(self) -> list[str]:
        if self._order is None:
            self._order = kg.topological_order(self.edges, set(self.nodes))
        return self._order

    @property
    def closure(self) -> dict[str, int]:
        """Transitive dependency sets as bitmasks, one per declaration.

        A DAG with 9,819 nodes and 34k edges has an all-pairs closure far too
        big to store as sets, but as Python big integers it is a few megabytes
        and makes `reaches` a single bit test -- which is what makes the
        all-pairs `bridges` scan tractable.
        """

        if self._closure is None:
            index = {n: i for i, n in enumerate(sorted(self.nodes))}
            self._index = index
            mask: dict[str, int] = {}
            for name in reversed(self.order):
                acc = 0
                for dep in self.edges.get(name, ()):
                    acc |= mask.get(dep, 0) | (1 << index[dep])
                mask[name] = acc
            for name in self.nodes:
                mask.setdefault(name, 0)
            self._closure = mask
        return self._closure

    def reaches(self, src: str, dst: str) -> bool:
        """Does `src` transitively depend on `dst`?"""

        self.closure  # noqa: B018 - populate the index
        return bool(self.closure[src] >> self._index[dst] & 1)

    def ancestors(self, name: str) -> set[str]:
        """Everything `name` transitively depends on (its dependency cone)."""

        return kg.reachable(self.edges, [name]) - {name}

    def descendants(self, name: str) -> set[str]:
        """Everything that transitively depends on `name`."""

        return kg.reachable(self.rev, [name]) - {name}

    # -- presentation ------------------------------------------------------

    def label(self, name: str) -> str:
        entry = self.nodes[name]
        loc = ""
        if entry.get("path"):
            loc = f"  [{entry['path']}:{entry.get('line', 0)}]"
        return f"{entry.get('kind', '?'):9s} {name}{loc}"

    def brief(self, name: str) -> str:
        entry = self.nodes[name]
        car = ",".join(self.tags[name]["facets"].get("carrier", ())) or "-"
        rol = ",".join(self.tags[name]["roles"]) or "-"
        return (
            f"{entry.get('used_by_count', 0):4d} users  {name}\n"
            f"            carrier={car}  role={rol}"
        )


# --------------------------------------------------------------------------
# Commands
# --------------------------------------------------------------------------


def cmd_show(g: KnowledgeGraph, args) -> int:
    name = g.require(args.name)
    entry = g.nodes[name]
    tag = g.tags[name]
    print(name)
    print("=" * len(name))
    print(f"kind      : {entry.get('kind')}")
    if entry.get("path"):
        print(f"location  : {entry['path']}:{entry.get('line')}")
    print(f"module    : {entry.get('module')}")
    print(f"used by   : {entry.get('used_by_count', 0)} declarations")
    print(f"uses      : {entry.get('uses_count', 0)} declarations")
    if entry.get("shape"):
        print(f"shape     : {' '.join(entry['shape'])}")
    print()
    print("semantic facets (search heuristics, not mathematical claims)")
    for facet, values in sorted(tag["facets"].items()):
        print(f"  {facet:20s} {', '.join(values)}")
    print(f"  {'role':20s} {', '.join(tag['roles']) or '-'}")
    if args.evidence:
        print("\n  evidence")
        for key, why in sorted(tag["evidence"].items()):
            print(f"    {key:36s} {why}")
    if entry.get("doc"):
        print(f"\ndoc: {entry['doc']}")
    if entry.get("statement_preview"):
        print(f"\nstatement: {entry['statement_preview']}")
    print("\nstatement references")
    for dep in entry["statement_refs"]:
        print(f"  {dep}")
    print("\nproof references")
    for dep in entry["proof_refs"]:
        print(f"  {dep}")
    users = g.rev.get(name, [])
    print(f"\ndirect users ({len(users)})")
    for user in users[: args.limit]:
        print(f"  {user}")
    if len(users) > args.limit:
        print(f"  ... and {len(users) - args.limit} more")
    return 0


def _print_set(g: KnowledgeGraph, names: set[str], limit: int, by_module: bool) -> None:
    if by_module:
        groups: dict[str, list[str]] = defaultdict(list)
        for n in names:
            groups[g.nodes[n].get("module", "?")].append(n)
        for mod in sorted(groups, key=lambda m: (-len(groups[m]), m))[:limit]:
            print(f"  {len(groups[mod]):4d}  {mod}")
        return
    ranked = sorted(names, key=lambda n: (-int(g.nodes[n].get("used_by_count", 0)), n))
    for n in ranked[:limit]:
        print(f"  {g.label(n)}")
    if len(ranked) > limit:
        print(f"  ... and {len(ranked) - limit} more")


def cmd_ancestors(g: KnowledgeGraph, args) -> int:
    name = g.require(args.name)
    anc = g.ancestors(name)
    print(f"{name}")
    print(f"transitive dependencies: {len(anc):,}")
    _print_set(g, anc, args.limit, args.by_module)
    return 0


def cmd_descendants(g: KnowledgeGraph, args) -> int:
    name = g.require(args.name)
    desc = g.descendants(name)
    print(f"{name}")
    print(f"transitive users: {len(desc):,}")
    _print_set(g, desc, args.limit, args.by_module)
    return 0


def cmd_path(g: KnowledgeGraph, args) -> int:
    a, b = g.require(args.source), g.require(args.target)
    path = kg.shortest_path(g.edges, a, b)
    if path is None:
        back = kg.shortest_path(g.edges, b, a)
        if back is None:
            print(f"no dependency path in either direction between\n  {a}\n  {b}")
            print("\nThese two results are mathematically unconnected in the current")
            print("library. If they share a carrier, that is exactly the kind of gap")
            print("`proofq bridges` is built to surface.")
            return 1
        print(f"no path {a} -> {b}; the dependency runs the other way:")
        path = back
    for i, node in enumerate(path):
        print(f"  {'  ' * 0}{i:2d}. {g.label(node)}")
    return 0


def cmd_common_ancestors(g: KnowledgeGraph, args) -> int:
    a, b = g.require(args.source), g.require(args.target)
    sa, sb = g.ancestors(a), g.ancestors(b)
    shared = sa & sb
    print(f"A = {a}  ({len(sa):,} dependencies)")
    print(f"B = {b}  ({len(sb):,} dependencies)")
    print(f"shared: {len(shared):,}")
    _print_set(g, shared, args.limit, args.by_module)
    return 0


def cmd_diff(g: KnowledgeGraph, args) -> int:
    a, b = g.require(args.source), g.require(args.target)
    sa, sb = g.ancestors(a), g.ancestors(b)
    only_a, only_b = sa - sb, sb - sa
    print(f"A = {a}")
    print(f"B = {b}")
    print(f"shared dependencies: {len(sa & sb):,}")
    print()
    print(f"machinery A has that B lacks ({len(only_a):,})")
    _print_set(g, only_a, args.limit, args.by_module)
    print()
    print(f"machinery B has that A lacks ({len(only_b):,})")
    _print_set(g, only_b, args.limit, args.by_module)
    print()
    print("Read this as: if A and B are two coordinates on the same object, these")
    print("lists are what each coordinate can currently reach and the other cannot.")
    return 0


def cmd_terminal_cone(g: KnowledgeGraph, args) -> int:
    root = g.require(args.root)
    cone = g.ancestors(root) | {root}
    proofs = {n for n, e in g.nodes.items() if e.get("kind") in kg.PROOF_KINDS}
    inside = cone & proofs
    outside = proofs - cone
    print(f"terminal root: {root}")
    print(f"declarations in cone : {len(cone):,} of {len(g.nodes):,}")
    print(f"named proofs in cone : {len(inside):,} of {len(proofs):,}")
    print(f"named proofs outside : {len(outside):,}")
    print()
    print("The cone is everything the terminal theorem currently rests on. A strong")
    print("result outside it is not wrong -- it is simply not yet wired into the")
    print("route. Those are the candidates for an unexploited connection.")
    print()
    print(f"strongest named proofs outside the cone (by internal users)")
    ranked = sorted(outside, key=lambda n: (-int(g.nodes[n].get("used_by_count", 0)), n))
    for n in ranked[: args.limit]:
        print(f"  {g.brief(n)}")
    if args.json:
        args.json.write_text(
            json.dumps(
                {
                    "root": root,
                    "cone": sorted(cone),
                    "proofs_in_cone": sorted(inside),
                    "proofs_outside_cone": sorted(outside),
                },
                indent=1,
            )
            + "\n",
            encoding="utf-8",
        )
    return 0


def cmd_dominators(g: KnowledgeGraph, args) -> int:
    root = g.require(args.root)
    idom = kg.dominators(g.edges, root)
    subtree: Counter[str] = Counter()
    for node in idom:
        if node == root:
            continue
        cur = idom[node]
        seen = set()
        while cur != root and cur not in seen:
            seen.add(cur)
            subtree[cur] += 1
            cur = idom.get(cur, root)
        subtree[root] += 1
    print(f"terminal root: {root}")
    print(f"declarations dominated: {len(idom):,}")
    print()
    print("A choke point is a declaration every route from the terminal theorem to")
    print("some part of its cone must pass through. Removing or weakening one of")
    print("these disconnects everything below it -- and strengthening one is felt")
    print("everywhere below it too.")
    print()
    print(f"{'dominated':>9}  declaration")
    for name, count in subtree.most_common(args.limit):
        if name == root:
            continue
        print(f"{count:9d}  {g.label(name)}")
    return 0


def _strength(g: KnowledgeGraph, name: str) -> int:
    return int(g.nodes[name].get("used_by_count", 0))


def cmd_bridges(g: KnowledgeGraph, args) -> int:
    """Compatible declaration pairs with no dependency path between them."""

    proofs = [
        n
        for n, e in g.nodes.items()
        if e.get("kind") in kg.PROOF_KINDS and _strength(g, n) >= args.min_users
    ]
    if args.carrier:
        proofs = [n for n in proofs if args.carrier in g.carriers(n)]

    by_carrier: dict[str, list[str]] = defaultdict(list)
    for n in proofs:
        for c in g.carriers(n):
            by_carrier[c].append(n)

    # Roles that supply different kinds of leverage. A pair is interesting when
    # each side brings something the other does not.
    COMPLEMENT = {
        "exact-equality",
        "equivalence",
        "reindexing-involution",
        "recursion-descent",
        "upper-bound",
        "lower-bound",
        "no-go",
    }

    g.closure  # populate
    candidates: list[tuple[float, str, str, str, set[str]]] = []
    for carrier, members in sorted(by_carrier.items()):
        if len(members) < 2:
            continue
        ranked = sorted(members, key=lambda n: -_strength(g, n))[: args.per_carrier]
        for i, a in enumerate(ranked):
            ra = g.roles(a) & COMPLEMENT
            if not ra:
                continue
            for b in ranked[i + 1 :]:
                rb = g.roles(b) & COMPLEMENT
                if not rb or ra == rb:
                    continue
                if not (ra - rb) or not (rb - ra):
                    continue
                if g.reaches(a, b) or g.reaches(b, a):
                    continue
                if g.nodes[a].get("module") == g.nodes[b].get("module"):
                    continue
                shared_facets = set()
                for facet in ("weight", "clock", "endpoint_convention"):
                    fa = set(g.tags[a]["facets"].get(facet, ()))
                    fb = set(g.tags[b]["facets"].get(facet, ()))
                    shared_facets |= fa & fb
                score = (
                    (_strength(g, a) + _strength(g, b))
                    * (1 + len(shared_facets))
                    * (1 + len(g.carriers(a) & g.carriers(b)))
                )
                candidates.append((score, carrier, a, b, shared_facets))

    candidates.sort(key=lambda t: (-t[0], t[2], t[3]))
    seen_pairs: set[tuple[str, str]] = set()
    print("Candidate missing bridges")
    print("=========================")
    print("Pairs of named proofs that share a carrier vocabulary, bring different")
    print("kinds of leverage, live in different modules, and have NO dependency path")
    print("in either direction.")
    print()
    print("This is a ranked place-to-look list produced from names and statement")
    print("shape. It is not evidence that a bridge theorem exists or is true.")
    print("Check each candidate against compiled source before acting on it.")
    print()
    shown = 0
    for score, carrier, a, b, shared in candidates:
        key = (a, b)
        if key in seen_pairs:
            continue
        seen_pairs.add(key)
        shown += 1
        if shown > args.limit:
            break
        print(f"[{shown:2d}] carrier={carrier}  score={score}")
        print(f"     A {a}")
        print(f"       roles={','.join(sorted(g.roles(a)))}  users={_strength(g, a)}")
        print(f"       {g.nodes[a].get('path')}:{g.nodes[a].get('line')}")
        print(f"     B {b}")
        print(f"       roles={','.join(sorted(g.roles(b)))}  users={_strength(g, b)}")
        print(f"       {g.nodes[b].get('path')}:{g.nodes[b].get('line')}")
        if shared:
            print(f"     also shared: {', '.join(sorted(shared))}")
        print()
    if not shown:
        print("no candidates at these thresholds")
    return 0


def cmd_duplicates(g: KnowledgeGraph, args) -> int:
    groups: dict[str, list[str]] = defaultdict(list)
    for name, entry in g.nodes.items():
        sig = entry.get("signature")
        if (
            sig
            and entry.get("kind") in kg.PROOF_KINDS
            and int(entry.get("signature_constants", 0)) >= args.min_constants
        ):
            groups[str(sig)].append(name)
    dupes = {s: sorted(v) for s, v in groups.items() if len(v) > 1}
    cross = {
        s: v
        for s, v in dupes.items()
        if len({g.nodes[n].get("module") for n in v}) > 1
    }
    print("Propositions with an identical normalized statement signature")
    print("=============================================================")
    print("Binder names, local hypothesis names and numerals are erased; what")
    print("remains is the logical skeleton plus the resolved repository constants.")
    print("Two declarations colliding here state the same shape over the same")
    print("constants -- a candidate duplicate, to be confirmed by reading both.")
    print()
    print(f"signature groups with >1 member : {len(dupes):,}")
    print(f"  of those, spanning >1 module  : {len(cross):,}")
    print()
    ranked = sorted(cross.items(), key=lambda kv: (-len(kv[1]), kv[0]))
    for sig, names in ranked[: args.limit]:
        print(f"signature {sig}  ({len(names)} declarations)")
        for n in names:
            print(f"    {g.label(n)}")
        print()
    return 0


def cmd_nogos(g: KnowledgeGraph, args) -> int:
    nogos = [n for n in g.nodes if "no-go" in g.roles(n)]
    if args.related:
        target = g.require(args.related)
        carriers = g.carriers(target)
        nogos = [n for n in nogos if g.carriers(n) & carriers]
        print(f"no-go results sharing a carrier with {target}")
        print(f"carriers: {', '.join(sorted(carriers)) or '-'}")
    else:
        print("recorded no-go results")
    print()
    print("AGENTS.md treats rediscovery of a recorded no-go as a failed branch")
    print("unless a genuinely new signed ingredient is supplied. Read these before")
    print("proposing a route on the same carrier.")
    print()
    for n in sorted(nogos, key=lambda n: (-_strength(g, n), n))[: args.limit]:
        print(f"  {g.label(n)}")
        doc = g.nodes[n].get("doc")
        if doc:
            print(f"      {doc[:160]}")
    print(f"\n{len(nogos)} no-go declarations total")
    return 0


def cmd_orphans(g: KnowledgeGraph, args) -> int:
    root = g.require(args.root)
    cone = g.ancestors(root) | {root}
    proofs = {n for n, e in g.nodes.items() if e.get("kind") in kg.PROOF_KINDS}
    outside = proofs - cone
    if args.near:
        target = g.require(args.near)
        carriers = g.carriers(target)
        outside = {n for n in outside if g.carriers(n) & carriers}
        print(f"strong results outside the terminal cone sharing a carrier with")
        print(f"  {target}")
        print(f"carriers: {', '.join(sorted(carriers)) or '-'}")
    else:
        print("strong results outside the terminal cone")
    print()
    ranked = sorted(outside, key=lambda n: (-_strength(g, n), n))
    for n in ranked[: args.limit]:
        print(f"  {g.brief(n)}")
        print(f"       {g.nodes[n].get('path')}:{g.nodes[n].get('line')}")
    print(f"\n{len(outside)} named proofs match")
    return 0


def cmd_obligations(g: KnowledgeGraph, args) -> int:
    """Map the open `Prop`-valued statements the RH route is conditional on.

    This repository does not reach RH through one long chain. It reaches it
    through a named proposition that is left as a hypothesis -- the analytic
    consumer is finished, and the arithmetic that would discharge the
    proposition is the open problem. So the useful map is not "what does the
    terminal theorem depend on" but "which propositions is it waiting on, and
    how much of the library already attaches to each".
    """

    # `def Foo : Prop` with no binders is a closed statement -- a research
    # target. `def IsFoo (n : ℕ) : Prop` is a predicate applied all over the
    # library; it is Prop-valued but it is not something anyone is trying to
    # prove. Only the former is an obligation, so binders are the discriminator.
    props = []
    for n, e in g.nodes.items():
        if e.get("kind") not in ("def", "abbrev"):
            continue
        preview = str(e.get("statement_preview", ""))
        m = re.match(r"^\s*(?:\w+\s+)*?(?:def|abbrev)\s+(\S+)(.*?):\s*Prop\s*$", preview)
        if not m:
            continue
        if not args.predicates and m.group(2).strip():
            continue
        props.append(n)
    rows = []
    for n in props:
        desc = g.descendants(n)
        anc = g.ancestors(n)
        reaches_rh = any("riemannhypothesis" in d.lower() for d in desc)
        rows.append((len(desc), len(anc), reaches_rh, n))
    rows.sort(key=lambda r: (-r[0], r[3]))

    if args.rh_only:
        rows = [r for r in rows if r[2]]

    print("Open propositions the RH route is conditional on")
    print("===============================================")
    print("A `def ... : Prop` is a named statement. Where no theorem proves it")
    print("outright, everything downstream of it is conditional. `users` counts")
    print("declarations that transitively depend on the proposition; `built-from`")
    print("counts what the proposition itself is defined in terms of.")
    print()
    print(f"{'users':>6} {'built-from':>10}  {'→RH':>3}  proposition")
    for desc, anc, rh, n in rows[: args.limit]:
        mark = "yes" if rh else "-"
        print(f"{desc:6d} {anc:10d}  {mark:>3}  {n}")
        entry = g.nodes[n]
        if args.verbose and entry.get("doc"):
            print(f"{'':22}{entry['doc'][:140]}")
    print(f"\n{len(rows)} Prop-valued statements match")
    return 0


def cmd_search(g: KnowledgeGraph, args) -> int:
    pattern = re.compile(args.pattern, re.IGNORECASE)
    hits = [n for n in g.nodes if pattern.search(n)]
    if args.carrier:
        hits = [n for n in hits if args.carrier in g.carriers(n)]
    if args.role:
        hits = [n for n in hits if args.role in g.roles(n)]
    ranked = sorted(hits, key=lambda n: (-_strength(g, n), n))
    for n in ranked[: args.limit]:
        print(f"  {g.brief(n)}")
        print(f"       {g.nodes[n].get('path')}:{g.nodes[n].get('line')}")
    print(f"\n{len(hits)} declarations match")
    return 0


def cmd_stats(g: KnowledgeGraph, args) -> int:
    stats = g.data.get("stats", {})
    print("RHLean knowledge graph")
    print("======================")
    print(f"provenance : {g.provenance.get('source', '?')}")
    print(f"producer   : {g.provenance.get('producer', '?')}")
    for key, value in stats.items():
        if isinstance(value, dict):
            continue
        print(f"{key:32s} {value:,}" if isinstance(value, int) else f"{key:32s} {value}")
    print()
    carriers: Counter[str] = Counter()
    roles: Counter[str] = Counter()
    for name in g.nodes:
        carriers.update(g.carriers(name))
        roles.update(g.roles(name))
    print("carrier tags")
    for c, k in carriers.most_common(args.limit):
        print(f"  {k:6d}  {c}")
    print("\nrole tags")
    for r, k in roles.most_common():
        print(f"  {k:6d}  {r}")
    print()
    print(f"authority: {g.provenance.get('authority', '')}")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(
        prog="proofq",
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    # Shared flags live on every subcommand rather than before it, so that
    # `proofq bridges --limit 40` works the way anyone would first type it.
    common = argparse.ArgumentParser(add_help=False)
    common.add_argument("--graph", type=Path, help="declaration graph JSON")
    common.add_argument("--limit", type=int, default=25, help="rows to display")
    common.add_argument(
        "--by-module", action="store_true", help="group results by module"
    )
    sub = parser.add_subparsers(dest="command", required=True)

    p = sub.add_parser("show", help="describe one declaration", parents=[common])
    p.add_argument("name")
    p.add_argument("--evidence", action="store_true", help="show why each tag was applied")
    p.set_defaults(func=cmd_show)

    p = sub.add_parser("ancestors", help="transitive dependencies", parents=[common])
    p.add_argument("name")
    p.set_defaults(func=cmd_ancestors)

    p = sub.add_parser("descendants", help="transitive users", parents=[common])
    p.add_argument("name")
    p.set_defaults(func=cmd_descendants)

    p = sub.add_parser("path", help="a dependency chain between two declarations", parents=[common])
    p.add_argument("source")
    p.add_argument("target")
    p.set_defaults(func=cmd_path)

    p = sub.add_parser("common-ancestors", help="shared machinery of two declarations", parents=[common])
    p.add_argument("source")
    p.add_argument("target")
    p.set_defaults(func=cmd_common_ancestors)

    p = sub.add_parser("diff", help="what one dependency cone has that another lacks", parents=[common])
    p.add_argument("source")
    p.add_argument("target")
    p.set_defaults(func=cmd_diff)

    p = sub.add_parser("terminal-cone", help="classify proofs by the terminal theorem", parents=[common])
    p.add_argument("--root", default=DEFAULT_TERMINAL)
    p.add_argument("--json", type=Path, help="write the cone classification")
    p.set_defaults(func=cmd_terminal_cone)

    p = sub.add_parser("dominators", help="choke points of the terminal cone", parents=[common])
    p.add_argument("--root", default=DEFAULT_TERMINAL)
    p.set_defaults(func=cmd_dominators)

    p = sub.add_parser("bridges", help="compatible pairs with no connecting path", parents=[common])
    p.add_argument("--carrier")
    p.add_argument("--min-users", type=int, default=1)
    p.add_argument("--per-carrier", type=int, default=120)
    p.set_defaults(func=cmd_bridges)

    p = sub.add_parser("duplicates", help="propositions of identical shape", parents=[common])
    p.add_argument(
        "--min-constants",
        type=int,
        default=2,
        help="minimum repository constants a signature must mention (default 2)",
    )
    p.set_defaults(func=cmd_duplicates)

    p = sub.add_parser("nogos", help="recorded no-go results", parents=[common])
    p.add_argument("--related")
    p.set_defaults(func=cmd_nogos)

    p = sub.add_parser("orphans", help="strong results outside the terminal cone", parents=[common])
    p.add_argument("--root", default=DEFAULT_TERMINAL)
    p.add_argument("--near")
    p.set_defaults(func=cmd_orphans)

    p = sub.add_parser(
        "obligations", help="open propositions the RH route is conditional on",
        parents=[common],
    )
    p.add_argument("--rh-only", action="store_true", help="only those reaching an RH theorem")
    p.add_argument(
        "--predicates",
        action="store_true",
        help="also include Prop-valued predicates that take binders",
    )
    p.add_argument("--verbose", action="store_true", help="show doc comments")
    p.set_defaults(func=cmd_obligations)

    p = sub.add_parser("search", help="find declarations", parents=[common])
    p.add_argument("pattern")
    p.add_argument("--carrier")
    p.add_argument("--role")
    p.set_defaults(func=cmd_search)

    p = sub.add_parser("stats", help="graph and facet summary", parents=[common])
    p.set_defaults(func=cmd_stats)

    args = parser.parse_args()
    graph = KnowledgeGraph.load(args.graph)
    return int(args.func(graph, args) or 0)


if __name__ == "__main__":
    raise SystemExit(main())
