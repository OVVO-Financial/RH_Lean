#!/usr/bin/env python3
"""One-shot follow-up: preserve conjunctive premise sets in the reduction layer."""

from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]


def read(path):
    return (ROOT / path).read_text(encoding="utf-8")


def write(path, text):
    (ROOT / path).write_text(text, encoding="utf-8")


def replace_once(path, old, new):
    text = read(path)
    n = text.count(old)
    if n != 1:
        raise SystemExit(f"{path}: expected one match, found {n}\n{old}")
    write(path, text.replace(old, new, 1))


def sub_once(path, pattern, repl):
    text = read(path)
    new, n = re.subn(pattern, lambda _m: repl, text, count=1, flags=re.S | re.M)
    if n != 1:
        raise SystemExit(f"{path}: expected one regex match, found {n}: {pattern}")
    write(path, new)


replace_once(
    "scripts/proofq.py",
    '''        self._closed_props: set[str] | None = None\n        self._reductions: dict[str, list[tuple[str, str]]] | None = None\n''',
    '''        self._closed_props: set[str] | None = None\n        self._reduction_rules: dict[str, list[tuple[tuple[str, ...], str]]] | None = None\n        self._reductions: dict[str, list[tuple[str, str]]] | None = None\n''',
)

new_reduction_block = r'''    @property
    def reduction_rules(self) -> dict[str, list[tuple[tuple[str, ...], str]]]:
        """Exact proposition-level reduction rules, preserving conjunction.

        A rule `(X, (A, B), t)` means theorem `t` proves X assuming *both* A
        and B.  Premises are never split into independent logical implications.
        Exact unconditional `A ↔ B` theorems contribute the two unary rules
        `A <- B` and `B <- A`.
        """

        if self._reduction_rules is None:
            out: dict[str, list[tuple[tuple[str, ...], str]]] = defaultdict(list)
            for name, entry in self.nodes.items():
                if entry.get("kind") not in kg.PROOF_KINDS or entry.get("hard_blocked"):
                    continue
                iff = list(entry.get("iff_props", ()))
                if len(iff) == 2:
                    a, b = iff
                    out[a].append(((b,), name))
                    out[b].append(((a,), name))
                    continue
                target = entry.get("establishes_prop")
                if target not in self.closed_props:
                    continue
                premises = tuple(sorted({
                    p for p in entry.get("closed_assumes", ())
                    if p in self.closed_props and p != target
                }))
                if premises:
                    out[target].append((premises, name))
            self._reduction_rules = {
                k: sorted(set(v), key=lambda x: (x[0], x[1])) for k, v in out.items()
            }
        return self._reduction_rules

    @property
    def reductions(self) -> dict[str, list[tuple[str, str]]]:
        """Dependency projection of `reduction_rules` for graph navigation.

        Each premise of a conjunctive rule appears as an edge so reachability
        can find everything a route may require.  These projected edges are
        *not* independent implications; use `reduction_rules` whenever logical
        sufficiency matters.
        """

        if self._reductions is None:
            out: dict[str, list[tuple[str, str]]] = defaultdict(list)
            for target, rules in self.reduction_rules.items():
                for premises, via in rules:
                    for dep in premises:
                        out[target].append((dep, via))
            self._reductions = {k: sorted(set(v)) for k, v in out.items()}
        return self._reductions

    @property
    def reduction_graph(self) -> dict[str, list[str]]:
        """Ordinary dependency projection of the conjunctive reduction rules."""
        return {
            p: sorted({d for d, _via in self.reductions.get(p, ())})
            for p in self.closed_props
        }

    @property
    def sufficient_graph(self) -> dict[str, list[str]]:
        """Unary implications after already-proved premises are discharged.

        An edge X -> Y exists only when some compiled rule for X has exactly one
        unresolved named premise Y; all of that rule's other premises are already
        proved.  Reachability here therefore supports the literal statement
        "Y alone (together with established library facts) is sufficient for X".
        """

        out: dict[str, set[str]] = {p: set() for p in self.closed_props}
        for target, rules in self.reduction_rules.items():
            for premises, _via in rules:
                unresolved = [p for p in premises if self.status(p) != kg.STATUS_PROVED]
                if len(unresolved) == 1:
                    out[target].add(unresolved[0])
        return {p: sorted(v) for p, v in out.items()}

    def reduction_component_data(
        self,
    ) -> tuple[list[list[str]], dict[str, int], dict[int, set[int]]]:
        comps = kg.strongly_connected_components(self.reduction_graph, self.closed_props)
        which: dict[str, int] = {}
        for i, comp in enumerate(comps):
            for node in comp:
                which[node] = i
        cgraph: dict[int, set[int]] = {i: set() for i in range(len(comps))}
        for src, deps in self.reduction_graph.items():
            a = which[src]
            for dep in deps:
                b = which[dep]
                if a != b:
                    cgraph[a].add(b)
        return comps, which, cgraph

    def reduction_cone(self, root: str = DEFAULT_RH_PROPOSITION) -> set[str]:
        """All propositions appearing as premises anywhere below `root`."""
        if root not in self.nodes:
            root = self.require(root)
        return kg.reachable(self.reduction_graph, [root])

    def sufficient_cone(self, root: str = DEFAULT_RH_PROPOSITION) -> set[str]:
        """Propositions that individually suffice for `root` via unary rules."""
        if root not in self.nodes:
            root = self.require(root)
        return kg.reachable(self.sufficient_graph, [root])

    def is_rh_relevant(self, proposition: str) -> bool:
        return proposition in self.reduction_cone(DEFAULT_RH_PROPOSITION)

    def is_rh_sufficient(self, proposition: str) -> bool:
        return proposition in self.sufficient_cone(DEFAULT_RH_PROPOSITION)

    def open_leaf_components(self, root: str | None = None) -> list[list[str]]:
        comps, which, cgraph = self.reduction_component_data()
        if root is None:
            allowed = set(range(len(comps)))
        else:
            if root not in self.nodes:
                root = self.require(root)
            start = which[root]
            allowed: set[int] = set()
            stack = [start]
            while stack:
                i = stack.pop()
                if i in allowed:
                    continue
                allowed.add(i)
                stack.extend(cgraph[i])
        leaves: list[list[str]] = []
        for i in sorted(allowed):
            if any(j in allowed for j in cgraph[i]):
                continue
            open_members = [n for n in comps[i] if self.status(n) == kg.STATUS_OPEN]
            if open_members:
                leaves.append(sorted(open_members))
        return leaves

    def carriers(self, name: str) -> set[str]:
'''

sub_once(
    "scripts/proofq.py",
    r"    @property\n    def reductions\(self\).*?^    def carriers\(self, name: str\) -> set\[str\]:\n",
    new_reduction_block,
)

new_cmd_reductions = r'''def cmd_reductions(g: KnowledgeGraph, args) -> int:
    """Print the exact conjunctive reduction rules beneath a proposition."""

    root = g.require(args.name)
    seen: set[str] = set()

    def walk(node: str, depth: int) -> None:
        if depth > args.depth:
            return
        mark = {"open": "OPEN", "proved": "PROVED", "refuted": "REFUTED"}.get(
            g.status(node), g.status(node).upper()
        )
        lead = "    " * depth
        print(f"{lead}{node}   [{mark}]")
        if node in seen:
            print(f"{lead}  (already shown; possibly an iff-equivalence component)")
            return
        seen.add(node)
        for premises, thm in g.reduction_rules.get(node, ()):
            short = thm.rsplit(".", 1)[-1]
            noun = "premise" if len(premises) == 1 else "premises"
            print(f"{lead}  via {short} requires {len(premises)} {noun} together:")
            for dep in premises:
                walk(dep, depth + 1)

    walk(root, 0)
    leaves = g.open_leaf_components(root)
    print()
    print(f"open leaf components beneath this proposition: {len(leaves)}")
    for comp in leaves:
        print(f"  {comp[0]}")
        for eq in comp[1:]:
            print(f"      equivalent: {eq}")
        print(f"      {g.nodes[comp[0]].get('path')}:{g.nodes[comp[0]].get('line')}")
    return 0


def cmd_open_leaves(g: KnowledgeGraph, args) -> int:
    """Open SCC leaves in the dependency projection of reduction rules."""

    root = DEFAULT_RH_PROPOSITION if args.rh_only else None
    components = g.open_leaf_components(root)
    rows = []
    for comp in components:
        users = max((len(g.descendants(n)) for n in comp), default=0)
        rows.append((users, comp))
    rows.sort(key=lambda r: (-r[0], r[1][0]))

    print("Open leaves of the reduction system")
    print("===================================")
    print("Conjunctive theorem premises remain grouped as rules. Exact iff bridges")
    print("are collapsed to strongly connected proposition components before")
    print("leafhood is decided. A listed leaf is RH-relevant, not necessarily")
    print("sufficient for RH by itself when it belongs to a multi-premise package.")
    print()
    print(f"{'users':>6}  {'RH-path':>7}  {'alone→RH':>8}  proposition/component")
    for users, comp in rows[: args.limit]:
        n = comp[0]
        car = ",".join(sorted(g.carriers(n))) or "-"
        relevant = g.is_rh_relevant(n)
        sufficient = g.is_rh_sufficient(n)
        print(
            f"{users:6d}  {'yes' if relevant else '-':>7}  "
            f"{'yes' if sufficient else '-':>8}  {n}"
        )
        print(f"{'':25}{g.nodes[n].get('path')}:{g.nodes[n].get('line')}  carrier={car}")
        for eq in comp[1:]:
            print(f"{'':25}≡ {eq}")
        if args.verbose and g.nodes[n].get("doc"):
            print(f"{'':25}{g.nodes[n]['doc'][:150]}")
    print(f"\n{len(rows)} open leaf components")
    return 0
'''

sub_once(
    "scripts/proofq.py",
    r"def cmd_reductions\(g: KnowledgeGraph, args\) -> int:\n.*?^def cmd_frontier\(g: KnowledgeGraph, args\) -> int:\n",
    new_cmd_reductions + "\n\ndef cmd_frontier(g: KnowledgeGraph, args) -> int:\n",
)

replace_once(
    "scripts/proofq.py",
    '''        reaches_rh = g.is_rh_sufficient(n)\n''',
    '''        reaches_rh = g.is_rh_relevant(n)\n''',
)
replace_once(
    "scripts/proofq.py",
    '''            and g.is_rh_sufficient(n)\n''',
    '''            and g.is_rh_relevant(n)\n''',
)

# Make obligation output precise about multi-premise rules.
replace_once(
    "scripts/proofq.py",
    '''    print("Open propositions the RH route is conditional on")\n    print("===============================================")\n''',
    '''    print("Open propositions appearing on RH reduction routes")\n    print("==================================================")\n''',
)
replace_once(
    "scripts/proofq.py",
    '''    print(f"{'users':>6} {'built-from':>10}  {'→RH':>3}  proposition")\n''',
    '''    print(f"{'users':>6} {'built-from':>10}  {'RH-path':>7}  proposition")\n''',
)
replace_once(
    "scripts/proofq.py",
    '''        mark = "yes" if rh else "-"\n        print(f"{desc:6d} {anc:10d}  {mark:>3}  {n}")\n''',
    '''        mark = "yes" if rh else "-"\n        print(f"{desc:6d} {anc:10d}  {mark:>7}  {n}")\n''',
)

# Documentation: acyclicity is an invariant, not a precision certificate; rules
# preserve conjunction; generated counts are not hard-coded.
p = "docs/KNOWLEDGE_GRAPH.md"
replace_once(
    p,
    '''Two checks bound the\ndamage: the graph it produces is acyclic (a graph full of spurious edges would\nnot be), and it recovers exactly the 6,616 named proofs the independent\ninventory counts.  Where layer 2a and layer 2b disagree, **2b is\nauthoritative**, per `AGENTS.md` rule 1.\n''',
    '''The source graph is required to be acyclic and its named-proof count is\ncross-checked against the independent inventory, but neither check is a\nprecision certificate for name resolution.  The hosted build compares it with\nthe elaborated graph.  Where layer 2a and layer 2b disagree, **2b is\nauthoritative**, per `AGENTS.md` rule 1.\n''',
)
replace_once(
    p,
    '''  of its conclusion and it has no hypotheses at all -- no inline hypothesis like\n  `1 ≤ R`, no assumed proposition, no structure-typed binder.  `A ↔ B`\n  establishes neither side; `A → B` establishes `B` while assuming `A`;\n  `¬ X` **refutes** `X` rather than establishing it;\n''',
    '''  of its conclusion and has no unresolved raw/data hypotheses.  Named closed\n  proposition assumptions are discharged by a least fixpoint.  An exact\n  unconditional `A ↔ B` contributes the two conditional rules `A ← B` and\n  `B ← A`; it proves neither side from nothing.  `¬ X` **refutes** `X`;\n''',
)
replace_once(
    p,
    '''Layer 6 is the proposition reduction graph: an edge `X → Y` whenever a\ncompiled theorem proves `X` from `Y`.  An unconditional exact `X ↔ Y` contributes\nboth directions.  Before leafhood is computed, strongly connected components are\ncollapsed, so coordinate equivalences do not create fake non-leaves.  Following\nthe condensed DAG downward reaches the **open leaves** -- the propositions where\nmathematics still has to happen.\n''',
    '''Layer 6 is a proposition **reduction-rule system**.  A theorem proving `X`\nfrom `A` and `B` records one conjunctive rule `X ← {A,B}`; it is never split\ninto the false claims `A → X` and `B → X`.  For navigation, those rules have an\nordinary dependency projection `X → A`, `X → B`.  Exact unconditional `X ↔ Y`\nadds the two unary rules.  Strongly connected components of the projection are\ncollapsed before leafhood is computed, so coordinate equivalences do not create\nfake non-leaves.  The tool separately reports whether an open proposition is\nmerely on an RH reduction route or can by itself imply RH after proved premises\nare discharged.\n''',
)
replace_once(
    p,
    '''proofq obligations   --rh-only          # open propositions sufficient for RH\n''',
    '''proofq obligations   --rh-only          # open propositions on RH reduction routes\n''',
)
replace_once(
    p,
    '''`proofq open-leaves --rh-only` is the shortest useful description of the whole\nproject.  Everything conditional sits above one of those propositions.\n''',
    '''`proofq open-leaves --rh-only` is the shortest useful description of the\ncurrent RH-relevant frontier.  Multi-premise packages remain conjunctive, so a\nleaf on that list is not automatically sufficient for RH by itself; the\n`alone→RH` column distinguishes the unary-sufficient case.\n''',
)
replace_once(
    p,
    '''continuation, the zeta identity, RH -- and none of the arithmetic.  The other\n6,587 proofs are not orphaned work; they are the attack on the hypothesis.\n''',
    '''continuation, the zeta identity, RH -- and none of the arithmetic.  The\nremaining thousands of proofs are not orphaned work; they are attacks on the\nconditional propositions feeding that consumer.\n''',
)

# Self-delete; the workflow that executes this script is removed separately.
(ROOT / "scripts/apply_kg_hyperedge_fix.py").unlink()
print("Applied conjunctive reduction-rule fix.")
