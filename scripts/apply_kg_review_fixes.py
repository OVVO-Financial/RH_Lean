#!/usr/bin/env python3
"""One-shot patcher for the PR #585 knowledge-graph review fixes.

This file is intentionally self-deleting.  It exists only because the GitHub
connector cannot apply a textual patch to an existing file; the workflow that
runs it checks out the branch, applies these exact source edits locally, removes
this patcher and its workflow, and pushes the resulting commit.
"""

from __future__ import annotations

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def read(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


def write(path: str, text: str) -> None:
    (ROOT / path).write_text(text, encoding="utf-8")


def replace_once(path: str, old: str, new: str) -> None:
    text = read(path)
    count = text.count(old)
    if count != 1:
        raise SystemExit(f"{path}: expected one exact match, found {count}\n--- needle ---\n{old}")
    write(path, text.replace(old, new, 1))


def sub_once(path: str, pattern: str, repl: str, *, flags: int = 0) -> None:
    text = read(path)
    new, count = re.subn(pattern, repl, text, count=1, flags=flags)
    if count != 1:
        raise SystemExit(f"{path}: expected one regex match, found {count}: {pattern}")
    write(path, new)


# ---------------------------------------------------------------------------
# 1. Count and parse same-line attributed declarations.
# ---------------------------------------------------------------------------

replace_once(
    "scripts/proof_inventory.py",
    '''DECL_RE = re.compile(\n    r"^\\s*(?:(?:private|protected|noncomputable|unsafe)\\s+)*"\n    r"(theorem|lemma|def|abbrev|structure|class|inductive|instance|example|axiom)\\b"\n)\nNAMED_PROOF_RE = re.compile(\n    r"^\\s*(?:(?:private|protected|noncomputable|unsafe)\\s+)*"\n    r"(theorem|lemma)\\s+([^\\s(:{\\[]+)"\n)\n''',
    '''ATTR_PREFIX = r"(?:@\\[[^\\n]*?\\]\\s*)*"\nMODIFIER_PREFIX = r"(?:(?:private|protected|noncomputable|unsafe|partial|scoped|local)\\s+)*"\nDECL_RE = re.compile(\n    r"^\\s*" + ATTR_PREFIX + MODIFIER_PREFIX\n    + r"(theorem|lemma|def|abbrev|structure|class|inductive|instance|example|axiom|opaque)\\b"\n)\nNAMED_PROOF_RE = re.compile(\n    r"^\\s*" + ATTR_PREFIX + MODIFIER_PREFIX\n    + r"(theorem|lemma)\\s+([^\\s(:{\\[]+)"\n)\n''',
)

replace_once(
    "scripts/rhlean_kg.py",
    '''_MODIFIERS = r"(?:(?:private|protected|noncomputable|unsafe|partial|scoped|local)\\s+)*"\nDECL_START_RE = re.compile(\n    r"^" + _MODIFIERS + r"(" + "|".join(DECL_KEYWORDS) + r")\\b"\n)\nDECL_NAME_RE = re.compile(\n    r"^" + _MODIFIERS + r"(" + "|".join(DECL_KEYWORDS) + r")\\s+([^\\s(:{\\[⦃]+)"\n)\n''',
    '''_MODIFIERS = r"(?:(?:private|protected|noncomputable|unsafe|partial|scoped|local)\\s+)*"\n_ATTR_PREFIX = r"(?:@\\[[^\\n]*?\\]\\s*)*"\nDECL_START_RE = re.compile(\n    r"^" + _ATTR_PREFIX + _MODIFIERS + r"(" + "|".join(DECL_KEYWORDS) + r")\\b"\n)\nDECL_NAME_RE = re.compile(\n    r"^" + _ATTR_PREFIX + _MODIFIERS + r"(" + "|".join(DECL_KEYWORDS) + r")\\s+([^\\s(:{\\[⦃]+)"\n)\n''',
)

replace_once(
    "scripts/rhlean_kg.py",
    '''        if ATTR_RE.match(stripped):\n            flush(idx - 1)\n            continue\n''',
    '''        if ATTR_RE.match(stripped) and not DECL_START_RE.match(stripped):\n            # Attribute-only command.  A same-line `@[simp] theorem ...` must\n            # fall through to the declaration parser below.\n            flush(idx - 1)\n            continue\n''',
)

# An equivalence-valued hypothesis is not the same as assuming both sides.
replace_once(
    "scripts/rhlean_kg.py",
    '''_RAW_HYPOTHESIS_GLYPHS = ("≤", "<", "≥", ">", "=", "∈", "∣", "≠", "∀", "∃", "¬")''',
    '''_RAW_HYPOTHESIS_GLYPHS = (\n    "≤", "<", "≥", ">", "=", "∈", "∣", "≠", "∀", "∃", "¬", "↔", "∧", "∨"\n)''',
)


# ---------------------------------------------------------------------------
# 2. Explicit SCC support.  Declaration dependencies are expected acyclic;
#    proposition reductions deliberately are not, because exact iff bridges
#    create equivalence components.
# ---------------------------------------------------------------------------

replace_once(
    "scripts/rhlean_kg.py",
    '''def topological_order(graph: dict[str, list[str]], nodes: set[str]) -> list[str]:\n''',
    '''def strongly_connected_components(\n    graph: dict[str, list[str]], nodes: set[str] | None = None\n) -> list[list[str]]:\n    """Kosaraju SCCs, implemented iteratively so a 10k-node graph is safe."""\n\n    keep = set(graph) if nodes is None else set(nodes)\n    for deps in graph.values():\n        keep.update(d for d in deps if nodes is None or d in nodes)\n\n    seen: set[str] = set()\n    finish: list[str] = []\n    for root in sorted(keep):\n        if root in seen:\n            continue\n        seen.add(root)\n        stack: list[tuple[str, object]] = [\n            (root, iter(d for d in graph.get(root, ()) if d in keep))\n        ]\n        while stack:\n            node, raw_it = stack[-1]\n            it = raw_it  # iterator, kept opaque only to satisfy the type checker\n            try:\n                nxt = next(it)  # type: ignore[arg-type]\n            except StopIteration:\n                stack.pop()\n                finish.append(node)\n                continue\n            if nxt in seen:\n                continue\n            seen.add(nxt)\n            stack.append((nxt, iter(d for d in graph.get(nxt, ()) if d in keep)))\n\n    rev = invert({n: [d for d in graph.get(n, ()) if d in keep] for n in keep})\n    seen.clear()\n    out: list[list[str]] = []\n    for root in reversed(finish):\n        if root in seen:\n            continue\n        comp: list[str] = []\n        seen.add(root)\n        stack = [root]\n        while stack:\n            node = stack.pop()\n            comp.append(node)\n            for nxt in rev.get(node, ()):\n                if nxt not in seen:\n                    seen.add(nxt)\n                    stack.append(nxt)\n        out.append(sorted(comp))\n    return out\n\n\ndef topological_order(graph: dict[str, list[str]], nodes: set[str]) -> list[str]:\n''',
)


# ---------------------------------------------------------------------------
# 3. Correct proof-status fixpoint and record exact proposition rules.
# ---------------------------------------------------------------------------

new_compute_status = r'''def compute_status(
    nodes: dict[str, dict],
    tags: dict[str, dict] | None = None,
) -> tuple[dict[str, str], dict[str, list[str]]]:
    """Classify declarations and derive proposition-level proof rules.

    Closed `def X : Prop` declarations are the research propositions.  A theorem
    can close one only when every *hard* hypothesis is absent and every named
    closed proposition it assumes has already been closed.  Parameterised Prop
    hypotheses and structure/class/inductive binders are hard blockers: they are
    data the theorem requires, not globally discharged propositions.

    Exact unconditional `A ↔ B` theorems contribute both implication rules.  The
    least fixpoint therefore propagates proved status across compiled coordinate
    equivalences instead of leaving an equivalent proposition artificially open.
    """

    closed = closed_propositions(nodes)
    all_props = prop_valued_defs(nodes)
    carriers = {
        n for n, e in nodes.items()
        if e.get("kind") in ("structure", "class", "inductive")
    }
    parameterised_props = all_props - closed

    assumed_all: dict[str, list[str]] = {}
    rules: dict[str, list[tuple[set[str], str]]] = defaultdict(list)
    refutes: dict[str, list[str]] = defaultdict(list)

    for name, entry in nodes.items():
        if entry.get("kind") not in PROOF_KINDS:
            continue

        stmt = set(entry.get("statement_refs", ()))
        concl = list(entry.get("conclusion_refs", ()))
        hypothesis_refs = stmt - set(concl)
        prop_assumptions = sorted(hypothesis_refs & all_props)
        closed_assumptions = sorted(hypothesis_refs & closed)

        hard_blocked = bool(entry.get("has_raw_hypothesis")) or bool(
            hypothesis_refs & (parameterised_props | carriers)
        )
        assumed_all[name] = prop_assumptions
        entry["closed_assumes"] = closed_assumptions
        entry["hard_blocked"] = hard_blocked

        conclusion_props = [r for r in concl if r in closed]
        shape = set(entry.get("shape") or ())

        if "¬" in shape and len(concl) == 1 and len(conclusion_props) == 1:
            target = conclusion_props[0]
            entry["refutes_prop"] = target
            refutes[target].append(name)
            continue

        # B from A (or from several named closed propositions).  Raw/data
        # hypotheses block a global proposition rule, but named closed premises
        # are allowed to discharge later in the fixpoint.
        if not hard_blocked and len(concl) == 1 and len(conclusion_props) == 1:
            target = conclusion_props[0]
            entry["establishes_prop"] = target
            rules[target].append((set(closed_assumptions), name))
            continue

        # An exact unconditional A ↔ B is two proposition implications.  Do not
        # manufacture this from a theorem that itself assumes another Prop.
        if (
            not hard_blocked
            and "↔" in shape
            and len(concl) == 2
            and len(conclusion_props) == 2
            and not prop_assumptions
        ):
            a, b = conclusion_props
            entry["iff_props"] = [a, b]
            rules[a].append(({b}, name))
            rules[b].append(({a}, name))

    proved_props: set[str] = set()
    changed = True
    while changed:
        changed = False
        for prop in closed - proved_props:
            for premises, _thm in rules.get(prop, ()):
                if premises <= proved_props:
                    proved_props.add(prop)
                    changed = True
                    break

    status: dict[str, str] = {}
    for name, entry in nodes.items():
        kind = entry.get("kind")
        if kind in PROOF_KINDS:
            if tags is not None and "no-go" in tags[name]["roles"]:
                status[name] = STATUS_NOGO
            elif any(a not in proved_props for a in assumed_all.get(name, ())):
                status[name] = STATUS_REDUCED
            else:
                status[name] = STATUS_PROVED
        elif name in closed:
            if name in proved_props:
                status[name] = STATUS_PROVED
            elif refutes.get(name):
                status[name] = STATUS_REFUTED
            else:
                status[name] = STATUS_OPEN
        else:
            status[name] = STATUS_DEFINITION
    return status, assumed_all
'''

sub_once(
    "scripts/rhlean_kg.py",
    r"def compute_status\(\n.*?^    return status, assumed\n",
    new_compute_status,
    flags=re.S | re.M,
)


# ---------------------------------------------------------------------------
# 4. Keep elaborated edges only between retained written declarations; report
#    SCCs and provide an explicit acyclicity gate.
# ---------------------------------------------------------------------------

replace_once(
    "scripts/decl_graph.py",
    '''    def to_id(raw: str) -> str:\n        mod = module_by_name.get(raw)\n        if mod is None:\n            return raw\n        return demangle_private(raw, mod)[0]\n\n    # Source-side metadata, keyed by the same ids.\n''',
    '''    def to_id(raw: str) -> str:\n        mod = module_by_name.get(raw)\n        if mod is None:\n            return raw\n        return demangle_private(raw, mod)[0]\n\n    # References may point at elaborator-generated constants that were filtered\n    # out above.  Drop those edges before statistics/reachability are computed.\n    kept_ids = {demangle_private(r["name"], r["module"])[0] for r in records}\n\n    # Source-side metadata, keyed by the same ids.\n''',
)

replace_once(
    "scripts/decl_graph.py",
    '''        stmt_refs = sorted({to_id(r) for r in rec["typeRefs"]} - {node_id})\n        stmt_refs_set = set(stmt_refs)\n        proof_refs = sorted({to_id(r) for r in rec["valueRefs"]} - {node_id})\n''',
    '''        stmt_refs = sorted(\n            ({to_id(r) for r in rec["typeRefs"]} - {node_id}) & kept_ids\n        )\n        stmt_refs_set = set(stmt_refs)\n        proof_refs = sorted(\n            ({to_id(r) for r in rec["valueRefs"]} - {node_id}) & kept_ids\n        )\n''',
)

replace_once(
    "scripts/decl_graph.py",
    '''    isolated = sorted(n for n in nodes if not combined[n] and not rev.get(n))\n\n    return {\n''',
    '''    isolated = sorted(n for n in nodes if not combined[n] and not rev.get(n))\n    sccs = kg.strongly_connected_components(combined, set(nodes))\n    cyclic = [\n        comp for comp in sccs\n        if len(comp) > 1 or (len(comp) == 1 and comp[0] in combined.get(comp[0], ()))\n    ]\n\n    return {\n''',
)

replace_once(
    "scripts/decl_graph.py",
    '''            "isolated_declarations": len(isolated),\n            "status": dict(sorted(Counter(status.values()).items())),\n''',
    '''            "isolated_declarations": len(isolated),\n            "cyclic_components": len(cyclic),\n            "largest_cyclic_component": max((len(c) for c in cyclic), default=0),\n            "status": dict(sorted(Counter(status.values()).items())),\n''',
)

replace_once(
    "scripts/decl_graph.py",
    '''    print(f"Isolated declarations:               {stats['isolated_declarations']:,}")\n    print(f"Duplicate statement-signature groups:{stats['duplicate_signature_groups']:,}")\n''',
    '''    print(f"Isolated declarations:               {stats['isolated_declarations']:,}")\n    print(f"Cyclic declaration components:       {stats['cyclic_components']:,}")\n    print(f"Duplicate statement-signature groups:{stats['duplicate_signature_groups']:,}")\n''',
)

replace_once(
    "scripts/decl_graph.py",
    '''    parser.add_argument("--no-summary", action="store_true")\n''',
    '''    parser.add_argument("--no-summary", action="store_true")\n    parser.add_argument(\n        "--require-acyclic", action="store_true",\n        help="fail when the retained declaration dependency graph contains a cycle",\n    )\n''',
)

replace_once(
    "scripts/decl_graph.py",
    '''    if args.dot:\n        write_dot(args.dot, graph, args.dot_limit)\n    return 0\n''',
    '''    if args.dot:\n        write_dot(args.dot, graph, args.dot_limit)\n    if args.require_acyclic and int(graph["stats"].get("cyclic_components", 0)):\n        print(\n            f"ERROR: declaration dependency graph has "\n            f"{graph['stats']['cyclic_components']} cyclic component(s)",\n            file=sys.stderr,\n        )\n        return 2\n    return 0\n''',
)

# decl_graph now uses sys.stderr in the acyclicity gate.
replace_once(
    "scripts/decl_graph.py",
    '''import json\nimport re\nfrom collections import Counter\n''',
    '''import json\nimport re\nimport sys\nfrom collections import Counter\n''',
)


# ---------------------------------------------------------------------------
# 5. Proposition implication/equivalence graph and true RH reduction reachability.
# ---------------------------------------------------------------------------

replace_once(
    "scripts/proofq.py",
    '''DEFAULT_GRAPH = Path("decl-graph.json")\nDEFAULT_TERMINAL = "RHLean.Proof.TerminalMertensForward.riemannHypothesis_of_squarePrefixEnergy"\n''',
    '''DEFAULT_GRAPH = Path("decl-graph.json")\nDEFAULT_TERMINAL = "RHLean.Proof.TerminalMertensForward.riemannHypothesis_of_squarePrefixEnergy"\nDEFAULT_RH_PROPOSITION = "RHLean.Analysis.RiemannHypothesisStatement"\n''',
)

new_reductions = r'''    @property
    def reductions(self) -> dict[str, list[tuple[str, str]]]:
        """Proposition reduction graph, including exact iff bridges.

        `X -> (Y, via)` means the compiled theorem `via` proves X from Y.  A
        theorem with hard/raw hypotheses contributes no global rule.  An exact
        unconditional `X ↔ Y` contributes both directions; SCC condensation is
        used by leaf queries so equivalence loops do not hide a frontier.
        """

        if self._reductions is None:
            out: dict[str, list[tuple[str, str]]] = defaultdict(list)
            for name, entry in self.nodes.items():
                if entry.get("kind") not in kg.PROOF_KINDS:
                    continue
                if entry.get("hard_blocked"):
                    continue
                iff = list(entry.get("iff_props", ()))
                if len(iff) == 2:
                    a, b = iff
                    out[a].append((b, name))
                    out[b].append((a, name))
                    continue
                target = entry.get("establishes_prop")
                if target not in self.closed_props:
                    continue
                for dep in entry.get("closed_assumes", ()):
                    if dep in self.closed_props and dep != target:
                        out[target].append((dep, name))
            self._reductions = {k: sorted(set(v)) for k, v in out.items()}
        return self._reductions

    @property
    def reduction_graph(self) -> dict[str, list[str]]:
        return {
            p: sorted({d for d, _via in self.reductions.get(p, ())})
            for p in self.closed_props
        }

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
        if root not in self.nodes:
            root = self.require(root)
        return kg.reachable(self.reduction_graph, [root])

    def is_rh_sufficient(self, proposition: str) -> bool:
        return proposition in self.reduction_cone(DEFAULT_RH_PROPOSITION)

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
    new_reductions,
    flags=re.S | re.M,
)

# Replace the reductions command so its leaf report is SCC-aware.
new_cmd_reductions = r'''def cmd_reductions(g: KnowledgeGraph, args) -> int:
    """Print the reduction tree beneath a proposition."""

    root = g.require(args.name)
    seen: set[str] = set()

    def walk(node: str, depth: int, via: str | None) -> None:
        if depth > args.depth:
            return
        mark = {"open": "OPEN", "proved": "PROVED", "refuted": "REFUTED"}.get(
            g.status(node), g.status(node).upper()
        )
        lead = "    " * depth
        arrow = "reduces to " if depth else ""
        print(f"{lead}{arrow}{node}   [{mark}]")
        if via:
            print(f"{lead}  via {via}")
        if node in seen:
            print(f"{lead}  (already shown; possibly an iff-equivalence component)")
            return
        seen.add(node)
        for dep, thm in g.reductions.get(node, ()):
            walk(dep, depth + 1, thm.rsplit(".", 1)[-1])

    walk(root, 0, None)
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
    """Open SCC leaves of the proposition reduction graph."""

    root = DEFAULT_RH_PROPOSITION if args.rh_only else None
    components = g.open_leaf_components(root)
    rows = []
    for comp in components:
        users = max((len(g.descendants(n)) for n in comp), default=0)
        rows.append((users, comp))
    rows.sort(key=lambda r: (-r[0], r[1][0]))

    print("Open leaves of the reduction DAG")
    print("===============================")
    print("Exact iff bridges are collapsed to strongly connected proposition")
    print("components before leafhood is decided, so an equivalence loop cannot")
    print("hide a genuine open frontier.")
    print()
    print(f"{'users':>6}  {'→RH':>3}  proposition/component")
    for users, comp in rows[: args.limit]:
        n = comp[0]
        car = ",".join(sorted(g.carriers(n))) or "-"
        rh = g.is_rh_sufficient(n)
        print(f"{users:6d}  {'yes' if rh else '-':>3}  {n}")
        print(f"{'':13}{g.nodes[n].get('path')}:{g.nodes[n].get('line')}  carrier={car}")
        for eq in comp[1:]:
            print(f"{'':13}≡ {eq}")
        if args.verbose and g.nodes[n].get("doc"):
            print(f"{'':13}{g.nodes[n]['doc'][:150]}")
    print(f"\n{len(rows)} open leaf components")
    return 0
'''

sub_once(
    "scripts/proofq.py",
    r"def cmd_reductions\(g: KnowledgeGraph, args\) -> int:\n.*?^def cmd_frontier\(g: KnowledgeGraph, args\) -> int:\n",
    new_cmd_reductions + "\n\ndef cmd_frontier(g: KnowledgeGraph, args) -> int:\n",
    flags=re.S | re.M,
)

# Obligations are actually open propositions, and RH membership comes from the
# proposition reduction graph rather than a declaration-name substring.
replace_once(
    "scripts/proofq.py",
    '''        props.append(n)\n''',
    '''        if g.status(n) == kg.STATUS_OPEN:\n            props.append(n)\n''',
)

replace_once(
    "scripts/proofq.py",
    '''        reaches_rh = any("riemannhypothesis" in d.lower() for d in desc)\n''',
    '''        reaches_rh = g.is_rh_sufficient(n)\n''',
)

# Frontier defaults to the actual RH reduction cone.
replace_once(
    "scripts/proofq.py",
    '''            if g.status(n) == "open"\n            and any("riemannhypothesis" in d.lower() for d in g.descendants(n))\n''',
    '''            if g.status(n) == kg.STATUS_OPEN\n            and g.is_rh_sufficient(n)\n''',
)


# ---------------------------------------------------------------------------
# 6. CI: cheap graph gates the source DAG; hosted Lean build executes and
#    compares the authoritative elaborated extractor.
# ---------------------------------------------------------------------------

p = "./.github/workflows/proof-inventory.yml"
replace_once(
    p[2:],
    '''      - 'scripts/semantic_facets.json'\n      - '.github/workflows/proof-inventory.yml'\n''',
    '''      - 'scripts/semantic_facets.json'\n      - 'scripts/lean/DeclGraph.lean'\n      - '.github/workflows/proof-inventory.yml'\n''',
)
# Same path list appears twice (push and pull_request); patch the second copy.
replace_once(
    p[2:],
    '''      - 'scripts/semantic_facets.json'\n      - '.github/workflows/proof-inventory.yml'\n''',
    '''      - 'scripts/semantic_facets.json'\n      - 'scripts/lean/DeclGraph.lean'\n      - '.github/workflows/proof-inventory.yml'\n''',
)

replace_once(
    p[2:],
    '''          python3 scripts/decl_graph.py \\\n            --json decl-graph.json \\\n            --dot decl-graph.dot \\\n            | tee decl-graph.txt\n''',
    '''          python3 scripts/decl_graph.py \\\n            --json decl-graph.json \\\n            --dot decl-graph.dot \\\n            --require-acyclic \\\n            | tee decl-graph.txt\n          python3 - <<'PY'\n          import json\n          inv = json.load(open('proof-inventory.json'))\n          graph = json.load(open('decl-graph.json'))\n          expected = len(inv['named_proofs']) if isinstance(inv.get('named_proofs'), list) else inv['declarations']['theorem'] + inv['declarations']['lemma']\n          actual = graph['stats']['named_proofs']\n          if expected != actual:\n              raise SystemExit(f'named-proof count mismatch: inventory={expected}, graph={actual}')\n          print(f'Independent source counters agree on {actual:,} named proofs.')\n          PY\n''',
)

# Lean workflow path filters: rerun authoritative extraction when its producer or
# source-side metadata/parser changes.
for _ in range(2):
    replace_once(
        ".github/workflows/lean.yml",
        '''      - 'scripts/lean_diagnostic_inventory.py'  # the dependency-noise gate\n      - '.github/workflows/lean.yml'     # changes to this audit workflow\n''',
        '''      - 'scripts/lean_diagnostic_inventory.py'  # the dependency-noise gate\n      - 'scripts/lean/DeclGraph.lean'    # exact declaration graph extractor\n      - 'scripts/decl_graph.py'          # exact graph ingestion/validation\n      - 'scripts/rhlean_kg.py'           # source metadata/status semantics\n      - '.github/workflows/lean.yml'     # changes to this audit workflow\n''',
    )

# Insert exact graph execution immediately after the hosted project build.
replace_once(
    ".github/workflows/lean.yml",
    '''      - name: Build Lean project\n        id: directbuild\n        continue-on-error: true\n        run: lake build RHLean > lean-build.log 2>&1\n\n''',
    '''      - name: Build Lean project\n        id: directbuild\n        continue-on-error: true\n        run: lake build RHLean > lean-build.log 2>&1\n\n      # The source-level declaration graph is a fast navigation index.  This is\n      # the authoritative dependency graph: constants actually recorded by the\n      # elaborated environment, including dependencies introduced by simp,\n      # instances, notation and macro expansion.\n      - name: Validate exact elaborated declaration graph\n        if: steps.directbuild.outcome == 'success'\n        run: |\n          lake env lean --run scripts/lean/DeclGraph.lean lean-decl-graph.jsonl\n          python3 scripts/decl_graph.py \\\n            --from-lean lean-decl-graph.jsonl \\\n            --json lean-decl-graph.json \\\n            --require-acyclic\n          python3 scripts/decl_graph.py \\\n            --json syntactic-decl-graph.json \\\n            --require-acyclic \\\n            --no-summary\n          python3 scripts/decl_graph.py \\\n            --compare syntactic-decl-graph.json lean-decl-graph.json \\\n            | tee decl-graph-compare.txt\n          python3 scripts/proof_inventory.py --json exact-proof-inventory.json > /dev/null\n          python3 - <<'PY'\n          import json\n          inv = json.load(open('exact-proof-inventory.json'))\n          exact = json.load(open('lean-decl-graph.json'))\n          expected = len(inv['named_proofs']) if isinstance(inv.get('named_proofs'), list) else inv['declarations']['theorem'] + inv['declarations']['lemma']\n          actual = exact['stats']['named_proofs']\n          if expected != actual:\n              raise SystemExit(f'elaborated/source named-proof mismatch: source={expected}, elaborated={actual}')\n          print(f'Elaborated graph agrees with source inventory on {actual:,} named proofs.')\n          PY\n\n      - name: Upload exact declaration graph\n        if: steps.directbuild.outcome == 'success'\n        uses: actions/upload-artifact@v4\n        with:\n          name: exact-declaration-graph\n          path: |\n            lean-decl-graph.jsonl\n            lean-decl-graph.json\n            syntactic-decl-graph.json\n            decl-graph-compare.txt\n            exact-proof-inventory.json\n\n''',
)


# ---------------------------------------------------------------------------
# 7. Documentation and generated-artifact hygiene.
# ---------------------------------------------------------------------------

replace_once(
    ".gitignore",
    '''lean-decl-graph.jsonl\nproof-inventory.json\n''',
    '''lean-decl-graph.jsonl\nlean-decl-graph.json\nsyntactic-decl-graph.json\nexact-proof-inventory.json\ndecl-graph-compare.txt\nproof-inventory.json\n''',
)

replace_once(
    "docs/KNOWLEDGE_GRAPH.md",
    '''At 718 modules, 9,819 declarations and 6,616 named proofs, `grep` no longer\nfinds the structure that matters.  This directory's tooling treats the library\nas a mathematical knowledge graph instead.\n\nThere are four layers.  Each answers a different question, and it is worth being\n''',
    '''At hundreds of modules and thousands of declarations, `grep` no longer\nfinds the structure that matters.  The generated inventory is authoritative for\ncurrent counts; this directory's tooling treats the library as a mathematical\nknowledge graph instead.\n\nThere are six layers.  Each answers a different question, and it is worth being\n''',
)

replace_once(
    "docs/KNOWLEDGE_GRAPH.md",
    '''Layer 6 is the reduction DAG: an edge `X → Y` whenever a theorem proves `X`\nfrom `Y`.  Following it downward reaches the **open leaves** -- propositions\nnothing trades for anything simpler, which is where mathematics still has to\nhappen.  This is what collapses 6,616 proofs into a short list.\n''',
    '''Layer 6 is the proposition reduction graph: an edge `X → Y` whenever a\ncompiled theorem proves `X` from `Y`.  An unconditional exact `X ↔ Y` contributes\nboth directions.  Before leafhood is computed, strongly connected components are\ncollapsed, so coordinate equivalences do not create fake non-leaves.  Following\nthe condensed DAG downward reaches the **open leaves** -- the propositions where\nmathematics still has to happen.\n''',
)

replace_once(
    "docs/KNOWLEDGE_GRAPH.md",
    '''The exact graph needs a built project:\n\n```bash\nlake build\nlake env lean --run scripts/lean/DeclGraph.lean lean-decl-graph.jsonl\npython3 scripts/decl_graph.py --from-lean lean-decl-graph.jsonl --json decl-graph.json\n```\n''',
    '''The exact graph needs a built project:\n\n```bash\nlake build\nlake env lean --run scripts/lean/DeclGraph.lean lean-decl-graph.jsonl\npython3 scripts/decl_graph.py --from-lean lean-decl-graph.jsonl --json decl-graph.json --require-acyclic\n```\n\nThe hosted Lean workflow runs this extractor after every successful RHLean build,\ncompares it with the cheap syntactic graph, checks named-proof counts against the\nindependent inventory, and uploads the exact graph as an artifact.\n''',
)

# Remove stale hard-coded terminal-cone counts; the report is generated on every run.
sub_once(
    "docs/KNOWLEDGE_GRAPH.md",
    r'''`terminal-cone` reports something surprising the first time:\n\n```\ndeclarations in cone : 40 of 9,819\nnamed proofs in cone : 29 of 6,616\n```\n\nThat is correct, and it is the single most important structural fact about the\nrepository\.''',
    '''`terminal-cone` reports that only a small analytic consumer cone sits below\nthe terminal theorem; the exact counts are generated on every run rather than\nhard-coded here.  That separation is one of the most important structural facts\nabout the repository.''',
    flags=re.S,
)

# Self-delete the transport mechanism; only the actual fixes remain in history.
(ROOT / "scripts/apply_kg_review_fixes.py").unlink()
(ROOT / ".github/workflows/kg-review-fixup.yml").unlink()

print("Applied all PR #585 knowledge-graph review fixes.")
