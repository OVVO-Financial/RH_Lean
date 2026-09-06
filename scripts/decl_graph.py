#!/usr/bin/env python3
"""Build the RHLean declaration-level dependency graph.

`scripts/proof_inventory.py` gives the module import graph -- which file knows
about which file.  This script gives the finer graph the research actually
needs: which *declaration* references which declaration, separating references
that appear in a theorem's statement from those that appear only in its proof.

The output JSON is the schema `scripts/proofq.py` consumes.  The same schema is
emitted by `scripts/lean/DeclGraph.lean`, which reads the compiled environment
instead of the source text; pass either file to `proofq --graph`.

Usage:
    python3 scripts/decl_graph.py --json decl-graph.json --dot decl-graph.dot
"""

from __future__ import annotations

import argparse
import json
import re
from collections import Counter
from pathlib import Path

import rhlean_kg as kg

SCHEMA = "rhlean-decl-graph/1"
DOC_PREVIEW = 400
STATEMENT_PREVIEW = 320


def _preview(text: str, limit: int) -> str:
    flat = " ".join(text.split())
    if len(flat) <= limit:
        return flat
    return flat[: limit - 1] + "…"




# --------------------------------------------------------------------------
# Elaborated graph ingestion (scripts/lean/DeclGraph.lean)
# --------------------------------------------------------------------------

# Auxiliary constants the elaborator generates.  They are real environment
# entries but they are not declarations anybody wrote, so including them would
# bury the mathematics under machinery.
_INTERNAL_SUFFIXES = (
    ".rec", ".recOn", ".casesOn", ".brecOn", ".below", ".ibelow", ".binductionOn",
    ".noConfusion", ".noConfusionType", ".injEq", ".inj", ".sizeOf_spec",
    ".eq_def", ".sunfold", ".mk.injEq", ".ofNat", ".toCtorIdx",
)
_INTERNAL_PART_RE = re.compile(
    r"(^|\.)(_cstage\d+|_spec_\d+|_unsafe_rec|_sunfold|match_\d+|proof_\d+"
    r"|_proof_\d+|eq_\d+|_eq_\d+|_simp_\d+|_regBuiltin.*|_auxLemma.*)(\.|$)"
)


def is_internal_lean_name(name: str) -> bool:
    """Is this an elaborator-generated auxiliary rather than a written declaration?"""

    if name.endswith(_INTERNAL_SUFFIXES):
        return True
    return bool(_INTERNAL_PART_RE.search(name))


def demangle_private(name: str, module: str) -> tuple[str, bool]:
    """Translate Lean's private mangling into this schema's id convention.

    Lean names a private declaration `_private.<module>.<n>.<user name>`.  This
    returns `(<user name>#<module>, True)` for such a name, matching
    `Declaration.decl_id`, and `(name, False)` otherwise.
    """

    prefix = f"_private.{module}."
    if not name.startswith(prefix):
        return name, False
    rest = name[len(prefix) :]
    head, _, tail = rest.partition(".")
    user = tail if head.isdigit() and tail else rest
    return f"{user}#{module}", True


def _module_of(name: str, module_by_name: dict[str, str]) -> str | None:
    return module_by_name.get(name)


def build_graph_from_lean(jsonl: Path, include_docs: bool = True) -> dict[str, object]:
    """Build the schema from the elaborated environment dump.

    Edges come from the compiled environment.  Source locations, doc comments,
    statement previews and normalized signatures are not in the environment
    dump, so they are merged in from the source parse where the declaration can
    be matched by name; declarations that only exist after elaboration simply
    lack them.
    """

    records: list[dict] = []
    module_by_name: dict[str, str] = {}
    with jsonl.open(encoding="utf-8") as fh:
        for line in fh:
            line = line.strip()
            if not line:
                continue
            rec = json.loads(line)
            if is_internal_lean_name(rec["name"]):
                continue
            records.append(rec)
            module_by_name[rec["name"]] = rec["module"]

    def to_id(raw: str) -> str:
        mod = module_by_name.get(raw)
        if mod is None:
            return raw
        return demangle_private(raw, mod)[0]

    # Source-side metadata, keyed by the same ids.
    src_decls, table = kg.build_declarations()
    meta = {d.decl_id: (d, kg.normalized_signature_parts(d, table)) for d in src_decls}

    nodes: dict[str, dict[str, object]] = {}
    for rec in records:
        node_id, is_private = demangle_private(rec["name"], rec["module"])
        stmt_refs = sorted({to_id(r) for r in rec["typeRefs"]} - {node_id})
        proof_refs = sorted({to_id(r) for r in rec["valueRefs"]} - {node_id})
        entry: dict[str, object] = {
            "kind": rec["kind"],
            "name": node_id.split("#", 1)[0],
            "private": is_private,
            "module": rec["module"],
            "statement_refs": stmt_refs,
            "proof_refs": proof_refs,
            "external_statement_refs": rec.get("externalTypeRefs", 0),
            "external_proof_refs": rec.get("externalValueRefs", 0),
        }
        found = meta.get(node_id)
        if found is not None:
            decl, (signature, sig_constants) = found
            entry["path"] = decl.path
            entry["line"] = decl.line
            entry["namespace"] = decl.namespace
            entry["signature"] = signature
            entry["signature_constants"] = sig_constants
            entry["shape"] = kg.statement_shape(decl.statement)
            entry["shape_full"] = kg.statement_shape(decl.statement, conclusion_only=False)
            entry["statement_preview"] = _preview(decl.statement, STATEMENT_PREVIEW)
            if include_docs and decl.doc:
                entry["doc"] = _preview(decl.doc, DOC_PREVIEW)
        nodes[node_id] = entry

    return _finalize(
        nodes,
        source="elaborated",
        producer="scripts/lean/DeclGraph.lean + scripts/decl_graph.py --from-lean",
        authority=(
            "Exact declaration dependency graph read from the compiled environment. "
            "Edges are the constants the kernel records in each declaration's type "
            "and proof term. This is authoritative per AGENTS.md."
        ),
    )


def compare_graphs(syntactic: Path, elaborated: Path) -> int:
    """Report how much of the exact graph the cheap syntactic graph recovers."""

    a = json.loads(syntactic.read_text(encoding="utf-8"))
    b = json.loads(elaborated.read_text(encoding="utf-8"))

    def edge_set(graph: dict) -> set[tuple[str, str]]:
        out: set[tuple[str, str]] = set()
        for name, entry in graph["declarations"].items():
            for dep in set(entry["statement_refs"]) | set(entry["proof_refs"]):
                out.add((name, dep))
        return out

    ea, eb = edge_set(a), edge_set(b)
    na = set(a["declarations"])
    nb = set(b["declarations"])
    shared_nodes = na & nb
    # Only judge edges whose endpoints both graphs know about.
    ea_c = {e for e in ea if e[0] in shared_nodes and e[1] in shared_nodes}
    eb_c = {e for e in eb if e[0] in shared_nodes and e[1] in shared_nodes}
    tp = len(ea_c & eb_c)

    print("Syntactic vs elaborated declaration graph")
    print("=========================================")
    print(f"syntactic nodes:  {len(na):,}")
    print(f"elaborated nodes: {len(nb):,}")
    print(f"shared nodes:     {len(shared_nodes):,}")
    print(f"syntactic-only nodes:  {len(na - nb):,}")
    print(f"elaborated-only nodes: {len(nb - na):,}")
    print()
    print(f"comparable syntactic edges:  {len(ea_c):,}")
    print(f"comparable elaborated edges: {len(eb_c):,}")
    print(f"edges in both:               {tp:,}")
    if ea_c:
        print(f"syntactic precision:         {tp / len(ea_c):.3f}")
    if eb_c:
        print(f"syntactic recall:            {tp / len(eb_c):.3f}")
    print()
    print("A syntactic edge missing from the elaborated graph is a false positive")
    print("(usually a local name shadowing a global one). An elaborated edge missing")
    print("from the syntactic graph was introduced by elaboration and is invisible")
    print("to source text. Use the elaborated graph for any claim about dependence.")
    return 0


def build_graph(include_docs: bool = True) -> dict[str, object]:
    """Build the syntactic graph directly from the Lean sources."""

    decls, table = kg.build_declarations()

    nodes: dict[str, dict[str, object]] = {}
    for decl in decls:
        entry: dict[str, object] = {
            "kind": decl.kind,
            "name": decl.name,
            "private": decl.is_private,
            "module": decl.module,
            "path": decl.path,
            "line": decl.line,
            "namespace": decl.namespace,
            "statement_refs": decl.statement_refs,
            "proof_refs": decl.proof_refs,
            "signature": kg.normalized_signature_parts(decl, table)[0],
            "signature_constants": kg.normalized_signature_parts(decl, table)[1],
            "shape": kg.statement_shape(decl.statement),
            "shape_full": kg.statement_shape(decl.statement, conclusion_only=False),
            "statement_preview": _preview(decl.statement, STATEMENT_PREVIEW),
        }
        if include_docs and decl.doc:
            entry["doc"] = _preview(decl.doc, DOC_PREVIEW)
        nodes[decl.decl_id] = entry

    return _finalize(
        nodes,
        source="syntactic",
        producer="scripts/decl_graph.py",
        authority=(
            "Syntactic name-reference graph over RHLean/**.lean. It records that one "
            "declaration's text mentions another's name. It cannot see dependencies "
            "introduced by elaboration (instances, notation, `simp` without explicit "
            "lemmas, dot-notation), and can over-report when a local name shadows a "
            "global one. scripts/lean/DeclGraph.lean emits the exact elaborated graph "
            "in this schema and is authoritative where the two differ."
        ),
    )


def _finalize(
    nodes: dict[str, dict[str, object]],
    *,
    source: str,
    producer: str,
    authority: str,
) -> dict[str, object]:
    """Attach degree counts, statistics and duplicate-signature groups."""

    combined = {
        name: sorted(set(e["statement_refs"]) | set(e["proof_refs"]))  # type: ignore[arg-type]
        for name, e in nodes.items()
    }
    rev = kg.invert(combined)
    for name, entry in nodes.items():
        entry["used_by_count"] = len(rev.get(name, ()))
        entry["uses_count"] = len(combined[name])

    kinds = Counter(str(e["kind"]) for e in nodes.values())
    statement_edges = sum(len(e["statement_refs"]) for e in nodes.values())  # type: ignore[arg-type]
    proof_edges = sum(len(e["proof_refs"]) for e in nodes.values())  # type: ignore[arg-type]

    signatures: dict[str, list[str]] = {}
    for name, entry in nodes.items():
        sig = entry.get("signature")
        # A statement mentioning fewer than two repository constants has almost
        # no skeleton left after normalization, so such signatures collide
        # trivially (`_ = _` over Mathlib-only terms) and are not evidence of a
        # duplicate.
        if sig and entry["kind"] in kg.PROOF_KINDS and int(entry.get("signature_constants", 0)) >= 2:
            signatures.setdefault(str(sig), []).append(name)
    duplicate_signatures = {
        sig: sorted(names) for sig, names in signatures.items() if len(names) > 1
    }

    isolated = sorted(n for n in nodes if not combined[n] and not rev.get(n))

    return {
        "schema": SCHEMA,
        "provenance": {"source": source, "producer": producer, "authority": authority},
        "stats": {
            "declarations": len(nodes),
            "named_proofs": kinds["theorem"] + kinds["lemma"],
            "kinds": dict(sorted(kinds.items())),
            "statement_edges": statement_edges,
            "proof_edges": proof_edges,
            "distinct_edges": sum(len(v) for v in combined.values()),
            "isolated_declarations": len(isolated),
            "duplicate_signature_groups": len(duplicate_signatures),
            "declarations_in_duplicate_groups": sum(
                len(v) for v in duplicate_signatures.values()
            ),
        },
        "duplicate_signatures": duplicate_signatures,
        "declarations": nodes,
    }


def write_dot(path: Path, graph: dict[str, object], limit: int) -> None:
    """Emit the most-referenced subgraph; the full graph is far too dense to draw."""

    nodes: dict[str, dict] = graph["declarations"]  # type: ignore[assignment]
    ranked = sorted(
        nodes.items(), key=lambda kv: (-int(kv[1]["used_by_count"]), kv[0])
    )[:limit]
    keep = {name for name, _ in ranked}
    lines = ["digraph RHLeanDecls {", "  rankdir=LR;", "  node [shape=box, fontsize=9];"]
    for name in sorted(keep):
        entry = nodes[name]
        short = name.rsplit(".", 1)[-1]
        lines.append(f'  "{name}" [label="{short}\\n{entry["used_by_count"]} users"];')
    for name in sorted(keep):
        entry = nodes[name]
        for dep in sorted(set(entry["statement_refs"]) | set(entry["proof_refs"])):
            if dep in keep:
                lines.append(f'  "{name}" -> "{dep}";')
    lines.append("}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def print_summary(graph: dict[str, object]) -> None:
    stats = graph["stats"]  # type: ignore[index]
    nodes: dict[str, dict] = graph["declarations"]  # type: ignore[assignment]
    print("RHLean declaration dependency graph")
    print("===================================")
    print(f"Source:                              {graph['provenance']['source']}")
    print(f"Declarations:                        {stats['declarations']:,}")
    print(f"Named proofs (theorem + lemma):      {stats['named_proofs']:,}")
    print(f"Statement edges:                     {stats['statement_edges']:,}")
    print(f"Proof edges:                         {stats['proof_edges']:,}")
    print(f"Distinct declaration edges:          {stats['distinct_edges']:,}")
    print(f"Isolated declarations:               {stats['isolated_declarations']:,}")
    print(f"Duplicate statement-signature groups:{stats['duplicate_signature_groups']:,}")
    print()
    print("Most-referenced declarations")
    print("----------------------------")
    ranked = sorted(
        nodes.items(), key=lambda kv: (-int(kv[1]["used_by_count"]), kv[0])
    )[:15]
    for name, entry in ranked:
        print(f"{entry['used_by_count']:5d}  {entry['kind']:9s} {name}")


def main() -> int:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("--json", type=Path, help="write the declaration graph JSON")
    parser.add_argument(
        "--from-lean",
        type=Path,
        metavar="JSONL",
        help="build from scripts/lean/DeclGraph.lean output instead of source text",
    )
    parser.add_argument(
        "--compare",
        nargs=2,
        type=Path,
        metavar=("SYNTACTIC", "ELABORATED"),
        help="report syntactic-graph precision and recall against the exact graph",
    )
    parser.add_argument("--dot", type=Path, help="write a DOT hub subgraph")
    parser.add_argument(
        "--dot-limit", type=int, default=120, help="declarations to include in the DOT"
    )
    parser.add_argument("--no-docs", action="store_true", help="omit doc comments from JSON")
    parser.add_argument("--no-summary", action="store_true")
    args = parser.parse_args()

    if args.compare:
        return compare_graphs(args.compare[0], args.compare[1])

    if args.from_lean:
        graph = build_graph_from_lean(args.from_lean, include_docs=not args.no_docs)
    else:
        graph = build_graph(include_docs=not args.no_docs)
    if not args.no_summary:
        print_summary(graph)
    if args.json:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(
            json.dumps(graph, indent=1, sort_keys=True, ensure_ascii=False) + "\n",
            encoding="utf-8",
        )
    if args.dot:
        write_dot(args.dot, graph, args.dot_limit)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
