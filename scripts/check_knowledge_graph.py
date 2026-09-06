#!/usr/bin/env python3
"""Regression checks for the RHLean declaration/reduction knowledge graph.

These checks target the failure modes that make a research graph actively
misleading rather than merely incomplete: missed attributed declarations,
spurious dependency cycles, incorrect proof-status propagation, lost iff
bridges, and splitting conjunctive theorem premises into fake independent
implications.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import rhlean_kg as kg
from proofq import DEFAULT_RH_PROPOSITION, KnowledgeGraph


def require(cond: bool, message: str) -> None:
    if not cond:
        raise SystemExit(f"ERROR: {message}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("graph", type=Path, nargs="?", default=Path("decl-graph.json"))
    args = parser.parse_args()

    data = json.loads(args.graph.read_text(encoding="utf-8"))
    g = KnowledgeGraph(data)

    require(
        int(data.get("stats", {}).get("cyclic_components", 0)) == 0,
        "declaration dependency graph contains a cycle",
    )

    # Sentinels deliberately use declarations written as `@[simp] theorem ...`.
    # A lexical scanner can otherwise undercount both the inventory and graph in
    # the same way and make their agreement look like independent validation.
    attributed_sentinels = {
        "RHLean.Arithmetic.mem_primesUpTo",
        "RHLean.Analysis.nativeMertensRecip_zero",
    }
    missing = sorted(attributed_sentinels - set(g.nodes))
    require(not missing, f"same-line attributed declarations were lost: {missing}")

    # Every exact closed-proposition iff discovered by the status layer must
    # appear as two unary rules.  This is what keeps coordinate equivalences in
    # the reduction system instead of silently dropping them.
    iff_count = 0
    for theorem, entry in g.nodes.items():
        iff = list(entry.get("iff_props", ()))
        if len(iff) != 2:
            continue
        iff_count += 1
        a, b = iff
        require(
            ((b,), theorem) in g.reduction_rules.get(a, ()),
            f"missing iff reduction rule {a} <- {b} via {theorem}",
        )
        require(
            ((a,), theorem) in g.reduction_rules.get(b, ()),
            f"missing iff reduction rule {b} <- {a} via {theorem}",
        )
    require(iff_count > 0, "no closed-proposition iff rules were detected")

    # Conjunctive rules are real in this repository.  Their dependency
    # projection may expose each required premise for navigation, but none of
    # several unresolved premises may be promoted to a unary sufficient edge.
    multi = [
        (target, premises, via)
        for target, rules in g.reduction_rules.items()
        for premises, via in rules
        if len(premises) > 1
    ]
    require(multi, "expected at least one conjunctive proposition reduction rule")
    for target, premises, via in multi:
        for premise in premises:
            require(
                premise in g.reduction_graph[target],
                f"dependency projection lost {premise} from {target} via {via}",
            )
        unresolved = [p for p in premises if g.status(p) != kg.STATUS_PROVED]
        if len(unresolved) > 1:
            for premise in unresolved:
                require(
                    premise not in g.sufficient_graph[target],
                    f"conjunctive premise {premise} was falsely made sufficient for {target}",
                )

    # Two high-value status sentinels exercise opposite sides of the fixpoint:
    # an actually discharged closed proposition and a compiled refutation.
    forward = "RHLean.Proof.TerminalMertensReduction.MertensForwardCriterion"
    refuted = "RHLean.Analysis.LiteralSquarePrefixCollisionDefectQuotientStatement"
    require(g.status(forward) == kg.STATUS_PROVED, f"{forward} is not classified proved")
    require(g.status(refuted) == kg.STATUS_REFUTED, f"{refuted} is not classified refuted")

    require(DEFAULT_RH_PROPOSITION in g.closed_props, "RH root is not a closed proposition")
    leaf_components = g.open_leaf_components(DEFAULT_RH_PROPOSITION)
    require(leaf_components, "RH reduction system has no open leaf components")
    for comp in leaf_components:
        require(
            any(g.status(n) == kg.STATUS_OPEN for n in comp),
            f"reported leaf component has no open member: {comp}",
        )
        require(
            all(g.is_rh_relevant(n) for n in comp),
            f"reported RH leaf is outside the RH reduction cone: {comp}",
        )

    print("RHLean knowledge-graph regression checks passed")
    print(f"  declarations:              {len(g.nodes):,}")
    print(f"  named proofs:              {data['stats']['named_proofs']:,}")
    print(f"  closed-proposition iffs:   {iff_count:,}")
    print(f"  conjunctive reduction rules:{len(multi):,}")
    print(f"  RH open leaf components:   {len(leaf_components):,}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
