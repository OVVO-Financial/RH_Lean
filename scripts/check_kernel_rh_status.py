#!/usr/bin/env python3
"""Exact root RH census from the raw elaborated environment. Never infer RH
from a name, a Prop alias, a proof graph or the absence of custom axioms."""
import json
import sys
from pathlib import Path

def main():
    records = [json.loads(line) for line in Path(sys.argv[1]).read_text().splitlines() if line]
    if not records or any("kernelTypeAudit" not in r for r in records):
        raise SystemExit("Incomplete kernel type evidence")
    proofs = [r for r in records if r["kind"] in ("theorem","opaque","def","axiom")]
    returns = [r for r in proofs if r["kernelTypeAudit"]["returnsRH"]]
    exact = [r for r in returns if r["kernelTypeAudit"]["exactRH"]]
    print("KERNEL_RH_CENSUS "+json.dumps({
        "records":len(records),"direct_rh_returns":len(returns),
        "closed_exact_root_rh_candidates":[r["name"] for r in exact],
        "conditional_direct_rh_returns":[r["name"] for r in returns if r not in exact]
    },ensure_ascii=False))
    if exact:
        # The active repository has no registered unconditional RH proof.
        # A future candidate is a mandatory review stop, NOT a failure of Lean.
        # Replace this open-phase guard only in the final proof PR, with a
        # pinned exact root, its transitive axiom audit and signed source review.
        raise SystemExit("Exact root RH candidate: mandatory independent terminal proof review before changing the open-phase guard")
    print("No exact closed root RiemannHypothesis proof in the scanned environment; RH remains OPEN")
if __name__ == "__main__":
    main()
