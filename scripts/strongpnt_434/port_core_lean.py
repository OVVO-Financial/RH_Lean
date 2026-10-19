#!/usr/bin/env python3
"""Staged Lean 4.34 compatibility repairs for RHLean-owned proofs.

Patch only the two CI-proven Lean elaboration/API drift sites, maintaining the
identical theorem statements and mathematical assumptions. Edits occur in the
CI overlay; the original Lean 4.24 project remains untouched.
"""
import json
from pathlib import Path
ROOT = Path(__file__).resolve().parents[2]
PATCHES = [
  [
    "RHLean/Geometry/TwoABDisplacement.lean",
    "  exact add_le_add_left\n    (mul_le_mul_of_nonneg_right hh (sub_nonneg.mpr hcq))\n    (squareMapY c q)",
    "  exact add_le_add_right\n    (mul_le_mul_of_nonneg_right hh (sub_nonneg.mpr hcq))\n    (squareMapY c q)"
  ],
  [
    "RHLean/Proof/ActualForcingEstimates.lean",
    "‖actualBoundaryResonant data.boundary M‖ := by\n      exact add_le_add_right (norm_add_le _ _) _",
    "‖actualBoundaryResonant data.boundary M‖ := by\n      exact add_le_add_left\n        (norm_add_le\n          (actualLowHeightResonant data.lowHeight M)\n          (actualEndpointResonant data.endpoint M))\n        (‖actualBoundaryResonant data.boundary M‖)"
  ],
  [
    "RHLean/Proof/ActualForcingEstimates.lean",
    "‖actualBoundaryNonresonant data.boundary M‖ := by\n      exact add_le_add_right (norm_add_le _ _) _",
    "‖actualBoundaryNonresonant data.boundary M‖ := by\n      exact add_le_add_left\n        (norm_add_le\n          (actualLowHeightNonresonant data.lowHeight M)\n          (actualEndpointNonresonant data.endpoint M))\n        (‖actualBoundaryNonresonant data.boundary M‖)"
  ],
  [
    "RHLean/Analysis/SquarePrefixMertensBridge.lean",
    "add_le_add_left (norm_mertensSummatory_sub_le a x hax) _",
    "add_le_add_right (norm_mertensSummatory_sub_le a x hax) _"
  ],
  [
    "RHLean/Analysis/SquarePrefixMertensBridge.lean",
    "exact add_le_add_left hgap _",
    "exact add_le_add_right hgap _"
  ],
  [
    "RHLean/Analysis/SquarePrefixMertensBridge.lean",
    "add_le_add_right hendpoint _",
    "add_le_add_left hendpoint _"
  ],
  [
    "RHLean/Analysis/SquarePrefixMertensBridge.lean",
    "simpa only [Real.rpow_one] using",
    "simpa only [Real.rpow_eq_pow, Real.rpow_one] using"
  ]
]

def main():
    lock=json.loads((ROOT / "lake-manifest.json").read_text())
    pins={p["name"]:p["rev"] for p in lock["packages"]}
    assert pins["mathlib"]=="d13f23b723b8a846827a245b89c10fc7d3f11612"
    assert (ROOT / "lean-toolchain").read_text().strip()=="leanprover/lean4:v4.34.1"
    content={}
    for rel, old, new in PATCHES:
        path=ROOT / rel
        text=content.setdefault(str(path),path.read_text(encoding="utf-8"))
        if text.count(old)==1 and text.count(new)==0:
            content[str(path)] = text.replace(old,new,1)
        elif text.count(old)==0 and text.count(new)==1:
            print("already applied:",rel)
        else:
            raise RuntimeError(f"Unexpected project source for {rel} : {old[:65]}")
    for path, data in content.items():
        Path(path).write_text(data,encoding="utf-8")
        print("Applied source-exact v4.34 proof elaboration repair:",Path(path).relative_to(ROOT))
    print("No theorem statement or axiom changed.")

if __name__ == "__main__":
    main()
