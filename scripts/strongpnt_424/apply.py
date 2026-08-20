#!/usr/bin/env python3
"""Apply the minimal StrongPNT source compatibility fixes for Mathlib 4.24.

The upstream StrongPNT revision is pinned in lakefile.lean.  This script deliberately
uses exact source replacements: if that pinned source changes unexpectedly, the script
fails instead of guessing at a repair.
"""

from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
TARGET = ROOT / ".lake" / "packages" / "StrongPNT" / "StrongPNT" / "PNT1_ComplexAnalysis.lean"

PATCHES: tuple[tuple[str, str, str], ...] = (
    (
        "redundant ring after final-bound field_simp",
        """  have h_rearrange : (2 * M * r) / (R - r) = (2 * r / (R - r)) * M := by
    field_simp
    ring

  -- Apply the rearrangement
""",
        """  have h_rearrange : (2 * M * r) / (R - r) = (2 * r / (R - r)) * M := by
    field_simp

  -- Apply the rearrangement
""",
    ),
    (
        "complex coefficient cancellation after field_simp",
        """lemma complex_coeff_I_cancel : (1 : ℂ) / (2 * Real.pi * I) * I = 1 / (2 * Real.pi) := by
  field_simp [Complex.I_ne_zero, Real.pi_pos.ne']
  -- After field_simp, we have: I * (2 * ↑Real.pi) / (2 * ↑Real.pi * I) = 1
  exact mul_comm_div_cancel I (2 * ↑Real.pi) Complex.I_ne_zero (by norm_num; exact Real.pi_pos.ne')
""",
        """lemma complex_coeff_I_cancel : (1 : ℂ) / (2 * Real.pi * I) * I = 1 / (2 * Real.pi) := by
  field_simp [Complex.I_ne_zero, Real.pi_pos.ne']
  exact div_self Complex.I_ne_zero
""",
    ),
    (
        "redundant ring after integrand-bound field_simp",
        """    field_simp [ne_of_gt h_R_sub_r_pos, ne_of_gt (pow_pos h_r_sub_r_pos 2)]
    ring

  -- Apply transitivity
""",
        """    field_simp [ne_of_gt h_R_sub_r_pos, ne_of_gt (pow_pos h_r_sub_r_pos 2)]

  -- Apply transitivity
""",
    ),
    (
        "continuousOn_univ API rename",
        """  -- Convert ContinuousOn Set.univ to Continuous using the equivalence
  rwa [← continuous_iff_continuousOn_univ] at hcomp_on
""",
        """  -- Convert ContinuousOn Set.univ to Continuous using the 4.24 equivalence
  exact continuousOn_univ.mp hcomp_on
""",
    ),
)


def main() -> None:
    if not TARGET.is_file():
        raise SystemExit(f"StrongPNT source not found: {TARGET}")

    text = TARGET.read_text()
    changed = False

    for label, old, new in PATCHES:
        old_count = text.count(old)
        new_count = text.count(new)
        if old_count == 1:
            text = text.replace(old, new, 1)
            changed = True
            print(f"applied: {label}")
        elif old_count == 0 and new_count == 1:
            print(f"already applied: {label}")
        else:
            raise SystemExit(
                f"compatibility patch mismatch for {label!r}: "
                f"old_count={old_count}, new_count={new_count}"
            )

    if changed:
        TARGET.write_text(text)
        print(f"patched {TARGET}")
    else:
        print("StrongPNT 4.24 compatibility patch already present")


if __name__ == "__main__":
    main()
