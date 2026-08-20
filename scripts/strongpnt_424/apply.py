#!/usr/bin/env python3
"""Apply the minimal StrongPNT source compatibility fixes for Mathlib 4.24.

The upstream StrongPNT revision is pinned in lakefile.lean. This script deliberately
uses exact source replacements: if that pinned source changes unexpectedly, the script
fails instead of guessing at a repair.
"""

from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
STRONGPNT = ROOT / ".lake" / "packages" / "StrongPNT" / "StrongPNT"

Patch = tuple[str, str, str]

PNT1_PATCHES: tuple[Patch, ...] = (
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

PNT2_PATCHES: tuple[Patch, ...] = (
    (
        "numerator rewrite now closed by field_simp",
        """      field_simp [ne_of_gt hR1_pos]
      ring_nf
      field_simp
      ring_nf
      norm_cast
      rw [pow_two]
      rw [mul_assoc R R R⁻¹]
      -- rw [(mul_inv_cancel R)]
      have : R * R⁻¹ = 1 := by
        have : R > 0 := by linarith
        -- apply mul_inv_cancel
        field_simp
      rw [this]
      simp
""",
        """      field_simp [ne_of_gt hR1_pos]
""",
    ),
    (
        "remove no-progress second field_simp on boundary norm",
        """    rw [factor_eq, Complex.norm_mul, norm_star, ←hz]
    field_simp
    field_simp [hz, z_ne_rho]

    have h_denom_ne_zero : R * ‖z - ρ‖ ≠ 0 := by
""",
        """    rw [factor_eq, Complex.norm_mul, norm_star, ←hz]
    field_simp

    have h_denom_ne_zero : R * ‖z - ρ‖ ≠ 0 := by
""",
    ),
    (
        "normalize positive real denominator before field_simp",
        """    rw [factor_eq, Complex.norm_mul, norm_star, ←hz]
    field_simp

    have h_denom_ne_zero : R * ‖z - ρ‖ ≠ 0 := by
      apply mul_ne_zero
      -- Prove R is not zero
      · linarith [hR1_pos, hR1_lt_R]
      -- Prove the norm is not zero
      · simp [norm_ne_zero_iff, sub_ne_zero, z_ne_rho]
    -- field_simp can now use this fact to solve the goal.
    field_simp [h_denom_ne_zero]
""",
        """    rw [factor_eq, Complex.norm_mul, norm_star, ←hz]
    have hR_pos : 0 < R := lt_trans hR1_pos hR1_lt_R
    have hnorm_ne_zero : ‖z - ρ‖ ≠ 0 :=
      norm_ne_zero_iff.mpr (sub_ne_zero.mpr z_ne_rho)
    have hz_norm_ne_zero : ‖z‖ ≠ 0 := by
      rw [hz]
      exact hR_pos.ne'
    rw [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg z)]
    field_simp [hz_norm_ne_zero, hnorm_ne_zero]
""",
    ),
)

PNT3_PATCHES: tuple[Patch, ...] = (
    (
        "explicit unconditional filter for imaginary part of real tsum",
        """lemma im_tsum_ofReal (g : ℕ → ℝ) : (∑' n : ℕ, (g n : ℂ)).im = 0 := by
  have him := congrArg Complex.im (Complex.ofReal_tsum (f := g)).symm
""",
        """lemma im_tsum_ofReal (g : ℕ → ℝ) : (∑' n : ℕ, (g n : ℂ)).im = 0 := by
  have him := congrArg Complex.im
    (Complex.ofReal_tsum (L := SummationFilter.unconditional ℕ) (f := g)).symm
""",
    ),
    (
        "explicit unconditional filter for real part of real tsum",
        """lemma re_tsum_ofReal (g : ℕ → ℝ) : (∑' n : ℕ, (g n : ℂ)).re = ∑' n : ℕ, g n := by
  have h := congrArg Complex.re (Complex.ofReal_tsum (f := g)).symm
""",
        """lemma re_tsum_ofReal (g : ℕ → ℝ) : (∑' n : ℕ, (g n : ℂ)).re = ∑' n : ℕ, g n := by
  have h := congrArg Complex.re
    (Complex.ofReal_tsum (L := SummationFilter.unconditional ℕ) (f := g)).symm
""",
    ),
    (
        "real absolute-value triangle inequality rename",
        """  have h3 : |s.im + t| ≤ |s.im| + |t| := abs_add s.im t
""",
        """  have h3 : |s.im + t| ≤ |s.im| + |t| := abs_add_le s.im t
""",
    ),
    (
        "redundant ring after positive quotient field_simp",
        """          have h_sq_div : R^2/R1 = R * (R/R1) := by
            field_simp [ne_of_gt hR1_pos]
            ring
          rw [h_sq_div]
""",
        """          have h_sq_div : R^2/R1 = R * (R/R1) := by
            field_simp [ne_of_gt hR1_pos]
          rw [h_sq_div]
""",
    ),
)

PNT5_PATCHES: tuple[Patch, ...] = (
    (
        "continuousOn_univ direction in smooth Mellin continuity",
        """  have cont_mellin_smooth : Continuous fun (a : ℝ) ↦
      𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑a * I) := by
    rw [continuous_iff_continuousOn_univ]
""",
        """  have cont_mellin_smooth : Continuous fun (a : ℝ) ↦
      𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑a * I) := by
    rw [← continuousOn_univ]
""",
    ),
)

FILE_PATCHES: tuple[tuple[str, tuple[Patch, ...]], ...] = (
    ("PNT1_ComplexAnalysis.lean", PNT1_PATCHES),
    ("PNT2_LogDerivative.lean", PNT2_PATCHES),
    ("PNT3_RiemannZeta.lean", PNT3_PATCHES),
    ("PNT5_Strong.lean", PNT5_PATCHES),
)


def patch_file(filename: str, patches: tuple[Patch, ...]) -> bool:
    target = STRONGPNT / filename
    if not target.is_file():
        raise SystemExit(f"StrongPNT source not found: {target}")

    text = target.read_text()
    changed = False

    for label, old, new in patches:
        old_count = text.count(old)
        new_count = text.count(new)
        if old_count == 1:
            text = text.replace(old, new, 1)
            changed = True
            print(f"applied {filename}: {label}")
        elif old_count == 0 and new_count == 1:
            print(f"already applied {filename}: {label}")
        else:
            raise SystemExit(
                f"compatibility patch mismatch in {filename} for {label!r}: "
                f"old_count={old_count}, new_count={new_count}"
            )

    if changed:
        target.write_text(text)
        print(f"patched {target}")
    return changed


def main() -> None:
    changed = False
    for filename, patches in FILE_PATCHES:
        changed = patch_file(filename, patches) or changed
    if not changed:
        print("StrongPNT 4.24 compatibility patch already present")


if __name__ == "__main__":
    main()
