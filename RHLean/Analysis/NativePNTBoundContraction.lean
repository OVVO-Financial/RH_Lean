import Mathlib
import RHLean.Analysis.NativePNTQuantitativeStatements

/-!
# Quantitative contraction retained from the native PNT proof

The native Selberg--Erdos proof already contains an explicit cubic contraction
of affine Chebyshev-error slopes.  This module keeps that quantitative content
visible after the Axer transfer instead of immediately collapsing it to the
qualitative statement `M(N) = o(N)`.

It also sharpens the cubic step in the small-slope regime.  The global proof
uses the convenient fixed choice `beta = alpha / 6`.  Once `alpha <= 3/2`, the
already-proved good-fibre deficit is proportional to `(alpha-beta) * beta^2`,
whose optimal admissible choice is `beta = 2*alpha/3`.  This improves the cubic
constant from `1/1123200000` to `1/175500000`, a factor of `32/5 = 6.4`, without
adding any analytic premise.

This is still not an RH-scale power estimate: the additive Axer constant depends
on the chosen PNT envelope.  Quantifying that dependence is the next bound-level
obligation if one wants to choose the contraction depth as a function of `N`.
-/

noncomputable section

namespace RHLean.Analysis

/-- Dividing the calibrated Axer estimate by `N log N` exposes the finite
normalized Mertens bound supplied by an affine Chebyshev envelope.  The leading
normalized coefficient is exactly `alpha`; all remaining loss is an explicit
`1 / log N` term. -/
theorem nativeMertens_abs_div_le_of_affineEnvelope
    (alpha : ℝ) (halpha : 0 ≤ alpha)
    (henv : nativePNTHasAffineEnvelope alpha) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ N : ℕ, 2 ≤ N →
      |nativeMertensSummatory N| / (N : ℝ) ≤
        alpha + (alpha + D + 2) / Real.log (N : ℝ) := by
  rcases nativeMertens_abs_mul_log_le_of_affineEnvelope
      alpha halpha henv with ⟨D, hD, hbound⟩
  refine ⟨D, hD, ?_⟩
  intro N hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have hlogpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  rw [div_le_iff₀ hNpos]
  apply (mul_le_mul_iff_right₀ hlogpos).mp
  calc
    |nativeMertensSummatory N| * Real.log (N : ℝ) ≤
        alpha * (N : ℝ) * (1 + Real.log (N : ℝ)) +
          (D + 2) * (N : ℝ) := hbound N hN
    _ = (alpha + (alpha + D + 2) / Real.log (N : ℝ)) *
          (N : ℝ) * Real.log (N : ℝ) := by
      field_simp [ne_of_gt hlogpos]
      ring

/-- Every certified PNT cubic iterate gives a strictly tighter finite normalized
Mertens coefficient. -/
theorem nativeMertens_abs_div_le_cubicSlope (k : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ N : ℕ, 2 ≤ N →
      |nativeMertensSummatory N| / (N : ℝ) ≤
        nativePNTCubicSlope k +
          (nativePNTCubicSlope k + D + 2) / Real.log (N : ℝ) := by
  exact nativeMertens_abs_div_le_of_affineEnvelope
    (nativePNTCubicSlope k)
    (nativePNTCubicSlope_spec k).1.le
    (nativePNTCubicSlope_spec k).2.2

/-- Finite iteration-budget form.  Any explicit `n` satisfying the existing
cubic budget certifies `eta` as the leading normalized Mertens coefficient. -/
theorem nativeMertens_abs_div_le_of_cubic_budget
    (eta : ℝ) (heta : 0 < eta) (n : ℕ)
    (hbudget :
      6 < nativePNTCubicConstant * (n : ℝ) * eta ^ 3) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ N : ℕ, 2 ≤ N →
      |nativeMertensSummatory N| / (N : ℝ) ≤
        eta + (eta + D + 2) / Real.log (N : ℝ) := by
  exact nativeMertens_abs_div_le_of_affineEnvelope eta heta.le
    (nativePNTHasAffineEnvelope_of_cubic_budget eta heta n hbudget)

/-- Improved cubic constant available once the affine PNT slope is at most
`3/2`. -/
def nativePNTLowSlopeCubicConstant : ℝ := 1 / 175500000

/-- The low-slope constant is exactly `32/5` times the globally calibrated one. -/
theorem nativePNTLowSlopeCubicConstant_eq_scaled :
    nativePNTLowSlopeCubicConstant =
      (32 / 5 : ℝ) * nativePNTCubicConstant := by
  norm_num [nativePNTLowSlopeCubicConstant, nativePNTCubicConstant]

/-- **Sharpened low-slope PNT contraction.**  For `0 < alpha <= 3/2`, choosing
`beta = 2*alpha/3` in the already-proved good-fibre compensation theorem
improves one affine-envelope step from `1/1123200000` to `1/175500000`.
No new analytic premise is introduced. -/
theorem nativePNTHasAffineEnvelope_lowSlope_cubic_step
    (alpha : ℝ) (halpha : 0 < alpha) (halphaSmall : alpha ≤ 3 / 2)
    (henv : nativePNTHasAffineEnvelope alpha) :
    nativePNTHasAffineEnvelope
      (alpha - nativePNTLowSlopeCubicConstant * alpha ^ 3) := by
  let beta : ℝ := 2 * alpha / 3
  have hbeta : 0 < beta := by
    dsimp [beta]
    positivity
  have hbeta0 : 0 ≤ beta := hbeta.le
  have hbeta1 : beta ≤ 1 := by
    dsimp [beta]
    nlinarith
  have hba : beta < alpha := by
    dsimp [beta]
    nlinarith
  let c : ℝ := beta ^ 2 / 6500000
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hprod : 0 ≤ beta * (1 - beta) :=
    mul_nonneg hbeta0 (sub_nonneg.mpr hbeta1)
  have hsq : beta ^ 2 ≤ 1 := by
    nlinarith
  have hc1 : c ≤ 1 := by
    dsimp [c]
    nlinarith
  have hgood : ∀ᶠ N : ℕ in Filter.atTop,
      c * (Real.log (N : ℝ)) ^ 2 ≤
        nativeLambdaTwoGoodRecipMass N beta := by
    simpa [c] using
      nativeLambdaTwoGoodRecipMass_eventually_quadratic_rate
        beta hbeta hbeta1
  have himp := nativePNTHasAffineEnvelope_improve_of_goodMass
    alpha beta c halpha hbeta0 hba hc hc1 hgood henv
  have hcoef :
      alpha - (alpha - beta) * c / 4 =
        alpha - nativePNTLowSlopeCubicConstant * alpha ^ 3 := by
    dsimp [beta, c, nativePNTLowSlopeCubicConstant]
    ring
  rw [hcoef] at himp
  exact himp

end RHLean.Analysis
