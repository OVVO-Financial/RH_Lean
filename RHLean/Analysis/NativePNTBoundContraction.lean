import Mathlib
import RHLean.Analysis.NativePNTQuantitativeStatements
import RHLean.Analysis.NativePNTSquarePrefixCubic

/-!
# Quantitative contraction retained from the native PNT proof

The native Selberg--Erdos proof already contains an explicit cubic contraction
of affine Chebyshev-error slopes.  This module keeps that quantitative content
visible after the Axer transfer instead of immediately collapsing it to the
qualitative statement `M(N) = o(N)`.

There are two quantitative gains recorded here.

First, dividing the Axer estimate by `N log N` preserves the contracted PNT
slope as the leading coefficient in a finite normalized Mertens bound.

Second, the exact cubic recurrence is stronger than the previously recorded
finite estimate `C * n * alpha_n^3 <= 6`.  Positivity of the exact next slope
implies that one step increases `1 / alpha_n^2` by at least `2C`.  Telescoping
therefore gives an iteration budget of order `eta^(-2)`, rather than the older
`eta^(-3)` budget extracted from a monotonicity-only cubic estimate.

The module also sharpens the one-step cubic coefficient in the small-slope
regime.  The global proof uses the convenient fixed choice `beta = alpha / 6`.
Once `alpha <= 3/2`, the already-proved good-fibre deficit is proportional to
`(alpha-beta) * beta^2`, whose optimal admissible choice is `beta = 2*alpha/3`.
This improves the legacy cubic constant from `1/1123200000` to `1/175500000`, a
factor of `32/5 = 6.4`, without adding any analytic premise.

These are still not RH-scale power estimates: the additive Axer constant depends
on the chosen PNT envelope.  Quantifying that dependence is the next bound-level
obligation if one wants to choose the contraction depth as a function of `N`.
-/

noncomputable section

namespace RHLean.Analysis

/-! ## Exact reciprocal-square contraction for a cubic step -/

/-- An exact positive cubic step grows the reciprocal square by at least `2C`.
This elementary inequality is the quantitative fact lost by the older generic
`C * n * alpha_n^3` estimate. -/
theorem inv_sq_add_two_mul_le_inv_sq_cubic_step
    (a C : ℝ) (ha : 0 < a) (hC : 0 ≤ C)
    (hnext : 0 < a - C * a ^ 3) :
    1 / a ^ 2 + 2 * C ≤ 1 / (a - C * a ^ 3) ^ 2 := by
  have hfactorEq :
      a - C * a ^ 3 = a * (1 - C * a ^ 2) := by
    ring
  have hfactor : 0 < 1 - C * a ^ 2 := by
    rw [hfactorEq] at hnext
    rcases (mul_pos_iff.mp hnext) with hpos | hneg
    · exact hpos.2
    · exfalso
      exact (not_lt_of_ge ha.le) hneg.1
  have hx0 : 0 ≤ C * a ^ 2 :=
    mul_nonneg hC (sq_nonneg a)
  have hx1 : C * a ^ 2 ≤ 1 := by linarith
  have hnextSq : 0 < (a - C * a ^ 3) ^ 2 :=
    sq_pos_of_pos hnext
  apply (le_div_iff₀ hnextSq).2
  have ha0 : a ≠ 0 := ne_of_gt ha
  have heq :
      (1 / a ^ 2 + 2 * C) * (a - C * a ^ 3) ^ 2 =
        (1 + 2 * (C * a ^ 2)) * (1 - C * a ^ 2) ^ 2 := by
    rw [hfactorEq]
    field_simp [ha0]
    ring
  rw [heq]
  let x : ℝ := C * a ^ 2
  change (1 + 2 * x) * (1 - x) ^ 2 ≤ 1
  have hx0' : 0 ≤ x := by simpa [x] using hx0
  have hx1' : x ≤ 1 := by simpa [x] using hx1
  have hrem : 0 ≤ x ^ 2 * (3 - 2 * x) :=
    mul_nonneg (sq_nonneg x) (by linarith)
  nlinarith

/-- Any exact positive cubic recurrence has linear reciprocal-square growth. -/
theorem inv_sq_rate_of_exact_cubic_recurrence
    (a : ℕ → ℝ) (C : ℝ)
    (hC : 0 ≤ C)
    (hpos : ∀ n, 0 < a n)
    (hrec : ∀ n, a (n + 1) = a n - C * (a n) ^ 3) :
    ∀ n : ℕ,
      1 / (a 0) ^ 2 + 2 * C * (n : ℝ) ≤ 1 / (a n) ^ 2 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hnext : 0 < a n - C * (a n) ^ 3 := by
        rw [← hrec n]
        exact hpos (n + 1)
      have hstep := inv_sq_add_two_mul_le_inv_sq_cubic_step
        (a n) C (hpos n) hC hnext
      calc
        1 / (a 0) ^ 2 + 2 * C * ((n + 1 : ℕ) : ℝ) =
            (1 / (a 0) ^ 2 + 2 * C * (n : ℝ)) + 2 * C := by
          push_cast
          ring
        _ ≤ 1 / (a n) ^ 2 + 2 * C := add_le_add_right ih _
        _ ≤ 1 / (a (n + 1)) ^ 2 := by
          simpa [hrec n] using hstep

/-! ## Keep the PNT contraction after the Axer transfer -/

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

/-- The legacy exact cubic sequence satisfies the sharper reciprocal-square
finite rate. -/
theorem nativePNTCubicSlope_inv_sq_rate (n : ℕ) :
    (1 : ℝ) / 36 + 2 * nativePNTCubicConstant * (n : ℝ) ≤
      1 / (nativePNTCubicSlope n) ^ 2 := by
  have h := inv_sq_rate_of_exact_cubic_recurrence
    nativePNTCubicSlope nativePNTCubicConstant
    (by norm_num [nativePNTCubicConstant])
    (fun m => (nativePNTCubicSlope_spec m).1)
    (fun m => nativePNTCubicSlope_succ m) n
  simpa [nativePNTCubicSlope_zero] using h

/-- Equivalent direct form of the sharper finite rate:
`2 C n alpha_n^2 <= 1`. -/
theorem nativePNTCubicSlope_quadratic_rate (n : ℕ) :
    2 * nativePNTCubicConstant * (n : ℝ) *
        (nativePNTCubicSlope n) ^ 2 ≤ 1 := by
  have hinv := nativePNTCubicSlope_inv_sq_rate n
  have hbase : 0 ≤ (1 : ℝ) / 36 := by norm_num
  have hdrop :
      2 * nativePNTCubicConstant * (n : ℝ) ≤
        1 / (nativePNTCubicSlope n) ^ 2 := by
    linarith
  have hslope : 0 < nativePNTCubicSlope n :=
    (nativePNTCubicSlope_spec n).1
  have hmul := mul_le_mul_of_nonneg_right hdrop
    (sq_nonneg (nativePNTCubicSlope n))
  calc
    2 * nativePNTCubicConstant * (n : ℝ) *
          (nativePNTCubicSlope n) ^ 2 ≤
        (1 / (nativePNTCubicSlope n) ^ 2) *
          (nativePNTCubicSlope n) ^ 2 := by
      simpa [mul_assoc] using hmul
    _ = 1 := by
      field_simp [ne_of_gt hslope]

/-- **Quadratic iteration budget.**  The same exact PNT cubic recurrence reaches
slope `eta` after a budget of order `eta^(-2)`.  This strictly strengthens the
older `eta^(-3)` budget theorem. -/
theorem nativePNTHasAffineEnvelope_of_quadratic_budget
    (eta : ℝ) (heta : 0 < eta) (n : ℕ)
    (hbudget :
      1 < 2 * nativePNTCubicConstant * (n : ℝ) * eta ^ 2) :
    nativePNTHasAffineEnvelope eta := by
  have hspec := nativePNTCubicSlope_spec n
  have hrate := nativePNTCubicSlope_quadratic_rate n
  have hslopeEta : nativePNTCubicSlope n ≤ eta := by
    by_contra hnot
    have hetaSlope : eta < nativePNTCubicSlope n := lt_of_not_ge hnot
    have hsq : eta ^ 2 ≤ (nativePNTCubicSlope n) ^ 2 :=
      pow_le_pow_left₀ heta.le hetaSlope.le 2
    have hcoef0 :
        0 ≤ 2 * nativePNTCubicConstant * (n : ℝ) := by
      positivity
    have hmul :
        2 * nativePNTCubicConstant * (n : ℝ) * eta ^ 2 ≤
          2 * nativePNTCubicConstant * (n : ℝ) *
            (nativePNTCubicSlope n) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hcoef0
    have hone :
        1 < 2 * nativePNTCubicConstant * (n : ℝ) *
          (nativePNTCubicSlope n) ^ 2 := hbudget.trans_le hmul
    linarith
  exact nativePNTHasAffineEnvelope_mono hslopeEta hspec.2.2

/-- The normalized Mertens bound now inherits the sharper `eta^(-2)` PNT
iteration budget directly. -/
theorem nativeMertens_abs_div_le_of_quadratic_budget
    (eta : ℝ) (heta : 0 < eta) (n : ℕ)
    (hbudget :
      1 < 2 * nativePNTCubicConstant * (n : ℝ) * eta ^ 2) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ N : ℕ, 2 ≤ N →
      |nativeMertensSummatory N| / (N : ℝ) ≤
        eta + (eta + D + 2) / Real.log (N : ℝ) := by
  exact nativeMertens_abs_div_le_of_affineEnvelope eta heta.le
    (nativePNTHasAffineEnvelope_of_quadratic_budget eta heta n hbudget)

/-- The older cubic-budget interface is retained for comparison and backwards
compatibility. -/
theorem nativeMertens_abs_div_le_of_cubic_budget
    (eta : ℝ) (heta : 0 < eta) (n : ℕ)
    (hbudget :
      6 < nativePNTCubicConstant * (n : ℝ) * eta ^ 3) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ N : ℕ, 2 ≤ N →
      |nativeMertensSummatory N| / (N : ℝ) ≤
        eta + (eta + D + 2) / Real.log (N : ℝ) := by
  exact nativeMertens_abs_div_le_of_affineEnvelope eta heta.le
    (nativePNTHasAffineEnvelope_of_cubic_budget eta heta n hbudget)

/-! ## The same sharper rate on the fully rederived square-prefix PNT path -/

/-- The independent square-prefix cubic sequence has the same reciprocal-square
finite rate. -/
theorem nativePNTSquarePrefixRederivedCubicSlope_inv_sq_rate (n : ℕ) :
    (1 : ℝ) / 36 +
        2 * nativePNTSquarePrefixRederivedCubicConstant * (n : ℝ) ≤
      1 / (nativePNTSquarePrefixRederivedCubicSlope n) ^ 2 := by
  have h := inv_sq_rate_of_exact_cubic_recurrence
    nativePNTSquarePrefixRederivedCubicSlope
    nativePNTSquarePrefixRederivedCubicConstant
    (by norm_num [nativePNTSquarePrefixRederivedCubicConstant])
    (fun m => (nativePNTSquarePrefixRederivedCubicSlope_spec m).1)
    (fun m => nativePNTSquarePrefixRederivedCubicSlope_succ m) n
  simpa [nativePNTSquarePrefixRederivedCubicSlope_zero] using h

/-- Direct square-prefix rate: `2 C n alpha_n^2 <= 1`. -/
theorem nativePNTSquarePrefixRederivedCubicSlope_quadratic_rate (n : ℕ) :
    2 * nativePNTSquarePrefixRederivedCubicConstant * (n : ℝ) *
        (nativePNTSquarePrefixRederivedCubicSlope n) ^ 2 ≤ 1 := by
  have hinv := nativePNTSquarePrefixRederivedCubicSlope_inv_sq_rate n
  have hdrop :
      2 * nativePNTSquarePrefixRederivedCubicConstant * (n : ℝ) ≤
        1 / (nativePNTSquarePrefixRederivedCubicSlope n) ^ 2 := by
    have hbase : 0 ≤ (1 : ℝ) / 36 := by norm_num
    linarith
  have hslope : 0 < nativePNTSquarePrefixRederivedCubicSlope n :=
    (nativePNTSquarePrefixRederivedCubicSlope_spec n).1
  have hmul := mul_le_mul_of_nonneg_right hdrop
    (sq_nonneg (nativePNTSquarePrefixRederivedCubicSlope n))
  calc
    2 * nativePNTSquarePrefixRederivedCubicConstant * (n : ℝ) *
          (nativePNTSquarePrefixRederivedCubicSlope n) ^ 2 ≤
        (1 / (nativePNTSquarePrefixRederivedCubicSlope n) ^ 2) *
          (nativePNTSquarePrefixRederivedCubicSlope n) ^ 2 := by
      simpa [mul_assoc] using hmul
    _ = 1 := by
      field_simp [ne_of_gt hslope]

/-- **Square-prefix quadratic iteration budget.**  The fully rederived
square-prefix PNT path also reaches slope `eta` with an `eta^(-2)` budget. -/
theorem nativePNTSquarePrefixRederivedHasAffineEnvelope_of_quadratic_budget
    (eta : ℝ) (heta : 0 < eta) (n : ℕ)
    (hbudget :
      1 < 2 * nativePNTSquarePrefixRederivedCubicConstant *
        (n : ℝ) * eta ^ 2) :
    nativePNTHasAffineEnvelope eta := by
  have hspec := nativePNTSquarePrefixRederivedCubicSlope_spec n
  have hrate := nativePNTSquarePrefixRederivedCubicSlope_quadratic_rate n
  have hslopeEta : nativePNTSquarePrefixRederivedCubicSlope n ≤ eta := by
    by_contra hnot
    have hetaSlope : eta < nativePNTSquarePrefixRederivedCubicSlope n :=
      lt_of_not_ge hnot
    have hsq : eta ^ 2 ≤ (nativePNTSquarePrefixRederivedCubicSlope n) ^ 2 :=
      pow_le_pow_left₀ heta.le hetaSlope.le 2
    have hcoef0 :
        0 ≤ 2 * nativePNTSquarePrefixRederivedCubicConstant * (n : ℝ) := by
      positivity
    have hmul :
        2 * nativePNTSquarePrefixRederivedCubicConstant * (n : ℝ) * eta ^ 2 ≤
          2 * nativePNTSquarePrefixRederivedCubicConstant * (n : ℝ) *
            (nativePNTSquarePrefixRederivedCubicSlope n) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hcoef0
    have hone :
        1 < 2 * nativePNTSquarePrefixRederivedCubicConstant * (n : ℝ) *
          (nativePNTSquarePrefixRederivedCubicSlope n) ^ 2 :=
      hbudget.trans_le hmul
    linarith
  exact nativePNTHasAffineEnvelope_mono hslopeEta hspec.2.2

/-- The normalized Mertens bound can therefore be driven by the fully rederived
square-prefix PNT contraction with the sharper quadratic budget. -/
theorem nativeMertens_abs_div_le_of_squarePrefix_quadratic_budget
    (eta : ℝ) (heta : 0 < eta) (n : ℕ)
    (hbudget :
      1 < 2 * nativePNTSquarePrefixRederivedCubicConstant *
        (n : ℝ) * eta ^ 2) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ N : ℕ, 2 ≤ N →
      |nativeMertensSummatory N| / (N : ℝ) ≤
        eta + (eta + D + 2) / Real.log (N : ℝ) := by
  exact nativeMertens_abs_div_le_of_affineEnvelope eta heta.le
    (nativePNTSquarePrefixRederivedHasAffineEnvelope_of_quadratic_budget
      eta heta n hbudget)

/-! ## Sharpen the one-step coefficient in the small-slope regime -/

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
