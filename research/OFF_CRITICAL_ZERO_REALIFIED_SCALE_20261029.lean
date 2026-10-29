import Mathlib
import «research.STABLE_FAR_PERRON_REALIFICATION»

/-!
# Exact zero-mode scale algebra and native realification

This module isolates the precise discrete coarsening algebra. It uses ANY
potential, no Euler-product hypothesis and no analytic continuation claim.

For an actual zeta-zero primitive g_rho(n), the only remaining prerequisite
to specialize the homogeneous theorem is the positive-real complex-power
scaling identity G_rho(q*n) = q^(2*rho) G_rho(n). The algebraic coarsening
and its exact realification below are proved WITHOUT that prerequisite.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

/-- Average q consecutive original complex-valued square blocks. -/
def offcriticalComplexCoarsen (q : ℕ) (a : ℕ → ℂ) (R : ℕ) : ℂ :=
  (∑ j ∈ Finset.Ico (q * R) (q * (R + 1)), a j) / (q : ℂ)

/-- First differences of an arbitrary complex spectral potential. -/
def offcriticalPotentialIncrement (potential : ℕ → ℂ) (R : ℕ) : ℂ :=
  potential (R + 1) - potential R

/-- Every interior boundary telescopes EXACTLY. -/
theorem offcriticalComplexCoarsen_increment
    (q R : ℕ) (potential : ℕ → ℂ) :
    offcriticalComplexCoarsen q
        (offcriticalPotentialIncrement potential) R =
      (potential (q * (R + 1)) - potential (q * R)) / (q : ℂ) := by
  have hle : q * R ≤ q * (R + 1) :=
    Nat.mul_le_mul_left q (Nat.le_succ R)
  unfold offcriticalComplexCoarsen offcriticalPotentialIncrement
  rw [Finset.sum_Ico_sub potential hle]

/-- A homogeneous primitive has the EXACT predicted scale eigenvalue
after taking its first square-block differences. No norm or convergence
hypothesis is present. -/
theorem offcriticalComplexCoarsen_homogeneous
    (q R : ℕ) (potential : ℕ → ℂ) (multiplier : ℂ)
    (hhomogeneous : ∀ n : ℕ, potential (q * n) = multiplier * potential n) :
    offcriticalComplexCoarsen q
        (offcriticalPotentialIncrement potential) R =
      (multiplier / (q : ℂ)) *
        offcriticalPotentialIncrement potential R := by
  rw [offcriticalComplexCoarsen_increment,
    hhomogeneous (R + 1), hhomogeneous R]
  unfold offcriticalPotentialIncrement
  ring

/-- Apply the ACTUAL repository's lossless Phi realification to a
coarsening eigenmode. No synthetic complex-to-real map is introduced. -/
theorem offcriticalRealifiedCoarsen_homogeneous
    (q R : ℕ) (potential : ℕ → ℂ) (multiplier : ℂ)
    (hhomogeneous : ∀ n : ℕ, potential (q * n) = multiplier * potential n) :
    RHLean.Proof.stableFarComplexToRealPair
      (offcriticalComplexCoarsen q
        (offcriticalPotentialIncrement potential) R) =
      RHLean.Proof.stableFarRealComplexMul (multiplier / (q : ℂ))
        (RHLean.Proof.stableFarComplexToRealPair
          (offcriticalPotentialIncrement potential R)) := by
  rw [offcriticalComplexCoarsen_homogeneous
      q R potential multiplier hhomogeneous]
  exact RHLean.Proof.stableFarComplexToRealPair_mul
    (multiplier / (q : ℂ))
    (offcriticalPotentialIncrement potential R)

/-- Real-pair normalized squared energy scales by the squared modulus
of the exact complex eigenvalue. Off-line expansion appears WITHOUT
assuming it is impossible for the actual arithmetic source. -/
theorem offcriticalRealifiedCoarsen_energy
    (q R : ℕ) (potential : ℕ → ℂ) (multiplier : ℂ)
    (hhomogeneous : ∀ n : ℕ, potential (q * n) = multiplier * potential n) :
    RHLean.Proof.stableFarRealPairNormalizedEnergy
      (RHLean.Proof.stableFarComplexToRealPair
        (offcriticalComplexCoarsen q
          (offcriticalPotentialIncrement potential) R)) =
      ‖multiplier / (q : ℂ)‖ ^ 2 *
        ‖offcriticalPotentialIncrement potential R‖ ^ 2 := by
  rw [RHLean.Proof.stableFarRealPairNormalizedEnergy_complexToRealPair,
    offcriticalComplexCoarsen_homogeneous
      q R potential multiplier hhomogeneous,
    norm_mul, mul_pow]

/-! ## Genuine exponential zero-mode primitive (positive real logarithm) -/

/-- For n > 0 this equals n^(2*rho)/rho using the positive-real branch.
At the artificial lower endpoint n = 0, define the potential to be zero,
so the q-scaling law remains true even at the first square block. -/
def offcriticalZeroPrimitive (rho : ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0
  else Complex.exp ((2 * rho) * ((Real.log (n : ℝ) : ℝ) : ℂ)) / rho

/-- A zero mode is an EXACT square-root first difference. -/
def offcriticalZeroMode (rho : ℂ) (R : ℕ) : ℂ :=
  offcriticalZeroPrimitive rho (R + 1) -
    offcriticalZeroPrimitive rho R

/-- This is the nontrivial positive-real complex-power step: actual logarithmic
homogeneity, not an assumed scaling of primes. -/
theorem offcriticalZeroPrimitive_scale
    (rho : ℂ) (q : ℕ) (hq : 0 < q) (n : ℕ) :
    offcriticalZeroPrimitive rho (q * n) =
      Complex.exp ((2 * rho) * ((Real.log (q : ℝ) : ℝ) : ℂ)) *
        offcriticalZeroPrimitive rho n := by
  by_cases hn : n = 0
  · subst n
    simp [offcriticalZeroPrimitive]
  · have hq0 : (q : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hq)
    have hn0 : (n : ℝ) ≠ 0 := by
      exact_mod_cast hn
    have hqn : q * n ≠ 0 := mul_ne_zero (Nat.ne_of_gt hq) hn
    simp only [offcriticalZeroPrimitive, ite_eq_right hn, ite_eq_right hqn]
    have hsplit :
        (2 * rho) * ((Real.log ((q * n : ℕ) : ℝ) : ℝ) : ℂ) =
          (2 * rho) * ((Real.log (q : ℝ) : ℝ) : ℂ) +
            (2 * rho) * ((Real.log (n : ℝ) : ℝ) : ℂ) := by
      rw [Nat.cast_mul, Real.log_mul hq0 hn0]
      push_cast
      ring
    rw [hsplit, Complex.exp_add]
    ring

/-- Every individual hypothetical zeta-zero mode obeys exact coarsening
eigenhomogeneity. The theorem holds for ALL complex rho, even though no
off-critical actual zeta zero is asserted to exist. -/
theorem offcriticalZeroMode_coarsen
    (rho : ℂ) (q R : ℕ) (hq : 0 < q) :
    offcriticalComplexCoarsen q (offcriticalZeroMode rho) R =
      (Complex.exp ((2 * rho) * ((Real.log (q : ℝ) : ℝ) : ℂ)) /
        (q : ℂ)) * offcriticalZeroMode rho R := by
  have hmode :
      offcriticalZeroMode rho =
        offcriticalPotentialIncrement (offcriticalZeroPrimitive rho) := by
    rfl
  rw [hmode]
  exact offcriticalComplexCoarsen_homogeneous q R
    (offcriticalZeroPrimitive rho)
    (Complex.exp ((2 * rho) * ((Real.log (q : ℝ) : ℝ) : ℂ)))
    (offcriticalZeroPrimitive_scale rho q hq)

/-- The true repository Phi map carries the same exact q-scale eigenaction. -/
theorem offcriticalZeroMode_realified_coarsen
    (rho : ℂ) (q R : ℕ) (hq : 0 < q) :
    RHLean.Proof.stableFarComplexToRealPair
      (offcriticalComplexCoarsen q (offcriticalZeroMode rho) R) =
      RHLean.Proof.stableFarRealComplexMul
        (Complex.exp ((2 * rho) * ((Real.log (q : ℝ) : ℝ) : ℂ)) /
          (q : ℂ))
        (RHLean.Proof.stableFarComplexToRealPair
          (offcriticalZeroMode rho R)) := by
  rw [offcriticalZeroMode_coarsen rho q R hq]
  exact RHLean.Proof.stableFarComplexToRealPair_mul
    (Complex.exp ((2 * rho) * ((Real.log (q : ℝ) : ℝ) : ℂ)) /
      (q : ℂ)) (offcriticalZeroMode rho R)

/-! ## The functional-equation reflected spectral pair -/

/-- Partner of rho across Re(s)=1/2, with the same imaginary coordinate. -/
def offcriticalReflected (rho : ℂ) : ℂ :=
  1 - star rho

theorem offcriticalReflected_re (rho : ℂ) :
    (offcriticalReflected rho).re = 1 - rho.re := by
  simp [offcriticalReflected]

theorem offcriticalReflected_im (rho : ℂ) :
    (offcriticalReflected rho).im = rho.im := by
  simp [offcriticalReflected]

/-- The individual q-scale eigenvalue is q^(2rho-1), not the
incorrect q^(2rho) that would arise from omitting the averaging /q. -/
def offcriticalZeroEigenMultiplier (rho : ℂ) (q : ℕ) : ℂ :=
  Complex.exp ((2 * rho - 1) *
    ((Real.log (q : ℝ) : ℝ) : ℂ))

/-- Exact radial part of the q-eigenvalue, applicable to any genuine
zeta zero and its reflected partner. -/
theorem offcriticalZeroEigenMultiplier_norm (rho : ℂ) (q : ℕ) :
    ‖offcriticalZeroEigenMultiplier rho q‖ =
      Real.exp ((2 * rho.re - 1) * Real.log (q : ℝ)) := by
  unfold offcriticalZeroEigenMultiplier
  rw [Complex.norm_exp]
  congr 1
  have hIm :
      (((Real.log (q : ℝ) : ℝ) : ℂ)).im = 0 := by
        simp only [Complex.ofReal_im]
  have hRe :
      (((Real.log (q : ℝ) : ℝ) : ℂ)).re = Real.log (q : ℝ) := by
        simp only [Complex.ofReal_re]
  rw [Complex.mul_re, hIm, hRe]
  simp only [mul_zero, sub_zero]
  have hCoeff : (2 * rho - 1).re = 2 * rho.re - 1 := by
    simp [Complex.sub_re, Complex.mul_re]
  rw [hCoeff]

/-- The reflected mode has reciprocal radial eigenvalue,
although its rotational phase is the SAME. No positivity or contraction
of the complete actual-prime source follows from this mode identity. -/
theorem offcriticalReflectedEigenMultiplier_norm (rho : ℂ) (q : ℕ) :
    ‖offcriticalZeroEigenMultiplier (offcriticalReflected rho) q‖ =
      Real.exp ((1 - 2 * rho.re) * Real.log (q : ℝ)) := by
  rw [offcriticalZeroEigenMultiplier_norm, offcriticalReflected_re]
  congr 1
  ring

end RHLean.Analysis
