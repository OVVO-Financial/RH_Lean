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
  have hle : q * R ≤ q * (R + 1) := by omega
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

end RHLean.Analysis
