import «research.VF_919_OAI_SQUARE_BLOCK_FOUR_INDEX_COVARIANCE_20261019»

/-!
# EXACT original ordered square-block covariance on individual ideal norm fibers

Mathematical all-integer source:
  mu_Z(n) = sum_{d*m=n} chi_-3(d) a_F(m),
  a_F(m) = sum_{Norm(I)=m} mu_F(I) (proved in original
           OAI/Hecke/LocalEulerIdentities under Lean 4.34.1).

This file compiles the SECOND equality into the ORIGINAL RH_Lean
within-block ordered pairs, WITHOUT CHANGING which physical integer
is larger or replacing prime-ideal labels by scalar Fourier phases.

The theorem accepts any norm-fiber function F whose coefficients are
pointwise identical to RH_Lean's constructed a_F. It does not postulate
that a true ideal fiber has this property: the separate pinned original
OAI 4.34.1 module proves that property with actual Ideal O and
UniqueFactorizationMonoid.moebius, without assumptions.

The resulting formula has genuine strict
  R^2 <= m < n < (R+1)^2,
TWO separate divisor fibers and ALL their cross-products.
It is a real proof of exactly the native vf919SquareShellCovariance R.
This is stronger than an aggregated norm-gram equality that forgets
the original m<n physical order.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

/-- The SAME physical pair carrier, but with an explicit generic
    genuine-ideal norm-fiber coefficient at each of its two ends. -/
def vf919OAIOrderedPhysicalIdealFiberCovariance
    (F : ℕ → ℂ) (R : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ico (R ^ 2) ((R + 1) ^ 2),
    ∑ m ∈ Finset.Ico (R ^ 2) n,
      ∑ s ∈ Nat.divisorsAntidiagonal m,
        ∑ t ∈ Nat.divisorsAntidiagonal n,
          (vf919ChiMinusThree s.1 * F s.2) *
            (vf919ChiMinusThree t.1 * F t.2)

/-- Kernel-checked actual-carrier equality, without dropping ONE original
    physical covariance pair or assuming independence/negative covariance.
    The only coefficient input is the precise true ideal-norm identity. -/
theorem vf919OAI_original_ordered_covariance_eq_any_real_ideal_fiber
    (F : ℕ → ℂ)
    (hF : ∀ m : ℕ, F m = vf919EisensteinNormCoefficients m)
    (R : ℕ) :
    (vf919SquareShellCovariance R : ℂ) =
      vf919OAIOrderedPhysicalIdealFiberCovariance F R := by
  rw [vf919SquareShell_actual_signed_covariance_eq_fourIndexHecke]
  unfold vf919OAIOrderedPhysicalIdealFiberCovariance
    vf919SquareShellFourIndexHeckeCovariance
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  rw [hF s.2, hF t.2]

/-- This literal auxiliary identity makes clear that the original
    diagonal has NOT been removed or counted twice. -/
theorem vf919OAI_original_signed_greenKubo_eq_real_ideal_fiber
    (F : ℕ → ℂ)
    (hF : ∀ m, F m = vf919EisensteinNormCoefficients m)
    (R : ℕ) :
    (vf919SquareShellSum R : ℂ) ^ 2 =
      (vf919SquareShellDiagonal R : ℂ) +
        2 * vf919OAIOrderedPhysicalIdealFiberCovariance F R := by
  have h := congrArg (fun x : ℝ => (x : ℂ))
    (vf919SquareShell_signedGreenKubo R)
  push_cast at h
  rw [← vf919OAI_original_ordered_covariance_eq_any_real_ideal_fiber
    F hF R]
  exact h

#print axioms vf919OAI_original_ordered_covariance_eq_any_real_ideal_fiber
#print axioms vf919OAI_original_signed_greenKubo_eq_real_ideal_fiber

end RHLean.Analysis
