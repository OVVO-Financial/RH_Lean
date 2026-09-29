import Mathlib
import «research.ALL_SCALE_LI_DISPLACEMENT_REDUCTION»
import RHLean.Proof.FinitePartialMoments

/-!
# Pure exact-Li model closure spine

This file isolates the model-only closure mechanism needed after PR #814.

There are no actual-prime indicators and no prime-count discrepancy terms in the
main theorem below.  The theorem says that a uniformly bounded continuous
reference model plus an O(R) discrete/continuous transfer is already enough to
prove the exact all-scale Li square-root target.

The file also records degree-zero partial mass separately from the generic
natural-power API.  This avoids the 0^0 convention and matches the CDF/VaR
meaning of degree zero used by the NNS partial-moment formulation.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Proof

/-- Degree-zero lower partial mass: the weighted CDF/counting functional.
This is deliberately separate from `lowerPartialMomentNat 0`. -/
def degreeZeroLowerMass {ι : Type*}
    (s : Finset ι) (w x : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i ∈ s, if x i ≤ t then w i else 0

/-- Degree-zero upper partial mass. -/
def degreeZeroUpperMass {ι : Type*}
    (s : Finset ι) (w x : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i ∈ s, if t < x i then w i else 0

/-- Degree-zero lower plus upper mass is exactly the common total weight. -/
theorem degreeZeroLowerMass_add_upperMass
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ) (t : ℝ) :
    degreeZeroLowerMass s w x t + degreeZeroUpperMass s w x t =
      ∑ i ∈ s, w i := by
  unfold degreeZeroLowerMass degreeZeroUpperMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : x i ≤ t
  · have hn : ¬ t < x i := not_lt.mpr h
    simp [h, hn]
  · have ht : t < x i := lt_of_not_ge h
    simp [h, ht]

/-- A uniformly bounded continuous/reference diagonal. -/
def UniformReferenceDiagonalBounded (M : ℕ → ℂ) : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℕ, ‖M x‖ ≤ B

/-- Linear discrete-to-reference transfer at square-root endpoints. -/
def AllScaleLiLinearReferenceTransfer (M : ℕ → ℂ) : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧
    ∀ (L : ℕ → ℕ → ℂ) (R : ℕ),
      IsAllScaleLiState L →
      PrimeFrequencySaturated L →
      2 ≤ R →
      ‖L (squareRootEndpoint R) (squareRootEndpoint R) -
          M (squareRootEndpoint R)‖ ≤ A * (R : ℝ)

/-- **Pure-model closure spine.**
A bounded continuous/reference model plus an O(R) transfer closes the intrinsic
all-scale Li theorem.  No actual-prime object occurs in the statement or proof. -/
theorem allScaleLiSquareRootBounded_of_uniformReference_linearTransfer
    (M : ℕ → ℂ)
    (hM : UniformReferenceDiagonalBounded M)
    (hT : AllScaleLiLinearReferenceTransfer M) :
    AllScaleLiSquareRootBoundedStatement := by
  rcases hM with ⟨B, hB, hMb⟩
  rcases hT with ⟨A, hA, hTb⟩
  refine ⟨(A + B) ^ 2, sq_nonneg (A + B), ?_⟩
  intro L R hL hsat hR
  have hR1n : 1 ≤ R := by omega
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR1n
  have hBR : B ≤ B * (R : ℝ) := by
    nlinarith
  have hMscale :
      ‖M (squareRootEndpoint R)‖ ≤ B * (R : ℝ) :=
    (hMb (squareRootEndpoint R)).trans hBR
  have hdiff := hTb L R hL hsat hR
  have hnorm :
      ‖L (squareRootEndpoint R) (squareRootEndpoint R)‖ ≤
        (A + B) * (R : ℝ) := by
    calc
      ‖L (squareRootEndpoint R) (squareRootEndpoint R)‖ =
          ‖(L (squareRootEndpoint R) (squareRootEndpoint R) -
              M (squareRootEndpoint R)) + M (squareRootEndpoint R)‖ := by
                congr 1
                ring
      _ ≤ ‖L (squareRootEndpoint R) (squareRootEndpoint R) -
              M (squareRootEndpoint R)‖ +
            ‖M (squareRootEndpoint R)‖ := norm_add_le _ _
      _ ≤ A * (R : ℝ) + B * (R : ℝ) := add_le_add hdiff hMscale
      _ = (A + B) * (R : ℝ) := by ring
  have hAB : 0 ≤ A + B := add_nonneg hA hB
  have hR0 : (0 : ℝ) ≤ (R : ℝ) := by positivity
  have hright : 0 ≤ (A + B) * (R : ℝ) := mul_nonneg hAB hR0
  have hsquare :=
    mul_self_le_mul_self (norm_nonneg
      (L (squareRootEndpoint R) (squareRootEndpoint R))) hnorm
  simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hsquare


/-! ## Exact residual propagation for a reference model -/

/-- Residual of an arbitrary reference state against the same prime-frequency
recursion.  For the continuous/Dickman reference this is exactly where the
unit-bin discretization error is to be estimated. -/
def primeFrequencyReferenceResidual
    (w : ℕ → ℂ) (C : ℕ → ℕ → ℂ) (x y : ℕ) : ℂ :=
  C x y - primeFrequencyStep w C x y

/-- An exact state has zero reference residual. -/
theorem primeFrequencyReferenceResidual_eq_zero
    {w : ℕ → ℂ} {C : ℕ → ℕ → ℂ}
    (hC : IsPrimeFrequencyState w C) (x y : ℕ) :
    primeFrequencyReferenceResidual w C x y = 0 := by
  unfold primeFrequencyReferenceResidual
  rw [hC x y]
  ring

/-- **Exact Duhamel/Volterra propagation identity.**
If `L` is the exact discrete frequency state and `C` is any reference
state, their difference is the propagated child difference plus only the local
reference residual.  No actual-prime or prime-discrepancy object occurs. -/
theorem primeFrequencyState_sub_reference_eq_propagated_sub_residual
    {w : ℕ → ℂ} {L C : ℕ → ℕ → ℂ}
    (hL : IsPrimeFrequencyState w L) (x y : ℕ) :
    L x y - C x y =
      -(∑ q ∈ Finset.Ioc 1 (min x y),
          w q * (L (x / q) (q - 1) - C (x / q) (q - 1))) -
        primeFrequencyReferenceResidual w C x y := by
  rw [hL x y]
  unfold primeFrequencyReferenceResidual primeFrequencyStep
  ring_nf
  rw [← Finset.sum_sub_distrib]
  apply congrArg (fun z : ℂ => -z - (C x y - (1 -
    ∑ q ∈ Finset.Ioc 1 (min x y), w q * C (x / q) (q - 1)))) ?_
  apply Finset.sum_congr rfl
  intro q hq
  ring

/-- Specialization to the all-scale singleton-Li weights. -/
theorem allScaleLiState_sub_reference_eq_propagated_sub_residual
    {L C : ℕ → ℕ → ℂ}
    (hL : IsAllScaleLiState L) (x y : ℕ) :
    L x y - C x y =
      -(∑ q ∈ Finset.Ioc 1 (min x y),
          primeSievePNTDensity q *
            (L (x / q) (q - 1) - C (x / q) (q - 1))) -
        primeFrequencyReferenceResidual primeSievePNTDensity C x y :=
  primeFrequencyState_sub_reference_eq_propagated_sub_residual hL x y

end RHLean.Analysis
