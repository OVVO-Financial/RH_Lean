import Mathlib
import «research.ALL_SCALE_LI_DISPLACEMENT_REDUCTION»
import «research.VF_MID_FLOOR_LI_CRITICAL_BALANCE»

/-!
# Actual-prime critical largest-owner recursion

The floor-Li reduction leaves one hard continuous critical atom

  (1_P(q) - w_Li(q)) / sqrt(q).

This file puts that atom into the repository's exact all-scale largest-prime
recursion.  No estimate is asserted here.

The critical transform of the actual-prime frequency state is itself a
prime-frequency state with owner weight

  1_P(q) / sqrt(q),

while the existing exact-Li critical transform has owner weight

  w_Li(q) / sqrt(q).

Duhamel subtraction therefore produces the centered critical atom before any
absolute values are taken.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

/-! ## Critical actual-prime owner weight and state -/

def criticalActualPrimeFrequencyWeight (q : ℕ) : ℂ :=
  primeSievePrimeIndicator q * criticalSqrtWeight q

def criticalCenteredPrimeFrequencyWeight (q : ℕ) : ℂ :=
  (primeSievePrimeIndicator q - primeSievePNTDensity q) *
    criticalSqrtWeight q

theorem criticalActualPrimeFrequencyWeight_sub_li
    (q : ℕ) :
    criticalActualPrimeFrequencyWeight q -
        criticalLiFrequencyWeight q =
      criticalCenteredPrimeFrequencyWeight q := by
  unfold criticalActualPrimeFrequencyWeight
    criticalLiFrequencyWeight
    criticalCenteredPrimeFrequencyWeight
  ring

def allScaleActualPrimeCriticalState
    (A : ℕ → ℕ → ℂ) (x y : ℕ) : ℂ :=
  1 + weightedForwardDifferencePrefix criticalSqrtWeight
    (fun n => A n y) x

theorem allScaleActualPrimeCriticalState_isPrimeFrequencyState
    {A : ℕ → ℕ → ℂ} (hA : IsAllScaleActualPrimeState A) :
    IsPrimeFrequencyState criticalActualPrimeFrequencyWeight
      (allScaleActualPrimeCriticalState A) := by
  intro x y
  unfold allScaleActualPrimeCriticalState
    primeFrequencyStep criticalActualPrimeFrequencyWeight
  have hzero : ∀ q : ℕ, A 0 (q - 1) = 1 := by
    intro q
    rw [hA 0 (q - 1)]
    simp [primeFrequencyStep]
  have hrec :=
    weightedForwardDifferencePrefix_primeFrequencyState
      hA criticalSqrtWeight_mul x y
  rw [hrec]
  apply congrArg (fun z : ℂ => 1 - z)
  apply Finset.sum_congr rfl
  intro q hq
  rw [hzero q]

/-! ## Exact critical Duhamel displacement -/

theorem actualPrimeCriticalState_sub_allScaleLiCriticalState
    {A L : ℕ → ℕ → ℂ}
    (hA : IsAllScaleActualPrimeState A)
    (hL : IsAllScaleLiState L)
    (x y : ℕ) :
    allScaleActualPrimeCriticalState A x y -
        allScaleLiCriticalState L x y =
      -(∑ q ∈ Finset.Ioc 1 (min x y),
          criticalCenteredPrimeFrequencyWeight q *
            allScaleActualPrimeCriticalState A (x / q) (q - 1)) -
        ∑ q ∈ Finset.Ioc 1 (min x y),
          criticalLiFrequencyWeight q *
            (allScaleActualPrimeCriticalState A (x / q) (q - 1) -
              allScaleLiCriticalState L (x / q) (q - 1)) := by
  have hAc :=
    allScaleActualPrimeCriticalState_isPrimeFrequencyState hA
  have hLc :=
    allScaleLiCriticalState_isPrimeFrequencyState hL
  have h :=
    primeFrequencyState_sub_eq_signedDisplacement
      hAc hLc x y
  rw [show
      (fun q =>
        criticalActualPrimeFrequencyWeight q -
          criticalLiFrequencyWeight q) =
        criticalCenteredPrimeFrequencyWeight by
      funext q
      exact criticalActualPrimeFrequencyWeight_sub_li q] at h
  exact h

/-! ## Solve Duhamel for the raw centered critical source -/

def criticalCenteredPrimeSource (x y : ℕ) : ℂ :=
  ∑ q ∈ Finset.Ioc 1 (min x y),
    criticalCenteredPrimeFrequencyWeight q

def criticalCenteredPrimeChildCorrection
    (A : ℕ → ℕ → ℂ) (x y : ℕ) : ℂ :=
  ∑ q ∈ Finset.Ioc 1 (min x y),
    criticalCenteredPrimeFrequencyWeight q *
      (allScaleActualPrimeCriticalState A (x / q) (q - 1) - 1)

def criticalLiPropagatedStateDisplacement
    (A L : ℕ → ℕ → ℂ) (x y : ℕ) : ℂ :=
  ∑ q ∈ Finset.Ioc 1 (min x y),
    criticalLiFrequencyWeight q *
      (allScaleActualPrimeCriticalState A (x / q) (q - 1) -
        allScaleLiCriticalState L (x / q) (q - 1))

/-- **Exact source identity.**
The raw centered critical prime source equals minus the transformed state
displacement, minus the actual-child deviation from one, minus the Li-weighted
propagated state displacement.  This is the direct signed recursion to attack;
no triangle inequality has been applied. -/
theorem criticalCenteredPrimeSource_eq_state_add_child_add_propagated
    {A L : ℕ → ℕ → ℂ}
    (hA : IsAllScaleActualPrimeState A)
    (hL : IsAllScaleLiState L)
    (x y : ℕ) :
    criticalCenteredPrimeSource x y =
      -(allScaleActualPrimeCriticalState A x y -
          allScaleLiCriticalState L x y) -
        criticalCenteredPrimeChildCorrection A x y -
        criticalLiPropagatedStateDisplacement A L x y := by
  have hduhamel :=
    actualPrimeCriticalState_sub_allScaleLiCriticalState hA hL x y
  unfold criticalCenteredPrimeSource
    criticalCenteredPrimeChildCorrection
    criticalLiPropagatedStateDisplacement
  have hsplit :
      (∑ q ∈ Finset.Ioc 1 (min x y),
          criticalCenteredPrimeFrequencyWeight q *
            allScaleActualPrimeCriticalState A (x / q) (q - 1)) =
        (∑ q ∈ Finset.Ioc 1 (min x y),
          criticalCenteredPrimeFrequencyWeight q) +
        ∑ q ∈ Finset.Ioc 1 (min x y),
          criticalCenteredPrimeFrequencyWeight q *
            (allScaleActualPrimeCriticalState A (x / q) (q - 1) - 1) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    ring
  rw [hsplit] at hduhamel
  linear_combination -hduhamel

/-! ## Root-to-square source tail -/

def criticalCenteredPrimeSourceTail (A X : ℕ) : ℂ :=
  ∑ q ∈ Finset.Ioc A X,
    criticalCenteredPrimeFrequencyWeight q

theorem criticalCenteredPrimeSourceTail_eq_prefix_sub
    {A X : ℕ} (hAX : A ≤ X) :
    criticalCenteredPrimeSourceTail A X =
      criticalCenteredPrimeSource X X -
        criticalCenteredPrimeSource A A := by
  unfold criticalCenteredPrimeSourceTail criticalCenteredPrimeSource
  simp only [min_self]
  have hsplit :=
    Finset.sum_Ioc_consecutive
      (f := criticalCenteredPrimeFrequencyWeight)
      (Nat.zero_le A) hAX
  linear_combination hsplit

end RHLean.Analysis
