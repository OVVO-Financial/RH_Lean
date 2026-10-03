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

/-- Floor-Li mismatch forcing transported into the already-proved critical
half-weight coordinate. -/
def criticalFloorLiMismatchFrequencyWeight (q : ℕ) : ℂ :=
  vfMidFloorLiMismatchFrequencyWeight q * criticalSqrtWeight q

/-- Deterministic floor-rounding forcing in the same critical coordinate. -/
def criticalFloorLiRoundingFrequencyWeight (q : ℕ) : ℂ :=
  vfMidFloorLiRoundingFrequencyWeight q * criticalSqrtWeight q

/-- The centered critical actual-prime forcing is exactly the sum of the
integer floor-Li forcing and deterministic rounding forcing. -/
theorem criticalCenteredPrimeFrequencyWeight_eq_floorLi_forcings
    (q : ℕ) :
    criticalCenteredPrimeFrequencyWeight q =
      criticalFloorLiMismatchFrequencyWeight q +
        criticalFloorLiRoundingFrequencyWeight q := by
  unfold criticalCenteredPrimeFrequencyWeight
    criticalFloorLiMismatchFrequencyWeight
    criticalFloorLiRoundingFrequencyWeight
  rw [primeSievePrimeIndicator_sub_pntDensity_eq_floorLi_forcing q]
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

/-- Critical fantasy propagation with only the forcing split changed.

The final sum is exactly the pre-existing critical Li propagator. Therefore
all critical cancellation and Abel return remain inherited from the fantasy
coordinate. -/
theorem actualPrimeCriticalState_sub_allScaleLiCriticalState_floorLi_forcing_split
    {A L : ℕ → ℕ → ℂ}
    (hA : IsAllScaleActualPrimeState A)
    (hL : IsAllScaleLiState L)
    (x y : ℕ) :
    allScaleActualPrimeCriticalState A x y -
        allScaleLiCriticalState L x y =
      -(∑ q ∈ Finset.Ioc 1 (min x y),
          criticalFloorLiMismatchFrequencyWeight q *
            allScaleActualPrimeCriticalState A (x / q) (q - 1)) -
        (∑ q ∈ Finset.Ioc 1 (min x y),
          criticalFloorLiRoundingFrequencyWeight q *
            allScaleActualPrimeCriticalState A (x / q) (q - 1)) -
        ∑ q ∈ Finset.Ioc 1 (min x y),
          criticalLiFrequencyWeight q *
            (allScaleActualPrimeCriticalState A (x / q) (q - 1) -
              allScaleLiCriticalState L (x / q) (q - 1)) := by
  have h :=
    actualPrimeCriticalState_sub_allScaleLiCriticalState hA hL x y
  have hforce :
      (∑ q ∈ Finset.Ioc 1 (min x y),
          criticalCenteredPrimeFrequencyWeight q *
            allScaleActualPrimeCriticalState A (x / q) (q - 1)) =
        (∑ q ∈ Finset.Ioc 1 (min x y),
          criticalFloorLiMismatchFrequencyWeight q *
            allScaleActualPrimeCriticalState A (x / q) (q - 1)) +
        ∑ q ∈ Finset.Ioc 1 (min x y),
          criticalFloorLiRoundingFrequencyWeight q *
            allScaleActualPrimeCriticalState A (x / q) (q - 1) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _hq
    rw [criticalCenteredPrimeFrequencyWeight_eq_floorLi_forcings q]
    ring
  rw [hforce] at h
  linear_combination h

/-! ## Reciprocal fantasy coordinate -/

def reciprocalActualPrimeFrequencyWeight (q : ℕ) : ℂ :=
  primeSievePrimeIndicator q * reciprocalWeight q

def reciprocalCenteredPrimeFrequencyWeight (q : ℕ) : ℂ :=
  (primeSievePrimeIndicator q - primeSievePNTDensity q) *
    reciprocalWeight q

def reciprocalFloorLiMismatchFrequencyWeight (q : ℕ) : ℂ :=
  vfMidFloorLiMismatchFrequencyWeight q * reciprocalWeight q

def reciprocalFloorLiRoundingFrequencyWeight (q : ℕ) : ℂ :=
  vfMidFloorLiRoundingFrequencyWeight q * reciprocalWeight q

theorem reciprocalActualPrimeFrequencyWeight_sub_li
    (q : ℕ) :
    reciprocalActualPrimeFrequencyWeight q -
        reciprocalLiFrequencyWeight q =
      reciprocalCenteredPrimeFrequencyWeight q := by
  unfold reciprocalActualPrimeFrequencyWeight
    reciprocalLiFrequencyWeight
    reciprocalCenteredPrimeFrequencyWeight
  ring

theorem reciprocalCenteredPrimeFrequencyWeight_eq_floorLi_forcings
    (q : ℕ) :
    reciprocalCenteredPrimeFrequencyWeight q =
      reciprocalFloorLiMismatchFrequencyWeight q +
        reciprocalFloorLiRoundingFrequencyWeight q := by
  unfold reciprocalCenteredPrimeFrequencyWeight
    reciprocalFloorLiMismatchFrequencyWeight
    reciprocalFloorLiRoundingFrequencyWeight
  rw [primeSievePrimeIndicator_sub_pntDensity_eq_floorLi_forcing q]
  ring

def allScaleActualPrimeReciprocalState
    (A : ℕ → ℕ → ℂ) (x y : ℕ) : ℂ :=
  1 + weightedForwardDifferencePrefix reciprocalWeight
    (fun n => A n y) x

theorem allScaleActualPrimeReciprocalState_isPrimeFrequencyState
    {A : ℕ → ℕ → ℂ} (hA : IsAllScaleActualPrimeState A) :
    IsPrimeFrequencyState reciprocalActualPrimeFrequencyWeight
      (allScaleActualPrimeReciprocalState A) := by
  intro x y
  unfold allScaleActualPrimeReciprocalState
    primeFrequencyStep reciprocalActualPrimeFrequencyWeight
  have hzero : ∀ q : ℕ, A 0 (q - 1) = 1 := by
    intro q
    rw [hA 0 (q - 1)]
    simp [primeFrequencyStep]
  have hrec :=
    weightedForwardDifferencePrefix_primeFrequencyState
      hA reciprocalWeight_mul x y
  rw [hrec]
  apply congrArg (fun z : ℂ => 1 - z)
  apply Finset.sum_congr rfl
  intro q _hq
  rw [hzero q]

theorem actualPrimeReciprocalState_sub_allScaleLiReciprocalState
    {A L : ℕ → ℕ → ℂ}
    (hA : IsAllScaleActualPrimeState A)
    (hL : IsAllScaleLiState L)
    (x y : ℕ) :
    allScaleActualPrimeReciprocalState A x y -
        allScaleLiReciprocalState L x y =
      -(∑ q ∈ Finset.Ioc 1 (min x y),
          reciprocalCenteredPrimeFrequencyWeight q *
            allScaleActualPrimeReciprocalState A (x / q) (q - 1)) -
        ∑ q ∈ Finset.Ioc 1 (min x y),
          reciprocalLiFrequencyWeight q *
            (allScaleActualPrimeReciprocalState A (x / q) (q - 1) -
              allScaleLiReciprocalState L (x / q) (q - 1)) := by
  have hAr :=
    allScaleActualPrimeReciprocalState_isPrimeFrequencyState hA
  have hLr :=
    allScaleLiReciprocalState_isPrimeFrequencyState hL
  have h :=
    primeFrequencyState_sub_eq_signedDisplacement
      hAr hLr x y
  rw [show
      (fun q =>
        reciprocalActualPrimeFrequencyWeight q -
          reciprocalLiFrequencyWeight q) =
        reciprocalCenteredPrimeFrequencyWeight by
      funext q
      exact reciprocalActualPrimeFrequencyWeight_sub_li q] at h
  exact h

/-- Reciprocal fantasy propagation with floor-Li forcing exposed.

The homogeneous propagator is unchanged and is the exact-Li reciprocal
operator whose root-to-square norm mass is already bounded by log 2. -/
theorem actualPrimeReciprocalState_sub_allScaleLiReciprocalState_floorLi_forcing_split
    {A L : ℕ → ℕ → ℂ}
    (hA : IsAllScaleActualPrimeState A)
    (hL : IsAllScaleLiState L)
    (x y : ℕ) :
    allScaleActualPrimeReciprocalState A x y -
        allScaleLiReciprocalState L x y =
      -(∑ q ∈ Finset.Ioc 1 (min x y),
          reciprocalFloorLiMismatchFrequencyWeight q *
            allScaleActualPrimeReciprocalState A (x / q) (q - 1)) -
        (∑ q ∈ Finset.Ioc 1 (min x y),
          reciprocalFloorLiRoundingFrequencyWeight q *
            allScaleActualPrimeReciprocalState A (x / q) (q - 1)) -
        ∑ q ∈ Finset.Ioc 1 (min x y),
          reciprocalLiFrequencyWeight q *
            (allScaleActualPrimeReciprocalState A (x / q) (q - 1) -
              allScaleLiReciprocalState L (x / q) (q - 1)) := by
  have h :=
    actualPrimeReciprocalState_sub_allScaleLiReciprocalState hA hL x y
  have hforce :
      (∑ q ∈ Finset.Ioc 1 (min x y),
          reciprocalCenteredPrimeFrequencyWeight q *
            allScaleActualPrimeReciprocalState A (x / q) (q - 1)) =
        (∑ q ∈ Finset.Ioc 1 (min x y),
          reciprocalFloorLiMismatchFrequencyWeight q *
            allScaleActualPrimeReciprocalState A (x / q) (q - 1)) +
        ∑ q ∈ Finset.Ioc 1 (min x y),
          reciprocalFloorLiRoundingFrequencyWeight q *
            allScaleActualPrimeReciprocalState A (x / q) (q - 1) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _hq
    rw [reciprocalCenteredPrimeFrequencyWeight_eq_floorLi_forcings q]
    ring
  rw [hforce] at h
  linear_combination h

theorem floorLiFantasyReciprocalPropagation_norm_sum_rootSquare_le_log_two
    {y x : ℕ} (hy : 2 ≤ y) (hxy : x ≤ y ^ 2) :
    (∑ q ∈ Finset.Ioc y x, ‖reciprocalLiFrequencyWeight q‖) ≤
      Real.log 2 :=
  reciprocalLiFrequencyWeight_norm_sum_rootSquare_le_log_two hy hxy

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
