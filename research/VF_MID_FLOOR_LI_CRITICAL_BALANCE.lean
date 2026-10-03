import Mathlib
import «research.VF_MID_FLOOR_LI_SIGNED_POPULATION_BALANCE»
import «research.EXACT_LI_PURE_MODEL_CLOSURE»

/-!
# Floor-Li forcing split inside the proved Li fantasy dynamics

This file deliberately proves **no new cancellation theorem**.

All homogeneous cancellation, critical transport, reciprocal contraction, and
Abel return remain in the already-proved exact-Li coordinates.  The only job
here is to split the actual-minus-Li forcing into

  actual - Li
    = (actual - floorLi) + (floorLi - Li).

The first summand is the integer {-1,0,1} floor-Li mismatch.  The second is
the deterministic floor-rounding forcing.  Substituting this identity into the
existing Duhamel/Volterra theorem leaves the Li propagation operator unchanged.

Thus every subsequent cancellation mechanism is inherited from the fantasy
coordinate rather than reproved on the actual-prime carrier.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

/-! ## Integer floor-Li singleton forcing -/

/-- One integer floor-Li event at site q. -/
def vfMidFloorLiSingletonWeight (q : ℕ) : ℂ :=
  (((vfMidFloorLiIntegerPotential q -
      vfMidFloorLiIntegerPotential (q - 1) : ℤ)) : ℂ)

/-- Actual prime event minus the integer floor-Li event.  This is the
sitewise {-1,0,1} forcing on the relevant range. -/
def vfMidFloorLiMismatchFrequencyWeight (q : ℕ) : ℂ :=
  primeSievePrimeIndicator q - vfMidFloorLiSingletonWeight q

/-- Integer floor-Li event minus the exact singleton Li mass.  This is the
deterministic rounding forcing. -/
def vfMidFloorLiRoundingFrequencyWeight (q : ℕ) : ℂ :=
  vfMidFloorLiSingletonWeight q - primeSievePNTDensity q

/-- **Exact forcing split.**
No cancellation is used: this is only the insertion of floor-Li between the
actual prime indicator and the exact-Li singleton weight. -/
theorem primeSievePrimeIndicator_sub_pntDensity_eq_floorLi_forcing
    (q : ℕ) :
    primeSievePrimeIndicator q - primeSievePNTDensity q =
      vfMidFloorLiMismatchFrequencyWeight q +
        vfMidFloorLiRoundingFrequencyWeight q := by
  unfold vfMidFloorLiMismatchFrequencyWeight
    vfMidFloorLiRoundingFrequencyWeight
  ring

/-! ## Existing fantasy propagation with the forcing split exposed -/

/-- **Actual-minus-Li = two forcings + proved Li propagation.**

The third term is *exactly* the homogeneous exact-Li propagator already used
by the fantasy closure.  No new cancellation mechanism is introduced here. -/
theorem actualPrimeState_sub_allScaleLiState_floorLi_forcing_split
    {A L : ℕ → ℕ → ℂ}
    (hA : IsAllScaleActualPrimeState A)
    (hL : IsAllScaleLiState L)
    (x y : ℕ) :
    A x y - L x y =
      -(∑ q ∈ Finset.Ioc 1 (min x y),
          vfMidFloorLiMismatchFrequencyWeight q *
            A (x / q) (q - 1)) -
        (∑ q ∈ Finset.Ioc 1 (min x y),
          vfMidFloorLiRoundingFrequencyWeight q *
            A (x / q) (q - 1)) -
        ∑ q ∈ Finset.Ioc 1 (min x y),
          primeSievePNTDensity q *
            (A (x / q) (q - 1) - L (x / q) (q - 1)) := by
  have h := actualPrimeState_sub_allScaleLiState hA hL x y
  have hforce :
      (∑ q ∈ Finset.Ioc 1 (min x y),
          (primeSievePrimeIndicator q - primeSievePNTDensity q) *
            A (x / q) (q - 1)) =
        (∑ q ∈ Finset.Ioc 1 (min x y),
          vfMidFloorLiMismatchFrequencyWeight q *
            A (x / q) (q - 1)) +
        ∑ q ∈ Finset.Ioc 1 (min x y),
          vfMidFloorLiRoundingFrequencyWeight q *
            A (x / q) (q - 1) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _hq
    rw [primeSievePrimeIndicator_sub_pntDensity_eq_floorLi_forcing q]
    ring
  rw [hforce] at h
  linear_combination h

end RHLean.Analysis
