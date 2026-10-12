import Mathlib
import «research.VF_MID_915_FIXED17_ACTUAL_SIGNED_INLET»
import «research.VF_MID_FLOOR_LI_TRANSPORT_CANCELLATION»
import «research.VF_MID_FIRST_BAD_NORMALIZED_PARTIAL_MOMENT»
import «research.VF_MID_LI_UNIFORM_QUADRATURE»

/-!
# #915: actual owner census compressed into discrete-Li unmatched boundary

This is the SOURCE-LEVEL transfer requested for #915. It does NOT import
the RED production theorem or assert its unproved first-bad inequality.

The original entire signed historical owner run is compressed exactly into:
  * the original signed historical anchor D_A,
  * the genuinely unmatched prime-versus-floor-Li positive-one / negative-one population at
    the endpoint, with all matched populations canceled ONCE, and
  * the DETERMINISTIC difference between floor-Li and VF at the two squares.

No historical |z| is added to the original #915 NNS denominator.

The fixed-17 wheel is eliminated pointwise in the moving-owner discrepancy:
  (W_17 - actualSupply) - (W_17 - floorLiDemand)
    = floorLiDemand - actualSupply.

The remaining arithmetic is NOT proved small. The theorem provides an
exact transport-boundary interface, not an RH closure.
-/

noncomputable section
open scoped BigOperators
namespace RHLean.Analysis
open RHLean.Arithmetic RHLean.Proof
attribute [local instance] Classical.propDecidable

/-- Moving ACTUAL prime-owner removals minus exactly the integer
floor-Li-required removals, on the SAME 17-wheel physical source.
The Li-required amount is only a benchmark, not a manufactured sieve. -/
def vfMid915MovingOwnerMinusFloorLiDemand (R : ℕ) : ℝ :=
  vfMid915ActualAfter17OwnerRemovals R -
    (vfMid915FixedWheel17Supply R -
      (vfMidFloorLiBlockSupply R : ℝ))

/-- Cancellation of the fixed wheel occurs before ANY absolute value.
This is exact even when the floor-Li benchmark is not a feasible
nonnegative count of physical removals. -/
theorem vfMid915MovingOwnerMinusFloorLiDemand_eq_blockDefect
    (R : ℕ) :
    vfMid915MovingOwnerMinusFloorLiDemand R =
      (vfMidFloorLiBlockPrimeDefect R : ℝ) := by
  unfold vfMid915MovingOwnerMinusFloorLiDemand
    vfMid915ActualAfter17OwnerRemovals
    vfMidFloorLiBlockPrimeDefect
  push_cast
  ring

/-- The COMPLETE historical moving-owner correction, kept signed. -/
def vfMid915HistoricalMovingOwnerCorrection (A B : ℕ) : ℝ :=
  ∑ r ∈ Finset.Ico A B,
    vfMid915MovingOwnerMinusFloorLiDemand r

/-- Exact entire history = negative boundary mass of the actual primitive
floor-Li mismatch stream. All paired opposite-sign event mass disappears once. -/
theorem vfMid915HistoricalMovingOwner_eq_signedMismatch
    {A B : ℕ} (hA : 2 ≤ A) (hAB : A ≤ B) :
    vfMid915HistoricalMovingOwnerCorrection A B =
      -((vfMidFloorLiSignedPopulationBalance (A ^ 2) (B ^ 2) : ℤ) : ℝ) := by
  have htern :
      VFMidFloorLiPrimitiveTernaryOn (A ^ 2) (B ^ 2) :=
    vfMidFloorLiPrimitiveTernaryOn_of_four_le
      (by nlinarith : 4 ≤ A ^ 2)
  have hbal :
      vfMidFloorLiSignedPopulationBalance (A ^ 2) (B ^ 2) =
        -vfMidFloorLiDyadicPrimeDefect A B := by
    rw [vfMidFloorLiSignedPopulationBalance_eq_mismatchMass htern]
    exact vfMidFloorLiSignedMismatchMass_sq_eq_neg_dyadicPrimeDefect hAB
  calc
    vfMid915HistoricalMovingOwnerCorrection A B =
        ∑ r ∈ Finset.Ico A B,
          ((vfMidFloorLiBlockPrimeDefect r : ℤ) : ℝ) := by
      unfold vfMid915HistoricalMovingOwnerCorrection
      apply Finset.sum_congr rfl
      intro r _hr
      exact vfMid915MovingOwnerMinusFloorLiDemand_eq_blockDefect r
    _ = ((vfMidFloorLiDyadicPrimeDefect A B : ℤ) : ℝ) := by
      simp [vfMidFloorLiDyadicPrimeDefect]
    _ = -((vfMidFloorLiSignedPopulationBalance (A ^ 2) (B ^ 2) : ℤ) : ℝ) := by
      rw [hbal]
      push_cast
      ring

/-! ## Honest cancellation of the two actual event populations -/

/-- The largest possible count of paired opposite-sign *unit* mismatches inside the
given interval. This definition makes no assertion about event chronology. -/
def vfMid915TransportMatchedPopulation (a b : ℕ) : ℤ :=
  min (vfMidFloorLiPositiveMismatchPopulation a b)
    (vfMidFloorLiNegativeMismatchPopulation a b)

def vfMid915TransportUnmatchedPositive (a b : ℕ) : ℤ :=
  vfMidFloorLiPositiveMismatchPopulation a b -
    vfMid915TransportMatchedPopulation a b

def vfMid915TransportUnmatchedNegative (a b : ℕ) : ℤ :=
  vfMidFloorLiNegativeMismatchPopulation a b -
    vfMid915TransportMatchedPopulation a b

/-- Cancellation is EXACT and cannot create extra historical NNS capacity:
every opposite-sign pair is deducted from both original populations once. -/
theorem vfMid915TransportUnmatched_signed_eq_balance
    (a b : ℕ) :
    vfMid915TransportUnmatchedPositive a b -
      vfMid915TransportUnmatchedNegative a b =
    vfMidFloorLiSignedPopulationBalance a b := by
  unfold vfMid915TransportUnmatchedPositive
    vfMid915TransportUnmatchedNegative
    vfMidFloorLiSignedPopulationBalance
  ring

theorem vfMid915TransportUnmatched_nonneg
    (a b : ℕ) :
    0 ≤ vfMid915TransportUnmatchedPositive a b ∧
      0 ≤ vfMid915TransportUnmatchedNegative a b := by
  constructor
  · unfold vfMid915TransportUnmatchedPositive
      vfMid915TransportMatchedPopulation
    exact sub_nonneg.mpr (min_le_left _ _)
  · unfold vfMid915TransportUnmatchedNegative
      vfMid915TransportMatchedPopulation
    exact sub_nonneg.mpr (min_le_right _ _)

/-- At the level of FINAL signed mass, one unmatched orientation must vanish.
This is NOT an assertion of a short-lifetime chronological pairing. -/
theorem vfMid915TransportUnmatched_one_side_zero
    (a b : ℕ) :
    vfMid915TransportUnmatchedPositive a b = 0 ∨
      vfMid915TransportUnmatchedNegative a b = 0 := by
  rcases le_total (vfMidFloorLiPositiveMismatchPopulation a b)
      (vfMidFloorLiNegativeMismatchPopulation a b) with h | h
  · left
    simp [vfMid915TransportUnmatchedPositive,
      vfMid915TransportMatchedPopulation, min_eq_left h]
  · right
    simp [vfMid915TransportUnmatchedNegative,
      vfMid915TransportMatchedPopulation, min_eq_right h]

/-- Direct moving-owner transfer to ACTUAL unmatched populations.
This is exact historical compression, not a probabilistic cancellation. -/
theorem vfMid915MovingOwnerHistory_eq_unmatchedBoundary
    {A B : ℕ} (hA : 2 ≤ A) (hAB : A ≤ B) :
    vfMid915HistoricalMovingOwnerCorrection A B =
      ((vfMid915TransportUnmatchedNegative (A ^ 2) (B ^ 2) : ℤ) : ℝ) -
      ((vfMid915TransportUnmatchedPositive (A ^ 2) (B ^ 2) : ℤ) : ℝ) := by
  rw [vfMid915HistoricalMovingOwner_eq_signedMismatch hA hAB,
    ← vfMid915TransportUnmatched_signed_eq_balance]
  push_cast
  ring

/-! ## Original anchored historical VF source, without denominator expansion -/

/-- The native complete VF-minus-actual historical seat mass contains
ONLY the signed unmatched transport mass plus the deterministic square
endpoint floorLi-VF bridge. All original owner contributions are included. -/
theorem vfMid915OriginalOddRun_eq_transportBoundary
    {A B : ℕ} (hA : 2 ≤ A) (hAB : A ≤ B) :
    vfMidOddRunSeatMass A B =
      -((vfMidFloorLiSignedPopulationBalance (A ^ 2) (B ^ 2) : ℤ) : ℝ) -
        (vfMidFloorLiVFBridge B - vfMidFloorLiVFBridge A) := by
  have hrun :=
    (vfMidDyadicVFTrackingDefect_eq_oddRunSeatMass hA hAB).symm
  have hbridge := vfMidDyadicVFTrackingDefect_eq_floorLiDefect_sub_bridgeIncrement
    hA (hA.trans hAB) hAB
  have htern :
      VFMidFloorLiPrimitiveTernaryOn (A ^ 2) (B ^ 2) :=
    vfMidFloorLiPrimitiveTernaryOn_of_four_le
      (by nlinarith : 4 ≤ A ^ 2)
  have hbal :
      vfMidFloorLiSignedPopulationBalance (A ^ 2) (B ^ 2) =
        -vfMidFloorLiDyadicPrimeDefect A B := by
    rw [vfMidFloorLiSignedPopulationBalance_eq_mismatchMass htern]
    exact vfMidFloorLiSignedMismatchMass_sq_eq_neg_dyadicPrimeDefect hAB
  rw [hrun, hbridge, hbal]
  push_cast
  ring

/-- PRODUCTION-ENDPOINT historical compression into the signed remainder of
actually unmatched floor-Li events. The historical anchor is preserved
as the one ORIGINAL D_A scalar. -/
theorem vfMid915ActualDefect_eq_anchor_add_unmatchedBoundary
    {A B : ℕ} (hA : 2 ≤ A) (hAB : A ≤ B) :
    vfMidActualPrimeEndpointDefect B =
      vfMidActualPrimeEndpointDefect A +
      ((vfMid915TransportUnmatchedPositive (A ^ 2) (B ^ 2) : ℤ) : ℝ) -
      ((vfMid915TransportUnmatchedNegative (A ^ 2) (B ^ 2) : ℤ) : ℝ) +
      (vfMidFloorLiVFBridge B - vfMidFloorLiVFBridge A) := by
  have hsource := vfMidActualPrimeEndpointDefect_eq_anchor_sub_oddRunSeatMass
    hA hAB
  have hrun := vfMid915OriginalOddRun_eq_transportBoundary hA hAB
  have hpopulation :=
    vfMid915TransportUnmatched_signed_eq_balance (A ^ 2) (B ^ 2)
  have hpopulationR :
      ((vfMid915TransportUnmatchedPositive (A ^ 2) (B ^ 2) : ℤ) : ℝ) -
        ((vfMid915TransportUnmatchedNegative (A ^ 2) (B ^ 2) : ℤ) : ℝ) =
      ((vfMidFloorLiSignedPopulationBalance (A ^ 2) (B ^ 2) : ℤ) : ℝ) := by
    exact_mod_cast hpopulation
  rw [hrun] at hsource
  linarith

/-- All historical owner interactions before B, including those preceding
the immediate half-scale run, are contained in ONE original integer backlog
plus ONE deterministic bounded bridge. -/
theorem vfMid915ActualDefect_eq_floorLiUnmatchedEndpoint
    (B : ℕ) :
    vfMidActualPrimeEndpointDefect B =
      (vfMidPrimeFloorLiBacklog B : ℝ) +
        vfMidFloorLiVFBridge B := by
  unfold vfMidActualPrimeEndpointDefect
  exact vfMidPrimeError_sq_eq_floorLiBacklog_add_bridge B

/-- Every R-th CURRENT block source is still the original integer VF charge.
No transport or historical event is inserted into this present block. -/
theorem vfMid915OriginalTotalMass_unchanged
    (R : ℕ) :
    vfMidFirstBadZeroTargetTotalMass R =
      (|vfMidActualPrimeEndpointDefect R| +
        ∑ n ∈ vfMidOddCandidateSeats R,
          |vfMidOddSignedSeatCharge R n|) ^ 2 :=
  vfMidFirstBadZeroTargetTotalMass_eq R

/-- A strictly UNIFORM deterministic square-endpoint bridge. The older
root-scale bound can be sharpened because the midpoint quadrature error
relative to Li is proved O(1) at square endpoints. -/
theorem vfMid915FloorLiVFBridge_abs_le_uniform
    {R : ℕ} (hR : 2 ≤ R) :
    |vfMidFloorLiVFBridge R| ≤
      1 + vfMidLiSquareEndpointUniformConstant := by
  have hfloor :=
    abs_liFloorPrimeCountProxy_sub_li_lt_one ((R : ℝ) ^ 2)
  have hquad := abs_vfMidLiError_sq_le_uniform (R := R) hR
  have hsplit :
      vfMidFloorLiVFBridge R =
        (liFloorPrimeCountProxy ((R : ℝ) ^ 2) -
          vfMidLogarithmicIntegralFromTwo ((R : ℝ) ^ 2)) -
        vfMidLiError ((R : ℝ) ^ 2) := by
    unfold vfMidFloorLiVFBridge vfMidLiError
    ring
  rw [hsplit]
  have htri :
      |(liFloorPrimeCountProxy ((R : ℝ) ^ 2) -
          vfMidLogarithmicIntegralFromTwo ((R : ℝ) ^ 2)) -
        vfMidLiError ((R : ℝ) ^ 2)| ≤
      |liFloorPrimeCountProxy ((R : ℝ) ^ 2) -
        vfMidLogarithmicIntegralFromTwo ((R : ℝ) ^ 2)| +
        |vfMidLiError ((R : ℝ) ^ 2)| := by
    calc
      _ = |(liFloorPrimeCountProxy ((R : ℝ) ^ 2) -
          vfMidLogarithmicIntegralFromTwo ((R : ℝ) ^ 2)) +
          (-vfMidLiError ((R : ℝ) ^ 2))| := by ring
      _ ≤ |liFloorPrimeCountProxy ((R : ℝ) ^ 2) -
          vfMidLogarithmicIntegralFromTwo ((R : ℝ) ^ 2)| +
          |-vfMidLiError ((R : ℝ) ^ 2)| := abs_add_le _ _
      _ = _ := by rw [abs_neg]
  linarith

/-- Exact first-bad HALF-SCALE interface, all historical signed owner drift
compressed to unmatched transport opposite-sign and a deterministic uniform bridge.
For B=R+1 the index ranges are the literal #915 physical run. -/
theorem vfMid915FirstBadHalfRun_eq_unmatchedTransport
    (R : ℕ) (hR : 8 ≤ R) :
    vfMidActualPrimeEndpointDefect (R + 1) =
      vfMidActualPrimeEndpointDefect (R / 2 + 1) +
      ((vfMid915TransportUnmatchedPositive
          ((R / 2 + 1) ^ 2) ((R + 1) ^ 2) : ℤ) : ℝ) -
      ((vfMid915TransportUnmatchedNegative
          ((R / 2 + 1) ^ 2) ((R + 1) ^ 2) : ℤ) : ℝ) +
      (vfMidFloorLiVFBridge (R + 1) -
        vfMidFloorLiVFBridge (R / 2 + 1)) := by
  exact vfMid915ActualDefect_eq_anchor_add_unmatchedBoundary
    (by omega : 2 ≤ R / 2 + 1)
    (by omega : R / 2 + 1 ≤ R + 1)

/-- EXACT unchanged #915 NNS capacity and final quadratic SOURCE in
unmatched boundary currency. This is the direct bridge toward hbalance:
the inequality itself is NOT asserted or proved by this identity. -/
theorem vfMid915OriginalHalfGate_eq_transportQuadratic
    (R : ℕ) (hR : 8 ≤ R) :
    vfMidFirstBadZeroTargetTotalMass R -
      2 * vfMidActualPrimeEndpointDefect (R + 1) ^ 2 =
    vfMidFirstBadZeroTargetTotalMass R -
      2 * (vfMidActualPrimeEndpointDefect (R / 2 + 1) +
        ((vfMid915TransportUnmatchedPositive
            ((R / 2 + 1) ^ 2) ((R + 1) ^ 2) : ℤ) : ℝ) -
        ((vfMid915TransportUnmatchedNegative
            ((R / 2 + 1) ^ 2) ((R + 1) ^ 2) : ℤ) : ℝ) +
        (vfMidFloorLiVFBridge (R + 1) -
          vfMidFloorLiVFBridge (R / 2 + 1))) ^ 2 := by
  rw [vfMid915FirstBadHalfRun_eq_unmatchedTransport R hR]

end RHLean.Analysis
