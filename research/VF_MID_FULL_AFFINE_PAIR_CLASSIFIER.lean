import Mathlib
import «research.VF_MID_FIRST_BAD_AFFINE_OWNER_SPLICE»

/-!
# Full affine pair classifier for one VF square block

The terminal first-bad argument must not square the survivor and processed
sectors separately.  This file therefore keeps the complete #888 affine carrier
intact and expands its square only after the exact signed linear reassembly.

The four tagged sectors are:

* survivor x survivor;
* survivor x processed-owner;
* processed-owner x survivor;
* processed-owner x processed-owner.

No inequality, norm, absolute value, or carrier enlargement occurs here.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- The literal frozen-survivor charge on the single block `[R,R+1)`. -/
def vfMidOneBlockFrozenSurvivorCharge (R : ℕ) : ℝ :=
  vfMidSubdoublingPrefixSurvivorChargeSum R R

/-- One already-processed least-owner contribution on the single block. -/
def vfMidOneBlockProcessedOwnerAtom (R p : ℕ) : ℝ :=
  vfMidOddFractionalPrimeSeatWeight R *
    ((vfMidSquareBandCompositeOwner R p).card : ℝ)

/-- The complete processed least-owner charge on the single block. -/
def vfMidOneBlockProcessedOwnerCharge (R : ℕ) : ℝ :=
  ∑ p ∈ vfMidFrozenProcessedOwnerPrimes R R,
    vfMidOneBlockProcessedOwnerAtom R p

/-- The dyadic frozen charge specializes exactly to the one-block charge. -/
theorem vfMidDyadicFrozenSurvivorSeatCharge_succ_eq_oneBlock
    (R : ℕ) :
    vfMidDyadicFrozenSurvivorSeatCharge R (R + 1) =
      vfMidOneBlockFrozenSurvivorCharge R := by
  simp [vfMidDyadicFrozenSurvivorSeatCharge,
    vfMidOneBlockFrozenSurvivorCharge]

/-- The dyadic processed charge specializes exactly to its one-block owner sum. -/
theorem vfMidDyadicProcessedOwnerSeatCharge_succ_eq_oneBlock
    (R : ℕ) :
    vfMidDyadicProcessedOwnerSeatCharge R (R + 1) =
      vfMidOneBlockProcessedOwnerCharge R := by
  simp [vfMidDyadicProcessedOwnerSeatCharge,
    vfMidOneBlockProcessedOwnerCharge,
    vfMidOneBlockProcessedOwnerAtom]

/-- Exact #888 two-sector charge in one-block notation. -/
theorem vfMidTwoSectorOwnerCharge_succ_eq_oneBlock_sum
    (R : ℕ) :
    vfMidDyadicFrozenSurvivorSeatCharge R (R + 1) +
        vfMidDyadicProcessedOwnerSeatCharge R (R + 1) =
      vfMidOneBlockFrozenSurvivorCharge R +
        vfMidOneBlockProcessedOwnerCharge R := by
  rw [vfMidDyadicFrozenSurvivorSeatCharge_succ_eq_oneBlock,
    vfMidDyadicProcessedOwnerSeatCharge_succ_eq_oneBlock]

/-- Survivor x survivor sector. -/
def vfMidOneBlockSurvivorSurvivorPairMass (R : ℕ) : ℝ :=
  ∑ n ∈ vfMidSquarePrefixWheelSurvivors R R,
    ∑ m ∈ vfMidSquarePrefixWheelSurvivors R R,
      vfMidOddSignedSeatCharge R n * vfMidOddSignedSeatCharge R m

/-- Survivor x processed-owner sector, retaining the processed owner label. -/
def vfMidOneBlockSurvivorProcessedPairMass (R : ℕ) : ℝ :=
  ∑ n ∈ vfMidSquarePrefixWheelSurvivors R R,
    ∑ p ∈ vfMidFrozenProcessedOwnerPrimes R R,
      vfMidOddSignedSeatCharge R n * vfMidOneBlockProcessedOwnerAtom R p

/-- Processed-owner x survivor sector.  Kept separately so the four-sector
classifier is an exact ordered-pair partition before any commutative collapse. -/
def vfMidOneBlockProcessedSurvivorPairMass (R : ℕ) : ℝ :=
  ∑ p ∈ vfMidFrozenProcessedOwnerPrimes R R,
    ∑ n ∈ vfMidSquarePrefixWheelSurvivors R R,
      vfMidOneBlockProcessedOwnerAtom R p * vfMidOddSignedSeatCharge R n

/-- Processed-owner x processed-owner sector with both owner labels retained. -/
def vfMidOneBlockProcessedProcessedPairMass (R : ℕ) : ℝ :=
  ∑ p ∈ vfMidFrozenProcessedOwnerPrimes R R,
    ∑ q ∈ vfMidFrozenProcessedOwnerPrimes R R,
      vfMidOneBlockProcessedOwnerAtom R p *
        vfMidOneBlockProcessedOwnerAtom R q

/-- Complete ordered pair ledger of the two-sector affine carrier. -/
def vfMidOneBlockCompleteAffinePairLedger (R : ℕ) : ℝ :=
  vfMidOneBlockSurvivorSurvivorPairMass R +
    vfMidOneBlockSurvivorProcessedPairMass R +
    vfMidOneBlockProcessedSurvivorPairMass R +
    vfMidOneBlockProcessedProcessedPairMass R

theorem vfMidOneBlockSurvivorSurvivorPairMass_eq_sq
    (R : ℕ) :
    vfMidOneBlockSurvivorSurvivorPairMass R =
      vfMidOneBlockFrozenSurvivorCharge R ^ 2 := by
  unfold vfMidOneBlockSurvivorSurvivorPairMass
    vfMidOneBlockFrozenSurvivorCharge
    vfMidSubdoublingPrefixSurvivorChargeSum
  rw [← Finset.sum_mul_sum]
  ring

theorem vfMidOneBlockSurvivorProcessedPairMass_eq_mul
    (R : ℕ) :
    vfMidOneBlockSurvivorProcessedPairMass R =
      vfMidOneBlockFrozenSurvivorCharge R *
        vfMidOneBlockProcessedOwnerCharge R := by
  unfold vfMidOneBlockSurvivorProcessedPairMass
    vfMidOneBlockFrozenSurvivorCharge
    vfMidSubdoublingPrefixSurvivorChargeSum
    vfMidOneBlockProcessedOwnerCharge
  rw [← Finset.sum_mul_sum]

theorem vfMidOneBlockProcessedSurvivorPairMass_eq_mul
    (R : ℕ) :
    vfMidOneBlockProcessedSurvivorPairMass R =
      vfMidOneBlockProcessedOwnerCharge R *
        vfMidOneBlockFrozenSurvivorCharge R := by
  unfold vfMidOneBlockProcessedSurvivorPairMass
    vfMidOneBlockFrozenSurvivorCharge
    vfMidSubdoublingPrefixSurvivorChargeSum
    vfMidOneBlockProcessedOwnerCharge
  rw [← Finset.sum_mul_sum]

theorem vfMidOneBlockProcessedProcessedPairMass_eq_sq
    (R : ℕ) :
    vfMidOneBlockProcessedProcessedPairMass R =
      vfMidOneBlockProcessedOwnerCharge R ^ 2 := by
  unfold vfMidOneBlockProcessedProcessedPairMass
    vfMidOneBlockProcessedOwnerCharge
  rw [← Finset.sum_mul_sum]
  ring

/-- **Unified weight-preserving four-sector classifier.**

The complete ordered pair ledger is literally the square of the full #888
two-sector signed charge.  Every survivor/processed cross term is present before
any inequality is introduced. -/
theorem vfMidOneBlockCompleteAffinePairLedger_eq_twoSector_sq
    (R : ℕ) :
    vfMidOneBlockCompleteAffinePairLedger R =
      (vfMidDyadicFrozenSurvivorSeatCharge R (R + 1) +
        vfMidDyadicProcessedOwnerSeatCharge R (R + 1)) ^ 2 := by
  rw [vfMidTwoSectorOwnerCharge_succ_eq_oneBlock_sum]
  unfold vfMidOneBlockCompleteAffinePairLedger
  rw [vfMidOneBlockSurvivorSurvivorPairMass_eq_sq,
    vfMidOneBlockSurvivorProcessedPairMass_eq_mul,
    vfMidOneBlockProcessedSurvivorPairMass_eq_mul,
    vfMidOneBlockProcessedProcessedPairMass_eq_sq]
  ring

/-- On the actual one-block VF carrier the complete affine pair ledger is exactly
the raw band-error square. -/
theorem vfMidOneBlockCompleteAffinePairLedger_eq_bandError_sq
    {R : ℕ} (hR : 3 ≤ R) :
    vfMidOneBlockCompleteAffinePairLedger R =
      vfMidSquareBandError R ^ 2 := by
  have hrun :=
    vfMidOddRunSeatMass_eq_frozenSurvivor_add_processedOwnerCharge
      (A := R) (B := R + 1) hR (by omega : R + 1 ≤ 2 * R)
  have hcharge :
      vfMidDyadicFrozenSurvivorSeatCharge R (R + 1) +
          vfMidDyadicProcessedOwnerSeatCharge R (R + 1) =
        -vfMidSquareBandError R := by
    calc
      vfMidDyadicFrozenSurvivorSeatCharge R (R + 1) +
          vfMidDyadicProcessedOwnerSeatCharge R (R + 1) =
        vfMidOddRunSeatMass R (R + 1) := hrun.symm
      _ = vfMidOddBlockSeatMass R := by
        simp [vfMidOddRunSeatMass]
      _ = -vfMidSquareBandError R :=
        vfMidOddBlockSeatMass_eq_neg_bandError R (by omega : 2 ≤ R)
  rw [vfMidOneBlockCompleteAffinePairLedger_eq_twoSector_sq, hcharge]
  ring

end RHLean.Analysis
