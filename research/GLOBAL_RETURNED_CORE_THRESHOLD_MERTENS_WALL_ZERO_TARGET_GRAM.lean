import Mathlib
import «research.GLOBAL_RETURNED_CORE_THRESHOLD_MERTENS_WALL»
import «research.LOW_OWNER_RETURNED_CORE_ZERO_TARGET_GRAM»
import «research.CANONICAL_ROUGH_Q2_TAIL_REDUCTION»

/-!
# Threshold Mertens walls in zero-target Gram currency

For every prime owner `p` and cutoff `y`, the signed p-free threshold wall

  n <= y < p*n

is already proved to have total Möbius mass `M(y)`.  The zero-target NNS Gram
identity therefore turns the *whole signed wall*, before any ownerwise norm or
absolute value, into the literal Mertens energy `M(y)^2`.

This is the arithmetic currency needed by the descending raw-parent
polarization: whichever fresh owner exposes the wall, the wall Gram is exactly
the same daughter energy.  No multiplicity, independence, Cauchy--Schwarz or
prime-counting estimate enters.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Exact target-zero Gram of one threshold wall. -/
def lowOwnerThresholdMertensWallZeroTargetGram (p y : ℕ) : ℝ :=
  zeroTargetCoPartialGram
      (lowOwnerThresholdMertensCrossingCarrier p y) realMoebiusStep -
    zeroTargetDivergentGram
      (lowOwnerThresholdMertensCrossingCarrier p y) realMoebiusStep

/-- **A threshold wall Gram is exactly the Mertens square at its cutoff.** -/
theorem lowOwnerThresholdMertensWallZeroTargetGram_eq_mertens_sq
    {p y : ℕ} (hp : p.Prime) :
    lowOwnerThresholdMertensWallZeroTargetGram p y =
      ((mertensSummatoryInt y : ℤ) : ℝ) ^ 2 := by
  unfold lowOwnerThresholdMertensWallZeroTargetGram
  rw [← zeroTarget_globalGram_reassembly]
  rw [sum_realMoebius_thresholdMertensCrossingCarrier_eq_mertens hp]

/-- At a literal q^2 daughter cutoff, the same wall Gram is exactly the
recursive daughter energy consumed by the CORR-4 terminal theorem.  The
identity is independent of the prime owner used to expose the wall. -/
theorem lowOwnerQ2ThresholdWallZeroTargetGram_eq_childEnergy
    {R q p : ℕ} (hp : p.Prime) :
    lowOwnerThresholdMertensWallZeroTargetGram p (rawQ2ChildCutoff R q) =
      rawQ2ChildEnergyReal R q := by
  rw [lowOwnerThresholdMertensWallZeroTargetGram_eq_mertens_sq hp]
  rfl

/-- Any prime-valued choice of exposing owner gives the same total low-q^2
wall energy: the canonical recursive Mertens daughter budget. -/
theorem sum_lowOwnerQ2ThresholdWallZeroTargetGram_eq_daughterEnergy
    (R : ℕ) (owner : ℕ → ℕ)
    (howner : ∀ q ∈ canonicalRoughLowQ2Owners R, (owner q).Prime) :
    (∑ q ∈ canonicalRoughLowQ2Owners R,
      lowOwnerThresholdMertensWallZeroTargetGram
        (owner q) (rawQ2ChildCutoff R q)) =
      canonicalRoughLowQ2DaughterEnergy R := by
  unfold canonicalRoughLowQ2DaughterEnergy
  apply Finset.sum_congr rfl
  intro q hq
  exact lowOwnerQ2ThresholdWallZeroTargetGram_eq_childEnergy (howner q hq)

end RHLean.Proof
