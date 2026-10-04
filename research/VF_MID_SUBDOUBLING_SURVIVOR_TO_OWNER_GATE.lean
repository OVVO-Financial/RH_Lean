import Mathlib
import «research.VF_MID_OPTIMAL_BASE_FIRST_CROSSING_TRIGGER»
import «research.GLOBAL_RETURNED_CORE_FIRST_OWNER_ARBITRARY_SITE_CELLS»
import «research.GLOBAL_RETURNED_CORE_SIGNED_INCIDENCE_ENERGY_GATE»
import «research.GLOBAL_RETURNED_CORE_ZERO_TARGET_GEOMETRIC_TREE_BUDGET»

/-!
# VF subdoubling survivor packet to returned-core owner gate

The post-#885 seam is a carrier identification, not a new cancellation law.

This file starts with the exact quadratic entrance.  The frozen-wheel survivor
Mobius mass already has a zero-target pair dictionary on exactly the same
physical carrier.  Summing that pointwise dictionary first within a pair of
square blocks and then over the complete subdoubling run puts the #885 signed
survivor packet directly into the returned-core zero-target pair currency
before any norm, reciprocal weight, or owner-energy estimate is used.

The next stage will reindex this restricted pair currency through the existing
arbitrary-site first-owner Fubini and then consume the already-compiled signed
incidence gate.  No new descent mechanism is introduced here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- **Exact block-pair entrance into zero-target currency.**

The zero-target Gram on two frozen survivor blocks is literally the product of
their signed Mobius masses.  This is just finite Fubini plus the compiled
zero-target pair product identity. -/
theorem vfMidZeroTargetCubeCrossGram_eq_survivorMobiusMass_mul
    (A R S : ℕ) :
    vfMidZeroTargetCubeCrossGram A R S =
      (vfMidSquareBandPrefixSurvivorMobiusMassReal A R : ℂ) *
        (vfMidSquareBandPrefixSurvivorMobiusMassReal A S : ℂ) := by
  unfold vfMidZeroTargetCubeCrossGram
    vfMidSquareBandPrefixSurvivorMobiusMassReal
  simp_rw [RHLean.Proof.postRootZeroTargetPairExcess_eq_weight]
  unfold realMoebiusStep
  push_cast
  rw [Finset.sum_mul_sum]

/-- Zero-target Gram accumulated over every ordered pair of square blocks in
one frozen-wheel dyadic run. -/
def vfMidDyadicPrefixZeroTargetGram (A B : ℕ) : ℂ :=
  ∑ R ∈ Finset.Ico A B,
    ∑ S ∈ Finset.Ico A B,
      vfMidZeroTargetCubeCrossGram A R S

/-- **Exact dyadic quadratic entrance.**

The square of the #885 frozen survivor Mobius packet is exactly the complete
zero-target Gram on that same run.  No diagonal is discarded and no absolute
value is taken. -/
theorem vfMidDyadicPrefixZeroTargetGram_eq_survivorMobiusMass_sq
    (A B : ℕ) :
    vfMidDyadicPrefixZeroTargetGram A B =
      (vfMidDyadicPrefixSurvivorMobiusMassReal A B : ℂ) ^ 2 := by
  unfold vfMidDyadicPrefixZeroTargetGram
  simp_rw [vfMidZeroTargetCubeCrossGram_eq_survivorMobiusMass_mul]
  rw [← Finset.sum_mul_sum]
  unfold vfMidDyadicPrefixSurvivorMobiusMassReal
  push_cast
  ring

end RHLean.Analysis
