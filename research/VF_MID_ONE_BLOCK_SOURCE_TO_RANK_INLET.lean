import Mathlib
import «research.VF_MID_FULL_AFFINE_PAIR_CLASSIFIER»

/-!
# Adjacent-block VF source-to-rank inlet

This file opens the exact one-block affine carrier before any positive-energy
gate.

For the adjacent first-bad step the frozen cutoff is the current square scale
itself.  Two simplifications are exact:

* no composite can survive the wheel through R inside (R^2,(R+1)^2), because
  every composite there has least prime factor at most R;
* every odd composite is therefore in the already-processed least-owner
  sector, and stripping its owner preserves the fibre cardinality.

Consequently the processed affine mass may be reindexed losslessly from
physical composites n to their strict lower children n/p while retaining the
literal VF coefficient w_R.  Owner labels remain outside the child sum, so no
cross-owner injectivity or packet inheritance is assumed.

This is an equality-only inlet.  No norm, triangle inequality, reciprocal
weight, RH hypothesis, or lower-scale VF identification is introduced.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- **Adjacent frozen wheel has no composite survivors.**

A composite in the R-th open square block has least prime owner at most R,
hence it cannot survive the prefix wheel through R itself. -/
theorem vfMidSquareBandPrefixCompositeSurvivors_self_eq_empty
    {R : ℕ} (hR : 2 ≤ R) :
    vfMidSquareBandPrefixCompositeSurvivors R R = ∅ := by
  ext n
  simp only [Finset.mem_empty, iff_false]
  intro hn
  rcases Finset.mem_filter.mp hn with ⟨hnComp, hnSurv⟩
  have hgt :
      R < n.minFac :=
    (vfMidSquareBandComposite_survives_prefix_iff_minFac_gt
      hR hnComp).1 hnSurv
  have howner :=
    vfMidSquareBandComposite_minFac_mem_ownerPrimes hR hnComp
  have hle : n.minFac ≤ R :=
    (mem_vfMidSquareBandOwnerPrimes.mp howner).2
  omega

/-- **Adjacent frozen survivors are exactly the actual primes.** -/
theorem vfMidSquarePrefixWheelSurvivors_self_eq_primes
    {R : ℕ} (hR : 2 ≤ R) :
    vfMidSquarePrefixWheelSurvivors R R =
      vfMidSquareWheelPrimes R := by
  rw [vfMidSquarePrefixWheelSurvivors_eq_prime_union_prefixComposite
      hR le_rfl,
    vfMidSquareBandPrefixCompositeSurvivors_self_eq_empty hR]
  simp

/-- At cutoff A=R every odd least-prime owner has already been processed. -/
theorem vfMidFrozenProcessedOwnerPrimes_self_eq_allOddOwners
    (R : ℕ) :
    vfMidFrozenProcessedOwnerPrimes R R =
      vfMidSquareBandLateOwnerPrimes 2 R := by
  ext p
  simp [vfMidFrozenProcessedOwnerPrimes,
    mem_vfMidSquareBandLateOwnerPrimes,
    mem_vfMidSquareBandOwnerPrimes]

/-- Processed affine mass written directly on stripped owner children.

The coefficient remains the parent block's exact VF fractional seat weight;
the child is only a lossless reindexing coordinate at this stage. -/
def vfMidOneBlockProcessedOwnerChildCharge (R : ℕ) : ℝ :=
  ∑ p ∈ vfMidFrozenProcessedOwnerPrimes R R,
    ∑ _m ∈ vfMidSquareBandCompositeOwnerChildren R p,
      vfMidOddFractionalPrimeSeatWeight R

/-- **Lossless processed-site to child reindexing.**

This is the adjacent-block all-scale version of the 1027-style owner strip:
each least-owner fibre is moved from n to n/p with its exact multiplicity and
with the VF coefficient unchanged. -/
theorem vfMidOneBlockProcessedOwnerCharge_eq_childCharge
    (R : ℕ) :
    vfMidOneBlockProcessedOwnerCharge R =
      vfMidOneBlockProcessedOwnerChildCharge R := by
  unfold vfMidOneBlockProcessedOwnerCharge
    vfMidOneBlockProcessedOwnerAtom
    vfMidOneBlockProcessedOwnerChildCharge
  apply Finset.sum_congr rfl
  intro p _hp
  rw [Finset.sum_const, nsmul_eq_mul,
    vfMidSquareBandCompositeOwnerChildren_card]
  ring

/-- The same lossless reindexing with an arbitrary retained scalar coefficient.

This is the form needed for the historical D_R polarization: no property of the
coefficient is used. -/
theorem vfMidProcessedOwner_retainedCoefficient_reindex
    (R : ℕ) (coefficient : ℝ) :
    (∑ p ∈ vfMidFrozenProcessedOwnerPrimes R R,
      ∑ _n ∈ vfMidSquareBandCompositeOwner R p,
        coefficient * vfMidOddFractionalPrimeSeatWeight R) =
      ∑ p ∈ vfMidFrozenProcessedOwnerPrimes R R,
        ∑ _m ∈ vfMidSquareBandCompositeOwnerChildren R p,
          coefficient * vfMidOddFractionalPrimeSeatWeight R := by
  apply Finset.sum_congr rfl
  intro p _hp
  rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul,
    vfMidSquareBandCompositeOwnerChildren_card]

/-- One-block two-sector charge with the processed sector already placed on
strict lower owner children. -/
theorem vfMidTwoSectorOwnerCharge_succ_eq_primeSurvivor_add_processedChildren
    {R : ℕ} (hR : 3 ≤ R) :
    vfMidDyadicFrozenSurvivorSeatCharge R (R + 1) +
        vfMidDyadicProcessedOwnerSeatCharge R (R + 1) =
      (∑ n ∈ vfMidSquareWheelPrimes R,
        vfMidOddSignedSeatCharge R n) +
        vfMidOneBlockProcessedOwnerChildCharge R := by
  rw [vfMidDyadicFrozenSurvivorSeatCharge_succ_eq_oneBlock,
    vfMidDyadicProcessedOwnerSeatCharge_succ_eq_oneBlock,
    vfMidOneBlockProcessedOwnerCharge_eq_childCharge]
  unfold vfMidOneBlockFrozenSurvivorCharge
    vfMidSubdoublingPrefixSurvivorChargeSum
  rw [vfMidSquarePrefixWheelSurvivors_self_eq_primes
    (by omega : 2 ≤ R)]

end RHLean.Analysis
