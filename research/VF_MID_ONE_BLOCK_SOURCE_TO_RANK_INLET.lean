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
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro n hn
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
  simp only [vfMidFrozenProcessedOwnerPrimes, Finset.mem_filter]
  constructor
  · intro hp
    exact hp.1
  · intro hp
    refine ⟨hp, ?_⟩
    have hpOwner :=
      (mem_vfMidSquareBandLateOwnerPrimes.mp hp).1
    exact (mem_vfMidSquareBandOwnerPrimes.mp hpOwner).2


/-- Squarefree-active part of one processed least-owner fibre.  This is the
only part allowed to enter the Möbius/zero-target rank machinery. -/
def vfMidSquarefreeProcessedOwnerSites (R p : ℕ) : Finset ℕ :=
  (vfMidSquareBandCompositeOwner R p).filter Squarefree

/-- Squareful-dead part of one processed least-owner fibre.  These sites remain
physical VF seats but are explicitly kept outside the Möbius rank tree. -/
def vfMidSquarefulProcessedOwnerSites (R p : ℕ) : Finset ℕ :=
  (vfMidSquareBandCompositeOwner R p).filter (fun n => ¬ Squarefree n)

/-- Active processed affine charge, restricted to squarefree physical sites. -/
def vfMidOneBlockProcessedSquarefreeCharge (R : ℕ) : ℝ :=
  ∑ p ∈ vfMidFrozenProcessedOwnerPrimes R R,
    ∑ n ∈ vfMidSquarefreeProcessedOwnerSites R p,
      vfMidOddSignedSeatCharge R n

/-- Dead processed affine charge on repeated-prime/squareful physical sites. -/
def vfMidOneBlockProcessedSquarefulCharge (R : ℕ) : ℝ :=
  ∑ p ∈ vfMidFrozenProcessedOwnerPrimes R R,
    ∑ n ∈ vfMidSquarefulProcessedOwnerSites R p,
      vfMidOddSignedSeatCharge R n

/-- **Exact squarefree/squareful rectifier split.**

The physical processed source is partitioned before any zero-target or
reciprocal gate is opened.  No squareful site is sent into the Möbius tree. -/
theorem vfMidOneBlockProcessedOwnerCharge_eq_squarefree_add_squareful
    (R : ℕ) :
    vfMidOneBlockProcessedOwnerCharge R =
      vfMidOneBlockProcessedSquarefreeCharge R +
        vfMidOneBlockProcessedSquarefulCharge R := by
  unfold vfMidOneBlockProcessedOwnerCharge
    vfMidOneBlockProcessedSquarefreeCharge
    vfMidOneBlockProcessedSquarefulCharge
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _hp
  rw [vfMidOneBlockProcessedOwnerAtom_eq_siteSum]
  unfold vfMidSquarefreeProcessedOwnerSites
    vfMidSquarefulProcessedOwnerSites
  simpa only using
    (Finset.sum_filter_add_sum_filter_not
      (s := vfMidSquareBandCompositeOwner R p)
      (p := Squarefree)
      (f := vfMidOddSignedSeatCharge R)).symm

/-- Every squareful processed site carries the raw positive VF affine charge;
there is no intrinsic Möbius rectifier in `vfMidOddSignedSeatCharge`. -/
theorem vfMidOddSignedSeatCharge_eq_weight_on_squareful_processed
    {R p n : ℕ}
    (hn : n ∈ vfMidSquarefulProcessedOwnerSites R p) :
    vfMidOddSignedSeatCharge R n =
      vfMidOddFractionalPrimeSeatWeight R := by
  have hnOwner :
      n ∈ vfMidSquareBandCompositeOwner R p :=
    (Finset.mem_filter.mp hn).1
  have hnComp := vfMidSquareBandCompositeOwner_mem hnOwner
  exact vfMidOddSignedSeatCharge_of_not_prime R n hnComp.2

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


/-- **Rectified adjacent one-block source.**

The complete physical source is now visibly split into three disjoint regimes:
actual prime survivors, squarefree processed composites (active Möbius regime),
and squareful processed composites (dead Möbius regime).  The last sector is
retained explicitly rather than silently sent through the zero-target tree. -/
theorem vfMidTwoSectorOwnerCharge_succ_eq_prime_add_squarefree_add_squareful
    {R : ℕ} (hR : 3 ≤ R) :
    vfMidDyadicFrozenSurvivorSeatCharge R (R + 1) +
        vfMidDyadicProcessedOwnerSeatCharge R (R + 1) =
      (∑ n ∈ vfMidSquareWheelPrimes R,
        vfMidOddSignedSeatCharge R n) +
        vfMidOneBlockProcessedSquarefreeCharge R +
        vfMidOneBlockProcessedSquarefulCharge R := by
  rw [vfMidDyadicFrozenSurvivorSeatCharge_succ_eq_oneBlock,
    vfMidDyadicProcessedOwnerSeatCharge_succ_eq_oneBlock,
    vfMidOneBlockProcessedOwnerCharge_eq_squarefree_add_squareful]
  unfold vfMidOneBlockFrozenSurvivorCharge
    vfMidSubdoublingPrefixSurvivorChargeSum
  rw [vfMidSquarePrefixWheelSurvivors_self_eq_primes
    (by omega : 2 ≤ R)]
  ring

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


/-! ## Quadratic child-level decompression -/

/-- One processed owner atom written on its stripped child fibre, retaining the
literal current-block VF coefficient. -/
def vfMidOneBlockProcessedOwnerChildAtom (R p : ℕ) : ℝ :=
  ∑ _m ∈ vfMidSquareBandCompositeOwnerChildren R p,
    vfMidOddFractionalPrimeSeatWeight R

theorem vfMidOneBlockProcessedOwnerAtom_eq_childAtom
    (R p : ℕ) :
    vfMidOneBlockProcessedOwnerAtom R p =
      vfMidOneBlockProcessedOwnerChildAtom R p := by
  unfold vfMidOneBlockProcessedOwnerAtom
    vfMidOneBlockProcessedOwnerChildAtom
  rw [Finset.sum_const, nsmul_eq_mul,
    vfMidSquareBandCompositeOwnerChildren_card]
  ring

/-- Survivor x processed sector after the processed coordinate is stripped to
its tagged lower child. -/
def vfMidOneBlockSurvivorProcessedChildPairMass (R : ℕ) : ℝ :=
  ∑ n ∈ vfMidSquareWheelPrimes R,
    ∑ p ∈ vfMidFrozenProcessedOwnerPrimes R R,
      ∑ _m ∈ vfMidSquareBandCompositeOwnerChildren R p,
        vfMidOddSignedSeatCharge R n *
          vfMidOddFractionalPrimeSeatWeight R

/-- Processed x survivor sector on tagged lower children. -/
def vfMidOneBlockProcessedChildSurvivorPairMass (R : ℕ) : ℝ :=
  ∑ p ∈ vfMidFrozenProcessedOwnerPrimes R R,
    ∑ _n ∈ vfMidSquareBandCompositeOwnerChildren R p,
      ∑ m ∈ vfMidSquareWheelPrimes R,
        vfMidOddFractionalPrimeSeatWeight R *
          vfMidOddSignedSeatCharge R m

/-- Processed x processed sector with both owner tags retained and both physical
composites stripped to lower children. -/
def vfMidOneBlockProcessedChildProcessedChildPairMass (R : ℕ) : ℝ :=
  ∑ p ∈ vfMidFrozenProcessedOwnerPrimes R R,
    ∑ _n ∈ vfMidSquareBandCompositeOwnerChildren R p,
      ∑ q ∈ vfMidFrozenProcessedOwnerPrimes R R,
        ∑ _m ∈ vfMidSquareBandCompositeOwnerChildren R q,
          vfMidOddFractionalPrimeSeatWeight R *
            vfMidOddFractionalPrimeSeatWeight R

/-- Complete adjacent-block current-current affine bill after lossless owner
stripping of every processed composite coordinate. -/
def vfMidOneBlockChildDecompressedAffinePairLedger (R : ℕ) : ℝ :=
  (∑ n ∈ vfMidSquareWheelPrimes R,
    ∑ m ∈ vfMidSquareWheelPrimes R,
      vfMidOddSignedSeatCharge R n * vfMidOddSignedSeatCharge R m) +
    vfMidOneBlockSurvivorProcessedChildPairMass R +
    vfMidOneBlockProcessedChildSurvivorPairMass R +
    vfMidOneBlockProcessedChildProcessedChildPairMass R

/-- The survivor-survivor physical sector is already the prime-prime sector in
an adjacent block. -/
theorem vfMidOneBlockSurvivorSurvivorPairMass_eq_primePrime
    {R : ℕ} (hR : 2 ≤ R) :
    vfMidOneBlockSurvivorSurvivorPairMass R =
      ∑ n ∈ vfMidSquareWheelPrimes R,
        ∑ m ∈ vfMidSquareWheelPrimes R,
          vfMidOddSignedSeatCharge R n * vfMidOddSignedSeatCharge R m := by
  unfold vfMidOneBlockSurvivorSurvivorPairMass
  rw [vfMidSquarePrefixWheelSurvivors_self_eq_primes hR]

/-- Exact survivor x processed child reindexing. -/
theorem vfMidOneBlockSurvivorProcessedPhysicalPairMass_eq_child
    {R : ℕ} (hR : 2 ≤ R) :
    vfMidOneBlockSurvivorProcessedPhysicalPairMass R =
      vfMidOneBlockSurvivorProcessedChildPairMass R := by
  unfold vfMidOneBlockSurvivorProcessedPhysicalPairMass
    vfMidOneBlockSurvivorProcessedChildPairMass
  rw [vfMidSquarePrefixWheelSurvivors_self_eq_primes hR]
  apply Finset.sum_congr rfl
  intro n _hn
  apply Finset.sum_congr rfl
  intro p _hp
  rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul,
    vfMidSquareBandCompositeOwnerChildren_card]

/-- Exact processed child x survivor reindexing. -/
theorem vfMidOneBlockProcessedSurvivorPhysicalPairMass_eq_child
    {R : ℕ} (hR : 2 ≤ R) :
    vfMidOneBlockProcessedSurvivorPhysicalPairMass R =
      vfMidOneBlockProcessedChildSurvivorPairMass R := by
  unfold vfMidOneBlockProcessedSurvivorPhysicalPairMass
    vfMidOneBlockProcessedChildSurvivorPairMass
  rw [vfMidSquarePrefixWheelSurvivors_self_eq_primes hR]
  apply Finset.sum_congr rfl
  intro p _hp
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _hm
  rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul,
    vfMidSquareBandCompositeOwnerChildren_card]
  ring

/-- Exact processed x processed double child reindexing. -/
theorem vfMidOneBlockProcessedProcessedPhysicalPairMass_eq_child
    (R : ℕ) :
    vfMidOneBlockProcessedProcessedPhysicalPairMass R =
      vfMidOneBlockProcessedChildProcessedChildPairMass R := by
  unfold vfMidOneBlockProcessedProcessedPhysicalPairMass
    vfMidOneBlockProcessedChildProcessedChildPairMass
  apply Finset.sum_congr rfl
  intro p _hp
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _hq
  rw [Finset.sum_comm, Finset.sum_comm]
  rw [Finset.sum_const, Finset.sum_const, Finset.sum_const, Finset.sum_const,
    nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul,
    vfMidSquareBandCompositeOwnerChildren_card]
  ring

/-- **Complete current-current source-to-child equality.**

Every physical composite coordinate in the #889 current-current bill has been
stripped to a strict lower child while retaining its least-owner tag and exact
VF coefficient.  Prime coordinates are untouched. -/
theorem vfMidOneBlockCompleteAffinePairLedger_eq_childDecompressed
    {R : ℕ} (hR : 3 ≤ R) :
    vfMidOneBlockCompleteAffinePairLedger R =
      vfMidOneBlockChildDecompressedAffinePairLedger R := by
  rw [vfMidOneBlockCompleteAffinePairLedger_eq_decompressedPhysical]
  unfold vfMidOneBlockDecompressedAffinePairLedger
    vfMidOneBlockChildDecompressedAffinePairLedger
  rw [vfMidOneBlockSurvivorSurvivorPairMass_eq_primePrime
      (by omega : 2 ≤ R),
    vfMidOneBlockSurvivorProcessedPhysicalPairMass_eq_child
      (by omega : 2 ≤ R),
    vfMidOneBlockProcessedSurvivorPhysicalPairMass_eq_child
      (by omega : 2 ≤ R),
    vfMidOneBlockProcessedProcessedPhysicalPairMass_eq_child]

/-- Historical-current processed sector after the same exact child reindexing. -/
def vfMidOneBlockHistoricalProcessedChildPhysical (R : ℕ) : ℝ :=
  ∑ p ∈ vfMidFrozenProcessedOwnerPrimes R R,
    ∑ _m ∈ vfMidSquareBandCompositeOwnerChildren R p,
      vfMidActualPrimeEndpointDefect R *
        vfMidOddFractionalPrimeSeatWeight R

/-- The historical-current processed physical sector is unchanged by stripping
its least owner. -/
theorem vfMidOneBlockHistoricalProcessed_eq_child
    (R : ℕ) :
    (∑ p ∈ vfMidFrozenProcessedOwnerPrimes R R,
      ∑ n ∈ vfMidSquareBandCompositeOwner R p,
        vfMidActualPrimeEndpointDefect R * vfMidOddSignedSeatCharge R n) =
      vfMidOneBlockHistoricalProcessedChildPhysical R := by
  unfold vfMidOneBlockHistoricalProcessedChildPhysical
  apply Finset.sum_congr rfl
  intro p _hp
  calc
    (∑ n ∈ vfMidSquareBandCompositeOwner R p,
      vfMidActualPrimeEndpointDefect R * vfMidOddSignedSeatCharge R n) =
        ∑ _n ∈ vfMidSquareBandCompositeOwner R p,
          vfMidActualPrimeEndpointDefect R *
            vfMidOddFractionalPrimeSeatWeight R := by
          apply Finset.sum_congr rfl
          intro n hn
          have hnComp : n ∈ vfMidSquareBandComposites R :=
            (Finset.mem_filter.mp hn).1
          have hnNotPrime : ¬ n.Prime :=
            (Finset.mem_filter.mp hnComp).2
          rw [vfMidOddSignedSeatCharge_of_not_prime R n hnNotPrime]
    _ = ∑ _m ∈ vfMidSquareBandCompositeOwnerChildren R p,
          vfMidActualPrimeEndpointDefect R *
            vfMidOddFractionalPrimeSeatWeight R := by
          rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul,
            nsmul_eq_mul, vfMidSquareBandCompositeOwnerChildren_card]

/-- **Historical-current source-to-child equality.**

The accumulated endpoint defect remains one rigid scalar; only the current
processed composite coordinate is stripped to its strict lower child. -/
theorem vfMidOneBlockHistoricalCurrentTwoSectorPhysical_eq_prime_child
    {R : ℕ} (hR : 3 ≤ R) :
    vfMidOneBlockHistoricalCurrentTwoSectorPhysical R =
      (∑ n ∈ vfMidSquareWheelPrimes R,
        vfMidActualPrimeEndpointDefect R *
          vfMidOddSignedSeatCharge R n) +
        vfMidOneBlockHistoricalProcessedChildPhysical R := by
  unfold vfMidOneBlockHistoricalCurrentTwoSectorPhysical
  rw [vfMidSquarePrefixWheelSurvivors_self_eq_primes
      (by omega : 2 ≤ R),
    vfMidOneBlockHistoricalProcessed_eq_child]

end RHLean.Analysis
