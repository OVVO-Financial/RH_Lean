import Mathlib
import «research.VF_MID_FULL_AFFINE_PAIR_CLASSIFIER»
import «research.VF_MID_RECURSIVE_REMAINDER_BOUND»

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
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

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

/-- Every physical site in a processed least-owner fibre is composite, hence
carries the raw positive VF affine charge. -/
theorem vfMidOddSignedSeatCharge_eq_weight_on_processed_owner
    {R p n : ℕ}
    (hn : n ∈ vfMidSquareBandCompositeOwner R p) :
    vfMidOddSignedSeatCharge R n =
      vfMidOddFractionalPrimeSeatWeight R := by
  have hnComp : n ∈ vfMidSquareBandComposites R :=
    (Finset.mem_filter.mp hn).1
  have hnNotPrime : ¬ n.Prime :=
    (Finset.mem_filter.mp hnComp).2
  exact vfMidOddSignedSeatCharge_of_not_prime R n hnNotPrime

/-- Every squareful processed site carries the raw positive VF affine charge;
there is no intrinsic Möbius rectifier in `vfMidOddSignedSeatCharge`. -/
theorem vfMidOddSignedSeatCharge_eq_weight_on_squareful_processed
    {R p n : ℕ}
    (hn : n ∈ vfMidSquarefulProcessedOwnerSites R p) :
    vfMidOddSignedSeatCharge R n =
      vfMidOddFractionalPrimeSeatWeight R := by
  exact
    vfMidOddSignedSeatCharge_eq_weight_on_processed_owner
      (Finset.mem_filter.mp hn).1


/-- Squareful processed children obtained by stripping the retained least-prime
owner.  Owner labels remain outside, so repeated children across owners are not
identified. -/
def vfMidSquarefulProcessedOwnerChildren (R p : ℕ) : Finset ℕ :=
  (vfMidSquarefulProcessedOwnerSites R p).image (fun n => n / p)

/-- Stripping preserves the squareful sub-fibre cardinality. -/
theorem vfMidSquarefulProcessedOwnerChildren_card
    (R p : ℕ) :
    (vfMidSquarefulProcessedOwnerChildren R p).card =
      (vfMidSquarefulProcessedOwnerSites R p).card := by
  unfold vfMidSquarefulProcessedOwnerChildren
  apply Finset.card_image_iff.mpr
  intro a ha b hb hab
  apply vfMidSquareBandCompositeOwner_child_injOn R p
  · exact (Finset.mem_filter.mp ha).1
  · exact (Finset.mem_filter.mp hb).1
  · exact hab

/-- Every squareful processed child is a strict prior square-scale state. -/
theorem vfMidSquarefulProcessedOwnerChild_lt_square
    {R p m : ℕ} (hR : 3 ≤ R)
    (hm : m ∈ vfMidSquarefulProcessedOwnerChildren R p) :
    m < R ^ 2 := by
  rcases Finset.mem_image.mp hm with ⟨n, hn, rfl⟩
  exact
    vfMidSquareBandCompositeOwner_child_lt_square hR
      (Finset.mem_filter.mp hn).1

/-- The squareful physical charge can be reindexed exactly onto strict owner
children while retaining the VF coefficient. -/
theorem vfMidOneBlockProcessedSquarefulCharge_eq_childCharge
    (R : ℕ) :
    vfMidOneBlockProcessedSquarefulCharge R =
      ∑ p ∈ vfMidFrozenProcessedOwnerPrimes R R,
        ∑ _m ∈ vfMidSquarefulProcessedOwnerChildren R p,
          vfMidOddFractionalPrimeSeatWeight R := by
  unfold vfMidOneBlockProcessedSquarefulCharge
  apply Finset.sum_congr rfl
  intro p _hp
  calc
    (∑ n ∈ vfMidSquarefulProcessedOwnerSites R p,
      vfMidOddSignedSeatCharge R n) =
      ∑ _n ∈ vfMidSquarefulProcessedOwnerSites R p,
        vfMidOddFractionalPrimeSeatWeight R := by
          apply Finset.sum_congr rfl
          intro n hn
          exact vfMidOddSignedSeatCharge_eq_weight_on_squareful_processed hn
    _ =
      ∑ _m ∈ vfMidSquarefulProcessedOwnerChildren R p,
        vfMidOddFractionalPrimeSeatWeight R := by
          rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul,
            vfMidSquarefulProcessedOwnerChildren_card]

/-- Total squareful processed population is bounded by the full processed owner
population, hence by the R odd candidate seats. -/
theorem vfMidSquarefulProcessedOwnerPopulation_le_R
    (R : ℕ) (hR : 3 ≤ R) :
    (∑ p ∈ vfMidFrozenProcessedOwnerPrimes R R,
      (vfMidSquarefulProcessedOwnerSites R p).card) ≤ R := by
  have hsub :
      (∑ p ∈ vfMidFrozenProcessedOwnerPrimes R R,
        (vfMidSquarefulProcessedOwnerSites R p).card) ≤
      ∑ p ∈ vfMidFrozenProcessedOwnerPrimes R R,
        (vfMidSquareBandCompositeOwner R p).card := by
    apply Finset.sum_le_sum
    intro p _hp
    unfold vfMidSquarefulProcessedOwnerSites
    exact Finset.card_filter_le _ _
  have hcount :=
    vfMidSquarePrefixWheelSurvivors_card_add_processedOwnerCards_eq_root
      (A := R) (R := R) hR le_rfl
  omega

/-- **Squareful dead-regime charge bound.**

This is deliberately kept outside #891.  It is a direct affine owner-child
residual with an explicit linear bound. -/
theorem vfMidOneBlockProcessedSquarefulCharge_le_three_div_log_four_mul
    (R : ℕ) (hR : 3 ≤ R) :
    vfMidOneBlockProcessedSquarefulCharge R ≤
      (3 / Real.log 4) * (R : ℝ) := by
  have hw0 :=
    vfMidOddFractionalPrimeSeatWeight_nonneg R (by omega : 2 ≤ R)
  have hwu :=
    vfMidOddFractionalPrimeSeatWeight_le_three_div_log_four
      R (by omega : 2 ≤ R)
  have hpopNat := vfMidSquarefulProcessedOwnerPopulation_le_R R hR
  have hpop :
      (∑ p ∈ vfMidFrozenProcessedOwnerPrimes R R,
        ((vfMidSquarefulProcessedOwnerSites R p).card : ℝ)) ≤
        (R : ℝ) := by
    exact_mod_cast hpopNat
  have hpop0 :
      0 ≤
        ∑ p ∈ vfMidFrozenProcessedOwnerPrimes R R,
          ((vfMidSquarefulProcessedOwnerSites R p).card : ℝ) := by
    positivity
  unfold vfMidOneBlockProcessedSquarefulCharge
  calc
    (∑ p ∈ vfMidFrozenProcessedOwnerPrimes R R,
      ∑ n ∈ vfMidSquarefulProcessedOwnerSites R p,
        vfMidOddSignedSeatCharge R n) =
      vfMidOddFractionalPrimeSeatWeight R *
        (∑ p ∈ vfMidFrozenProcessedOwnerPrimes R R,
          ((vfMidSquarefulProcessedOwnerSites R p).card : ℝ)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro p _hp
            calc
              (∑ n ∈ vfMidSquarefulProcessedOwnerSites R p,
                vfMidOddSignedSeatCharge R n) =
                ∑ _n ∈ vfMidSquarefulProcessedOwnerSites R p,
                  vfMidOddFractionalPrimeSeatWeight R := by
                    apply Finset.sum_congr rfl
                    intro n hn
                    exact
                      vfMidOddSignedSeatCharge_eq_weight_on_squareful_processed hn
              _ = vfMidOddFractionalPrimeSeatWeight R *
                  ((vfMidSquarefulProcessedOwnerSites R p).card : ℝ) := by
                    rw [Finset.sum_const, nsmul_eq_mul]
                    ring
    _ ≤ (3 / Real.log 4) *
        (∑ p ∈ vfMidFrozenProcessedOwnerPrimes R R,
          ((vfMidSquarefulProcessedOwnerSites R p).card : ℝ)) :=
      mul_le_mul_of_nonneg_right hwu hpop0
    _ ≤ (3 / Real.log 4) * (R : ℝ) := by
      have hC0 : (0 : ℝ) ≤ 3 / Real.log 4 := by
        have hlog : 0 < Real.log 4 := Real.log_pos (by norm_num)
        positivity
      exact mul_le_mul_of_nonneg_left hpop hC0


/-- Processed affine mass written directly on stripped owner children.

The coefficient remains the parent block's exact VF fractional seat weight;
the child is only a lossless reindexing coordinate at this stage. -/
def vfMidOneBlockProcessedOwnerChildCharge (R : ℕ) : ℝ :=
  ∑ p ∈ vfMidFrozenProcessedOwnerPrimes R R,
    ∑ _m ∈ vfMidSquareBandCompositeOwnerChildren R p,
      vfMidOddFractionalPrimeSeatWeight R

/-- Möbius-active processed children.  The rectifier is applied *after* the
least-owner strip, which is the coordinate actually used by the rank tree. -/
def vfMidSquarefreeProcessedOwnerChildren (R p : ℕ) : Finset ℕ :=
  (vfMidSquareBandCompositeOwnerChildren R p).filter Squarefree

/-- Processed children still carrying a repeated-prime collision after the
least-owner strip.  These remain outside the nonzero-Möbius clock. -/
def vfMidSquarefulProcessedOwnerChildrenAfterStrip (R p : ℕ) : Finset ℕ :=
  (vfMidSquareBandCompositeOwnerChildren R p).filter (fun m => ¬ Squarefree m)

/-- Exact post-strip rectifier partition of the processed physical charge. -/
theorem vfMidOneBlockProcessedOwnerChildCharge_eq_active_add_dead
    (R : ℕ) :
    vfMidOneBlockProcessedOwnerChildCharge R =
      (∑ p ∈ vfMidFrozenProcessedOwnerPrimes R R,
        ∑ _m ∈ vfMidSquarefreeProcessedOwnerChildren R p,
          vfMidOddFractionalPrimeSeatWeight R) +
      (∑ p ∈ vfMidFrozenProcessedOwnerPrimes R R,
        ∑ _m ∈ vfMidSquarefulProcessedOwnerChildrenAfterStrip R p,
          vfMidOddFractionalPrimeSeatWeight R) := by
  unfold vfMidOneBlockProcessedOwnerChildCharge
    vfMidSquarefreeProcessedOwnerChildren
    vfMidSquarefulProcessedOwnerChildrenAfterStrip
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _hp
  simpa only using
    (Finset.sum_filter_add_sum_filter_not
      (s := vfMidSquareBandCompositeOwnerChildren R p)
      (p := Squarefree)
      (f := fun _m => vfMidOddFractionalPrimeSeatWeight R)).symm

/-- Site coefficient which turns the squarefree stripped child back into the
literal positive VF processed charge. -/
def vfMidProcessedActiveChildRetainedCoefficient (R m : ℕ) : ℝ :=
  vfMidOddFractionalPrimeSeatWeight R * realMoebiusStep m

/-- **Exact active-child weight preservation.**

On a squarefree stripped child, the retained coefficient times the Möbius sign
is exactly the original physical +w_R processed-seat charge. -/
theorem vfMidProcessedActiveChildRetainedCoefficient_mul_moebius
    {R p m : ℕ}
    (hm : m ∈ vfMidSquarefreeProcessedOwnerChildren R p) :
    vfMidProcessedActiveChildRetainedCoefficient R m *
        realMoebiusStep m =
      vfMidOddFractionalPrimeSeatWeight R := by
  have hsq : Squarefree m := (Finset.mem_filter.mp hm).2
  have hmu0 : μ m ≠ 0 :=
    ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hsq
  rcases ArithmeticFunction.moebius_eq_or m with h0 | h1 | hm1
  · exact (hmu0 h0).elim
  · unfold vfMidProcessedActiveChildRetainedCoefficient realMoebiusStep
    rw [h1]
    norm_num
  · unfold vfMidProcessedActiveChildRetainedCoefficient realMoebiusStep
    rw [hm1]
    norm_num

/-- Every active stripped processed child lies on the exact nonzero-Möbius
common clock at the adjacent endpoint R+1. -/
theorem vfMidSquarefreeProcessedOwnerChild_mem_lowOwnerCarrier_succ
    {R p m : ℕ} (hR : 3 ≤ R)
    (hm : m ∈ vfMidSquarefreeProcessedOwnerChildren R p) :
    m ∈ lowOwnerNonzeroMobiusCarrier (R + 1) := by
  rcases Finset.mem_filter.mp hm with ⟨hmChild, hsq⟩
  unfold lowOwnerNonzeroMobiusCarrier
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_Icc.mpr
    constructor
    · exact Nat.one_le_iff_ne_zero.mpr hsq.ne_zero
    · have hlt :=
        vfMidSquareBandCompositeOwnerChildren_lt_square hR hmChild
      have hnext : R ^ 2 < (R + 1) ^ 2 :=
        Nat.pow_lt_pow_left (by omega : R < R + 1) (by omega)
      have hmnext : m < (R + 1) ^ 2 := hlt.trans hnext
      unfold squareRootEndpoint
      omega
  · unfold realMoebiusStep
    exact_mod_cast
      (ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hsq)

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



private theorem vfMidActualPrimeEndpointDefect_eq_squareEndpointError_inlet
    {R : ℕ} (hR : 2 ≤ R) :
    vfMidActualPrimeEndpointDefect R = vfMidSquareEndpointError R := by
  unfold vfMidActualPrimeEndpointDefect
  rw [← vfMidDirectSquareEndpointError_eq_vfMidPrimeError hR]
  rfl

private theorem vfMidTwoSectorOwnerCharge_eq_endpointDefect_sub_inlet
    {A B : ℕ}
    (hA : 3 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A) :
    vfMidDyadicFrozenSurvivorSeatCharge A B +
        vfMidDyadicProcessedOwnerSeatCharge A B =
      vfMidActualPrimeEndpointDefect A -
        vfMidActualPrimeEndpointDefect B := by
  calc
    vfMidDyadicFrozenSurvivorSeatCharge A B +
        vfMidDyadicProcessedOwnerSeatCharge A B =
      vfMidOddRunSeatMass A B :=
        (vfMidOddRunSeatMass_eq_frozenSurvivor_add_processedOwnerCharge
          hA hBA).symm
    _ = -(vfMidSquareEndpointError B - vfMidSquareEndpointError A) :=
      vfMidOddRunSeatMass_eq_neg_endpointError_increment
        A B (by omega : 2 ≤ A) hAB
    _ = vfMidActualPrimeEndpointDefect A -
        vfMidActualPrimeEndpointDefect B := by
      rw [vfMidActualPrimeEndpointDefect_eq_squareEndpointError_inlet
            (R := A) (by omega : 2 ≤ A),
          vfMidActualPrimeEndpointDefect_eq_squareEndpointError_inlet
            (R := B) (by omega : 2 ≤ B)]
      ring

/-- **Exact three-stream quadratic snap-back.**

The terminal correlation bill is the quadratic energy of the rectified physical
source with all prime/squarefree/squareful cross terms intact.  No branch is
bounded separately here. -/
theorem vfMidCorrelationEnergy_eq_rectifiedThreeStream
    {R : ℕ} (hR : 3 ≤ R) :
    2 * vfMidSquareEndpointAccumulationCorrelation R +
        vfMidSquareBandError R ^ 2 =
      ((∑ n ∈ vfMidSquareWheelPrimes R,
          vfMidOddSignedSeatCharge R n) +
        vfMidOneBlockProcessedSquarefreeCharge R +
        vfMidOneBlockProcessedSquarefulCharge R) ^ 2 -
      2 * vfMidActualPrimeEndpointDefect R *
        ((∑ n ∈ vfMidSquareWheelPrimes R,
            vfMidOddSignedSeatCharge R n) +
          vfMidOneBlockProcessedSquarefreeCharge R +
          vfMidOneBlockProcessedSquarefulCharge R) := by
  have hcorr :=
    vfMidSquareEndpointError_sq_succ_eq_correlation
      R (by omega : 2 ≤ R)
  have hD0 :=
    vfMidActualPrimeEndpointDefect_eq_squareEndpointError_inlet
      (R := R) (by omega : 2 ≤ R)
  have hD1 :=
    vfMidActualPrimeEndpointDefect_eq_squareEndpointError_inlet
      (R := R + 1) (by omega : 2 ≤ R + 1)
  have hT :=
    vfMidTwoSectorOwnerCharge_eq_endpointDefect_sub_inlet
      (A := R) (B := R + 1) hR (by omega) (by omega)
  have hsplit :=
    vfMidTwoSectorOwnerCharge_succ_eq_prime_add_squarefree_add_squareful hR
  have hsource :
      (∑ n ∈ vfMidSquareWheelPrimes R,
          vfMidOddSignedSeatCharge R n) +
          vfMidOneBlockProcessedSquarefreeCharge R +
          vfMidOneBlockProcessedSquarefulCharge R =
        vfMidActualPrimeEndpointDefect R -
          vfMidActualPrimeEndpointDefect (R + 1) := by
    exact hsplit.symm.trans hT
  rw [← hD0, ← hD1] at hcorr
  rw [hsource]
  nlinarith



/-- Elementary one-seat ceiling: from R=3 onward the VF fractional odd-seat
weight is at most one.  This uses only the midpoint formula and
`log 2 > 0.9`. -/
theorem vfMidOddFractionalPrimeSeatWeight_le_one_of_three_le
    (R : ℕ) (hR : 3 ≤ R) :
    vfMidOddFractionalPrimeSeatWeight R ≤ 1 := by
  have hRpos : (0 : ℝ) < (R : ℝ) := by
    exact_mod_cast (by omega : 0 < R)
  have hR3 : (3 : ℝ) ≤ (R : ℝ) := by
    exact_mod_cast hR
  have hm12 : (12 : ℝ) ≤ vfMidBandMidpoint R := by
    unfold vfMidBandMidpoint
    nlinarith
  have hlog3 : (1 : ℝ) < Real.log 3 := by
    rw [show (1 : ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
    apply Real.log_lt_log (Real.exp_pos 1)
    exact Real.exp_one_lt_d9.trans (by norm_num)
  have hlog4eq : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    calc
      Real.log (4 : ℝ) = Real.log ((2 : ℝ) ^ 2) := by norm_num
      _ = (2 : ℕ) * Real.log 2 := by rw [Real.log_pow]
      _ = 2 * Real.log 2 := by norm_num
  have hlog4 : (4 / 3 : ℝ) < Real.log 4 := by
    rw [hlog4eq]
    have h2 := Real.log_two_gt_d9
    nlinarith
  have hlog12eq :
      Real.log (12 : ℝ) = Real.log 3 + Real.log 4 := by
    calc
      Real.log (12 : ℝ) = Real.log ((3 : ℝ) * 4) := by norm_num
      _ = Real.log 3 + Real.log 4 := by
        rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0)
          (by norm_num : (4 : ℝ) ≠ 0)]
  have hlog12 : (7 / 3 : ℝ) < Real.log 12 := by
    rw [hlog12eq]
    nlinarith
  have hlogmono :
      Real.log (12 : ℝ) ≤ Real.log (vfMidBandMidpoint R) :=
    Real.log_le_log (by norm_num) hm12
  have hlog : (7 / 3 : ℝ) < Real.log (vfMidBandMidpoint R) :=
    hlog12.trans_le hlogmono
  have hlogpos : 0 < Real.log (vfMidBandMidpoint R) := by
    linarith
  have hnum :
      2 * (R : ℝ) + 1 ≤ (R : ℝ) * (7 / 3 : ℝ) := by
    nlinarith
  have hmul :
      (R : ℝ) * (7 / 3 : ℝ) <
        (R : ℝ) * Real.log (vfMidBandMidpoint R) :=
    mul_lt_mul_of_pos_left hlog hRpos
  have hnumlog :
      2 * (R : ℝ) + 1 <
        (R : ℝ) * Real.log (vfMidBandMidpoint R) :=
    hnum.trans_lt hmul
  unfold vfMidOddFractionalPrimeSeatWeight vfMidBandMass
  rw [div_le_iff₀ hRpos]
  simp only [one_mul]
  rw [div_le_iff₀ hlogpos]
  exact le_of_lt hnumlog

/-- Prime stream of the adjacent one-block physical source. -/
def vfMidOneBlockPrimeSeatCharge (R : ℕ) : ℝ :=
  ∑ n ∈ vfMidSquareWheelPrimes R, vfMidOddSignedSeatCharge R n

/-- The prime stream is nonpositive. -/
theorem vfMidOneBlockPrimeSeatCharge_nonpos
    (R : ℕ) (hR : 3 ≤ R) :
    vfMidOneBlockPrimeSeatCharge R ≤ 0 := by
  unfold vfMidOneBlockPrimeSeatCharge
  apply Finset.sum_nonpos
  intro n hn
  have hp : n.Prime := (Finset.mem_filter.mp hn).2
  rw [vfMidOddSignedSeatCharge_of_prime R n hp]
  have hw :=
    vfMidOddFractionalPrimeSeatWeight_le_one_of_three_le R hR
  linarith

/-- The squareful processed stream is nonnegative. -/
theorem vfMidOneBlockProcessedSquarefulCharge_nonneg
    (R : ℕ) (hR : 2 ≤ R) :
    0 ≤ vfMidOneBlockProcessedSquarefulCharge R := by
  unfold vfMidOneBlockProcessedSquarefulCharge
  apply Finset.sum_nonneg
  intro p _hp
  apply Finset.sum_nonneg
  intro n hn
  rw [vfMidOddSignedSeatCharge_eq_weight_on_squareful_processed hn]
  exact vfMidOddFractionalPrimeSeatWeight_nonneg R hR

/-- Upper-escape rectifier identity.

Writing the full one-step source as active plus squareful-dead, the exact
quadratic bill differs from the active bill by the restoring term
minus Q times (2 D_(R+1) plus Q). -/
theorem vfMidCorrelationEnergy_eq_upperActive_sub_squarefulRestoring
    {R : ℕ} (hR : 3 ≤ R) :
    2 * vfMidSquareEndpointAccumulationCorrelation R +
        vfMidSquareBandError R ^ 2 =
      (vfMidOneBlockPrimeSeatCharge R +
          vfMidOneBlockProcessedSquarefreeCharge R) ^ 2 -
        2 * vfMidActualPrimeEndpointDefect R *
          (vfMidOneBlockPrimeSeatCharge R +
            vfMidOneBlockProcessedSquarefreeCharge R) -
        vfMidOneBlockProcessedSquarefulCharge R *
          (2 * vfMidActualPrimeEndpointDefect (R + 1) +
            vfMidOneBlockProcessedSquarefulCharge R) := by
  have henergy := vfMidCorrelationEnergy_eq_rectifiedThreeStream hR
  have hT :=
    vfMidTwoSectorOwnerCharge_eq_endpointDefect_sub_inlet
      (A := R) (B := R + 1) hR (by omega) (by omega)
  have hsplit :=
    vfMidTwoSectorOwnerCharge_succ_eq_prime_add_squarefree_add_squareful hR
  have hsource :
      vfMidOneBlockPrimeSeatCharge R +
          vfMidOneBlockProcessedSquarefreeCharge R +
          vfMidOneBlockProcessedSquarefulCharge R =
        vfMidActualPrimeEndpointDefect R -
          vfMidActualPrimeEndpointDefect (R + 1) := by
    change
      (∑ n ∈ vfMidSquareWheelPrimes R,
          vfMidOddSignedSeatCharge R n) +
          vfMidOneBlockProcessedSquarefreeCharge R +
          vfMidOneBlockProcessedSquarefulCharge R =
        vfMidActualPrimeEndpointDefect R -
          vfMidActualPrimeEndpointDefect (R + 1)
    exact hsplit.symm.trans hT
  change
    2 * vfMidSquareEndpointAccumulationCorrelation R +
        vfMidSquareBandError R ^ 2 =
      (vfMidOneBlockPrimeSeatCharge R +
          vfMidOneBlockProcessedSquarefreeCharge R +
          vfMidOneBlockProcessedSquarefulCharge R) ^ 2 -
        2 * vfMidActualPrimeEndpointDefect R *
          (vfMidOneBlockPrimeSeatCharge R +
            vfMidOneBlockProcessedSquarefreeCharge R +
            vfMidOneBlockProcessedSquarefulCharge R) at henergy
  nlinarith

/-- At an upper endpoint the squareful branch can only lower the terminal
quadratic bill. -/
theorem vfMidCorrelationEnergy_le_upperActive_of_endpoint_nonneg
    {R : ℕ} (hR : 3 ≤ R)
    (hB : 0 ≤ vfMidActualPrimeEndpointDefect (R + 1)) :
    2 * vfMidSquareEndpointAccumulationCorrelation R +
        vfMidSquareBandError R ^ 2 ≤
      (vfMidOneBlockPrimeSeatCharge R +
          vfMidOneBlockProcessedSquarefreeCharge R) ^ 2 -
        2 * vfMidActualPrimeEndpointDefect R *
          (vfMidOneBlockPrimeSeatCharge R +
            vfMidOneBlockProcessedSquarefreeCharge R) := by
  rw [vfMidCorrelationEnergy_eq_upperActive_sub_squarefulRestoring hR]
  have hQ :=
    vfMidOneBlockProcessedSquarefulCharge_nonneg R (by omega : 2 ≤ R)
  nlinarith

/-- Lower-escape rectifier identity.

Writing the full source as composite plus prime, the exact correction from the
prime stream is P times (-2 D_(R+1) minus P). -/
theorem vfMidCorrelationEnergy_eq_lowerActive_add_primeRestoring
    {R : ℕ} (hR : 3 ≤ R) :
    2 * vfMidSquareEndpointAccumulationCorrelation R +
        vfMidSquareBandError R ^ 2 =
      (vfMidOneBlockProcessedSquarefreeCharge R +
          vfMidOneBlockProcessedSquarefulCharge R) ^ 2 -
        2 * vfMidActualPrimeEndpointDefect R *
          (vfMidOneBlockProcessedSquarefreeCharge R +
            vfMidOneBlockProcessedSquarefulCharge R) +
        vfMidOneBlockPrimeSeatCharge R *
          (-2 * vfMidActualPrimeEndpointDefect (R + 1) -
            vfMidOneBlockPrimeSeatCharge R) := by
  have henergy := vfMidCorrelationEnergy_eq_rectifiedThreeStream hR
  have hT :=
    vfMidTwoSectorOwnerCharge_eq_endpointDefect_sub_inlet
      (A := R) (B := R + 1) hR (by omega) (by omega)
  have hsplit :=
    vfMidTwoSectorOwnerCharge_succ_eq_prime_add_squarefree_add_squareful hR
  have hsource :
      vfMidOneBlockPrimeSeatCharge R +
          vfMidOneBlockProcessedSquarefreeCharge R +
          vfMidOneBlockProcessedSquarefulCharge R =
        vfMidActualPrimeEndpointDefect R -
          vfMidActualPrimeEndpointDefect (R + 1) := by
    change
      (∑ n ∈ vfMidSquareWheelPrimes R,
          vfMidOddSignedSeatCharge R n) +
          vfMidOneBlockProcessedSquarefreeCharge R +
          vfMidOneBlockProcessedSquarefulCharge R =
        vfMidActualPrimeEndpointDefect R -
          vfMidActualPrimeEndpointDefect (R + 1)
    exact hsplit.symm.trans hT
  change
    2 * vfMidSquareEndpointAccumulationCorrelation R +
        vfMidSquareBandError R ^ 2 =
      (vfMidOneBlockPrimeSeatCharge R +
          vfMidOneBlockProcessedSquarefreeCharge R +
          vfMidOneBlockProcessedSquarefulCharge R) ^ 2 -
        2 * vfMidActualPrimeEndpointDefect R *
          (vfMidOneBlockPrimeSeatCharge R +
            vfMidOneBlockProcessedSquarefreeCharge R +
            vfMidOneBlockProcessedSquarefulCharge R) at henergy
  nlinarith

/-- At a lower endpoint the negative prime stream can only lower the terminal
quadratic bill. -/
theorem vfMidCorrelationEnergy_le_lowerComposite_of_endpoint_nonpos
    {R : ℕ} (hR : 3 ≤ R)
    (hB : vfMidActualPrimeEndpointDefect (R + 1) ≤ 0) :
    2 * vfMidSquareEndpointAccumulationCorrelation R +
        vfMidSquareBandError R ^ 2 ≤
      (vfMidOneBlockProcessedSquarefreeCharge R +
          vfMidOneBlockProcessedSquarefulCharge R) ^ 2 -
        2 * vfMidActualPrimeEndpointDefect R *
          (vfMidOneBlockProcessedSquarefreeCharge R +
            vfMidOneBlockProcessedSquarefulCharge R) := by
  rw [vfMidCorrelationEnergy_eq_lowerActive_add_primeRestoring hR]
  have hP := vfMidOneBlockPrimeSeatCharge_nonpos R hR
  nlinarith


/-- **Exact lower-escape composite descent.**

At the adjacent cutoff every odd composite owner is already processed.  The
entire positive composite stream is therefore the native recursive lower-scale
charge plus only the terminal-owner and scale-transfer remainders.  The
restoring prime channel has disappeared before this identity is used. -/
theorem vfMidOneBlockProcessedOwnerCharge_eq_native_add_terminal_add_transfer
    (R : ℕ) (hR : 7 ≤ R) :
    vfMidOneBlockProcessedOwnerCharge R =
      vfMidRecursiveAggregateNativeCharge R +
        vfMidTerminalParentCharge R +
        vfMidRecursiveAggregateRemainder R := by
  have hdef :=
    vfMidOddCompositeTrackingDefect_eq_nativeCharge_add_descentRemainder R hR
  have howners :=
    vfMidOddCompositeTrackingDefect_eq_ownerCharges_sub_primeCharge
      R (by omega : 2 ≤ R)
  have hself :=
    vfMidFrozenProcessedOwnerPrimes_self_eq_allOddOwners R
  have hprocessed :
      vfMidOneBlockProcessedOwnerCharge R =
        ∑ p ∈ vfMidSquareBandLateOwnerPrimes 2 R,
          vfMidOddFractionalPrimeSeatWeight R *
            ((vfMidSquareBandCompositeOwner R p).card : ℝ) := by
    unfold vfMidOneBlockProcessedOwnerCharge vfMidOneBlockProcessedOwnerAtom
    rw [hself]
  have hprime :
      vfMidOriginalPrimeCharge R =
        (1 - vfMidOddFractionalPrimeSeatWeight R) *
          (vfMidIntegerBlockPrimeSupply R : ℝ) := rfl
  rw [← hprocessed] at howners
  unfold vfMidNativeDescentRemainder at hdef
  rw [hprime] at hdef
  linarith

/-- The lower-active branch in the terminal energy may therefore be rewritten
entirely in native descendant plus explicit terminal/transfer currency. -/
theorem vfMidLowerCompositeCharge_eq_nativeDescent
    (R : ℕ) (hR : 7 ≤ R) :
    vfMidOneBlockProcessedSquarefreeCharge R +
        vfMidOneBlockProcessedSquarefulCharge R =
      vfMidRecursiveAggregateNativeCharge R +
        vfMidTerminalParentCharge R +
        vfMidRecursiveAggregateRemainder R := by
  rw [← vfMidOneBlockProcessedOwnerCharge_eq_squarefree_add_squareful]
  exact vfMidOneBlockProcessedOwnerCharge_eq_native_add_terminal_add_transfer R hR


/-! ## Radial-square slack absorbs the explicit native descent remainder -/

private lemma vfMid_inlet_log_three_gt_one :
    (1 : ℝ) < Real.log 3 := by
  rw [show (1 : ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
  apply Real.log_lt_log (Real.exp_pos 1)
  exact Real.exp_one_lt_d9.trans (by norm_num)

/-- From R >= 7, one radial-square step has a completely elementary linear
lower bound.  No PNT or prime-distribution estimate enters. -/
theorem vfMidSyntheticRadialScale_sq_increment_gt_25_div_3_mul
    (R : ℕ) (hR : 7 ≤ R) :
    (25 / 3 : ℝ) * (R : ℝ) <
      vfMidSyntheticRadialScale (R + 1) ^ 2 -
        vfMidSyntheticRadialScale R ^ 2 := by
  have hR0 : (0 : ℝ) < (R : ℝ) := by
    exact_mod_cast (by omega : 0 < R)
  have hRp0 : (0 : ℝ) < ((R + 1 : ℕ) : ℝ) := by positivity
  have hlog2 : (2 / 3 : ℝ) < Real.log 2 := by
    have h := Real.log_two_gt_d9
    nlinarith
  have hlog3 : (1 : ℝ) < Real.log 3 :=
    vfMid_inlet_log_three_gt_one
  have hlog6eq :
      Real.log (6 : ℝ) = Real.log 2 + Real.log 3 := by
    calc
      Real.log (6 : ℝ) = Real.log ((2 : ℝ) * 3) := by norm_num
      _ = Real.log 2 + Real.log 3 := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
          (by norm_num : (3 : ℝ) ≠ 0)]
  have hlog6 : (5 / 3 : ℝ) < Real.log 6 := by
    rw [hlog6eq]
    nlinarith
  have h6R : (6 : ℝ) ≤ (R : ℝ) := by
    exact_mod_cast (by omega : 6 ≤ R)
  have hlog6R : Real.log (6 : ℝ) ≤ Real.log (R : ℝ) :=
    Real.log_le_log (by norm_num) h6R
  have hlogR : (5 / 3 : ℝ) < Real.log (R : ℝ) :=
    hlog6.trans_le hlog6R
  have hlog8eq :
      Real.log (8 : ℝ) = 3 * Real.log 2 := by
    calc
      Real.log (8 : ℝ) = Real.log ((2 : ℝ) ^ 3) := by norm_num
      _ = (3 : ℕ) * Real.log 2 := by rw [Real.log_pow]
      _ = 3 * Real.log 2 := by norm_num
  have hlog8 : (2 : ℝ) < Real.log 8 := by
    rw [hlog8eq]
    nlinarith
  have h8Rp : (8 : ℝ) ≤ ((R + 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 8 ≤ R + 1)
  have hlog8Rp :
      Real.log (8 : ℝ) ≤ Real.log ((R + 1 : ℕ) : ℝ) :=
    Real.log_le_log (by norm_num) h8Rp
  have hlogRp : (2 : ℝ) < Real.log ((R + 1 : ℕ) : ℝ) :=
    hlog8.trans_le hlog8Rp
  have hratioPos :
      0 < (R : ℝ) / ((R + 1 : ℕ) : ℝ) :=
    div_pos hR0 hRp0
  have hrecip :=
    Real.log_le_sub_one_of_pos hratioPos
  rw [Real.log_div hR0.ne' hRp0.ne'] at hrecip
  have hratioId :
      (R : ℝ) / ((R + 1 : ℕ) : ℝ) - 1 =
        -(1 / ((R + 1 : ℕ) : ℝ)) := by
    push_cast
    field_simp [hR0.ne', hRp0.ne']
    ring
  rw [hratioId] at hrecip
  have hstep :
      1 / ((R + 1 : ℕ) : ℝ) ≤
        Real.log ((R + 1 : ℕ) : ℝ) - Real.log (R : ℝ) := by
    linarith
  have hhalfRatio :
      (1 / 2 : ℝ) ≤ (R : ℝ) / ((R + 1 : ℕ) : ℝ) := by
    rw [div_le_iff₀ hRp0]
    push_cast
    nlinarith
  have hstepMul :
      (1 / 2 : ℝ) ≤
        (R : ℝ) *
          (Real.log ((R + 1 : ℕ) : ℝ) - Real.log (R : ℝ)) := by
    calc
      (1 / 2 : ℝ) ≤ (R : ℝ) / ((R + 1 : ℕ) : ℝ) := hhalfRatio
      _ = (R : ℝ) * (1 / ((R + 1 : ℕ) : ℝ)) := by ring
      _ ≤ (R : ℝ) *
          (Real.log ((R + 1 : ℕ) : ℝ) - Real.log (R : ℝ)) :=
        mul_le_mul_of_nonneg_left hstep hR0.le
  have hdiff :
      (5 / 2 : ℝ) <
        vfMidSyntheticRadialScale (R + 1) -
          vfMidSyntheticRadialScale R := by
    unfold vfMidSyntheticRadialScale
    have hid :
        (((R + 1 : ℕ) : ℝ) *
              Real.log ((R + 1 : ℕ) : ℝ) -
            (R : ℝ) * Real.log (R : ℝ)) =
          Real.log ((R + 1 : ℕ) : ℝ) +
            (R : ℝ) *
              (Real.log ((R + 1 : ℕ) : ℝ) - Real.log (R : ℝ)) := by
      push_cast
      ring
    rw [hid]
    linarith
  have hrhoR :
      (5 / 3 : ℝ) * (R : ℝ) <
        vfMidSyntheticRadialScale R := by
    unfold vfMidSyntheticRadialScale
    exact mul_lt_mul_of_pos_left hlogR hR0
  have hrhoRp :
      (5 / 3 : ℝ) * (R : ℝ) <
        vfMidSyntheticRadialScale (R + 1) := by
    unfold vfMidSyntheticRadialScale
    have h53Rp :
        (5 / 3 : ℝ) * (R : ℝ) <
          (5 / 3 : ℝ) * ((R + 1 : ℕ) : ℝ) := by
      push_cast
      nlinarith
    have h53log :
        (5 / 3 : ℝ) < Real.log ((R + 1 : ℕ) : ℝ) := by
      linarith
    have hmul :
        (5 / 3 : ℝ) * ((R + 1 : ℕ) : ℝ) <
          ((R + 1 : ℕ) : ℝ) *
            Real.log ((R + 1 : ℕ) : ℝ) := by
      have := mul_lt_mul_of_pos_left h53log hRp0
      nlinarith
    exact h53Rp.trans hmul
  have hsum :
      (10 / 3 : ℝ) * (R : ℝ) <
        vfMidSyntheticRadialScale (R + 1) +
          vfMidSyntheticRadialScale R := by
    linarith
  have htenPos : (0 : ℝ) < (10 / 3) * (R : ℝ) := by positivity
  have hdiffPos :
      0 < vfMidSyntheticRadialScale (R + 1) -
        vfMidSyntheticRadialScale R := by
    linarith
  calc
    (25 / 3 : ℝ) * (R : ℝ) =
        (5 / 2 : ℝ) * ((10 / 3 : ℝ) * (R : ℝ)) := by ring
    _ < (vfMidSyntheticRadialScale (R + 1) -
          vfMidSyntheticRadialScale R) *
        ((10 / 3 : ℝ) * (R : ℝ)) :=
      mul_lt_mul_of_pos_right hdiff htenPos
    _ < (vfMidSyntheticRadialScale (R + 1) -
          vfMidSyntheticRadialScale R) *
        (vfMidSyntheticRadialScale (R + 1) +
          vfMidSyntheticRadialScale R) :=
      mul_lt_mul_of_pos_left hsum hdiffPos
    _ = vfMidSyntheticRadialScale (R + 1) ^ 2 -
        vfMidSyntheticRadialScale R ^ 2 := by ring

/-- The explicit native-descent remainder is strictly smaller than one
radial-square increment **as a linear scalar**.

This theorem is diagnostic only.  The terminal bill contains
`(G_native + Rem)^2 - 2 D_R (G_native + Rem)`, so this estimate does not
license squaring `Rem` separately or charging it independently to the same
radial-square increment.  The signed `G_native + Rem` coupling must be
preserved. -/
theorem abs_vfMidNativeDescentRemainder_lt_radial_sq_increment
    (R : ℕ) (hR : 7 ≤ R) :
    |vfMidNativeDescentRemainder R| <
      vfMidSyntheticRadialScale (R + 1) ^ 2 -
        vfMidSyntheticRadialScale R ^ 2 := by
  have hrem :=
    abs_vfMidNativeDescentRemainder_le_linear R hR
  have hlog4 : (5 / 4 : ℝ) < Real.log 4 := by
    have h2 := Real.log_two_gt_d9
    have hpow : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      calc
        Real.log (4 : ℝ) = Real.log ((2 : ℝ) ^ 2) := by norm_num
        _ = (2 : ℕ) * Real.log 2 := by rw [Real.log_pow]
        _ = 2 * Real.log 2 := by norm_num
    rw [hpow]
    nlinarith
  have hlogPos : 0 < Real.log 4 := by linarith
  have hdiv : 9 / Real.log 4 < (36 / 5 : ℝ) := by
    rw [div_lt_iff₀ hlogPos]
    nlinarith
  have hC : 1 + 9 / Real.log 4 < (41 / 5 : ℝ) := by
    linarith
  have hR0 : (0 : ℝ) < (R : ℝ) := by
    exact_mod_cast (by omega : 0 < R)
  have hrem41 :
      |vfMidNativeDescentRemainder R| <
        (41 / 5 : ℝ) * (R : ℝ) := by
    calc
      |vfMidNativeDescentRemainder R| ≤
          (1 + 9 / Real.log 4) * (R : ℝ) := hrem
      _ < (41 / 5 : ℝ) * (R : ℝ) :=
        mul_lt_mul_of_pos_right hC hR0
  have hconst :
      (41 / 5 : ℝ) * (R : ℝ) <
        (25 / 3 : ℝ) * (R : ℝ) := by
    have : (41 / 5 : ℝ) < 25 / 3 := by norm_num
    exact mul_lt_mul_of_pos_right this hR0
  have hrad :=
    vfMidSyntheticRadialScale_sq_increment_gt_25_div_3_mul R hR
  exact hrem41.trans (hconst.trans hrad)

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
  calc
    (∑ m ∈ vfMidSquareBandCompositeOwner R p,
      vfMidOddSignedSeatCharge R n * vfMidOddSignedSeatCharge R m) =
      ∑ _m ∈ vfMidSquareBandCompositeOwner R p,
        vfMidOddSignedSeatCharge R n *
          vfMidOddFractionalPrimeSeatWeight R := by
            apply Finset.sum_congr rfl
            intro m hm
            rw [vfMidOddSignedSeatCharge_eq_weight_on_processed_owner hm]
    _ = ∑ _m ∈ vfMidSquareBandCompositeOwnerChildren R p,
        vfMidOddSignedSeatCharge R n *
          vfMidOddFractionalPrimeSeatWeight R := by
            rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul,
              nsmul_eq_mul, vfMidSquareBandCompositeOwnerChildren_card]

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
  calc
    (∑ n ∈ vfMidSquareBandCompositeOwner R p,
      ∑ m ∈ vfMidSquareWheelPrimes R,
        vfMidOddSignedSeatCharge R n * vfMidOddSignedSeatCharge R m) =
      ∑ _n ∈ vfMidSquareBandCompositeOwner R p,
        ∑ m ∈ vfMidSquareWheelPrimes R,
          vfMidOddFractionalPrimeSeatWeight R *
            vfMidOddSignedSeatCharge R m := by
              apply Finset.sum_congr rfl
              intro n hn
              apply Finset.sum_congr rfl
              intro m _hm
              rw [vfMidOddSignedSeatCharge_eq_weight_on_processed_owner hn]
    _ = ∑ _n ∈ vfMidSquareBandCompositeOwnerChildren R p,
        ∑ m ∈ vfMidSquareWheelPrimes R,
          vfMidOddFractionalPrimeSeatWeight R *
            vfMidOddSignedSeatCharge R m := by
              rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul,
                nsmul_eq_mul, vfMidSquareBandCompositeOwnerChildren_card]

/-- Exact processed x processed double child reindexing. -/
theorem vfMidOneBlockProcessedProcessedPhysicalPairMass_eq_child
    (R : ℕ) :
    vfMidOneBlockProcessedProcessedPhysicalPairMass R =
      vfMidOneBlockProcessedChildProcessedChildPairMass R := by
  unfold vfMidOneBlockProcessedProcessedPhysicalPairMass
    vfMidOneBlockProcessedChildProcessedChildPairMass
  apply Finset.sum_congr rfl
  intro p _hp
  calc
    (∑ n ∈ vfMidSquareBandCompositeOwner R p,
      ∑ q ∈ vfMidFrozenProcessedOwnerPrimes R R,
        ∑ m ∈ vfMidSquareBandCompositeOwner R q,
          vfMidOddSignedSeatCharge R n * vfMidOddSignedSeatCharge R m) =
      ∑ _n ∈ vfMidSquareBandCompositeOwner R p,
        ∑ q ∈ vfMidFrozenProcessedOwnerPrimes R R,
          ∑ _m ∈ vfMidSquareBandCompositeOwner R q,
            vfMidOddFractionalPrimeSeatWeight R *
              vfMidOddFractionalPrimeSeatWeight R := by
                apply Finset.sum_congr rfl
                intro n hn
                apply Finset.sum_congr rfl
                intro q _hq
                apply Finset.sum_congr rfl
                intro m hm
                rw [vfMidOddSignedSeatCharge_eq_weight_on_processed_owner hn,
                  vfMidOddSignedSeatCharge_eq_weight_on_processed_owner hm]
    _ = ∑ _n ∈ vfMidSquareBandCompositeOwner R p,
        ∑ q ∈ vfMidFrozenProcessedOwnerPrimes R R,
          ∑ _m ∈ vfMidSquareBandCompositeOwnerChildren R q,
            vfMidOddFractionalPrimeSeatWeight R *
              vfMidOddFractionalPrimeSeatWeight R := by
                apply Finset.sum_congr rfl
                intro _n _hn
                apply Finset.sum_congr rfl
                intro q _hq
                rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul,
                  nsmul_eq_mul, vfMidSquareBandCompositeOwnerChildren_card]
    _ = ∑ _n ∈ vfMidSquareBandCompositeOwnerChildren R p,
        ∑ q ∈ vfMidFrozenProcessedOwnerPrimes R R,
          ∑ _m ∈ vfMidSquareBandCompositeOwnerChildren R q,
            vfMidOddFractionalPrimeSeatWeight R *
              vfMidOddFractionalPrimeSeatWeight R := by
                rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul,
                  nsmul_eq_mul, vfMidSquareBandCompositeOwnerChildren_card]

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
