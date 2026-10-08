import Mathlib
import «research.VF_MID_FIRST_BAD_RESTORING_DECOMPOSITION»
import «research.GLOBAL_RETURNED_CORE_FIRST_OWNER_ARBITRARY_SITE_CELLS»
import «research.GLOBAL_RETURNED_CORE_OWNER_TWO_CLIPPED_EXIT»
import «research.GLOBAL_RETURNED_CORE_VIRTUAL_OWNER_HALF_GATE»

/-!
# Weighted first-bad first-owner Fubini

Only the green physical-carrier, retained-scale, and arbitrary-site gate slice
of #900 (commit 1bf2b6c89ecf32484710eed1f0ae1fad37e2ca84) is transplanted here.
The failing terminal theorem and completed-tree program are not imported.

The physical clock is R+1 throughout the VF specialization.  The actual source
retains its diagonal and squareful restoring correction.  The original #897
denominator retains the absolute mass of every odd seat.  First-owner cell
capacities are absolute pair masses, not the sum of local half-gate squares
and not the bare #903 no-persistence safe mass.
-/

noncomputable section
open scoped BigOperators
namespace RHLean.Analysis
open RHLean.Arithmetic RHLean.Proof
attribute [local instance] Classical.propDecidable

/-! ## Previously compiled dependency slice -/

theorem vfMidSquarefreeProcessedOwnerSites_pairwiseDisjoint
    (R : ℕ) :
    Set.PairwiseDisjoint
      (↑(vfMidFrozenProcessedOwnerPrimes R R))
      (vfMidSquarefreeProcessedOwnerSites R) := by
  intro p _hp q _hq hpq
  change Disjoint
    (vfMidSquarefreeProcessedOwnerSites R p)
    (vfMidSquarefreeProcessedOwnerSites R q)
  rw [Finset.disjoint_left]
  intro n hnp hnq
  have hpmin :
      n.minFac = p :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hnp).1).2
  have hqmin :
      n.minFac = q :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hnq).1).2
  exact hpq (hpmin.symm.trans hqmin)

def vfMidOneBlockProcessedSquarefreePhysicalCarrier
    (R : ℕ) : Finset ℕ :=
  (vfMidFrozenProcessedOwnerPrimes R R).biUnion
    (vfMidSquarefreeProcessedOwnerSites R)

theorem vfMidProcessedSquarefreePhysicalCarrier_sum_eq_charge
    (R : ℕ) :
    (∑ n ∈ vfMidOneBlockProcessedSquarefreePhysicalCarrier R,
      vfMidOddSignedSeatCharge R n) =
      vfMidOneBlockProcessedSquarefreeCharge R := by
  unfold vfMidOneBlockProcessedSquarefreePhysicalCarrier
    vfMidOneBlockProcessedSquarefreeCharge
  rw [Finset.sum_biUnion
    (vfMidSquarefreeProcessedOwnerSites_pairwiseDisjoint R)]

theorem vfMidSquareWheelPrimes_disjoint_processedSquarefreePhysical
    (R : ℕ) :
    Disjoint
      (vfMidSquareWheelPrimes R)
      (vfMidOneBlockProcessedSquarefreePhysicalCarrier R) := by
  rw [Finset.disjoint_left]
  intro n hnPrime hnProcessed
  have hnP : n.Prime := (Finset.mem_filter.mp hnPrime).2
  rcases Finset.mem_biUnion.mp hnProcessed with ⟨p, _hp, hnp⟩
  have hnOwner := (Finset.mem_filter.mp hnp).1
  have hnComp := (Finset.mem_filter.mp hnOwner).1
  have hnNotPrime : ¬ n.Prime := (Finset.mem_filter.mp hnComp).2
  exact hnNotPrime hnP

def vfMidOneBlockActivePhysicalCarrier (R : ℕ) : Finset ℕ :=
  vfMidSquareWheelPrimes R ∪
    vfMidOneBlockProcessedSquarefreePhysicalCarrier R

theorem vfMidOneBlockActivePhysicalCarrier_sum_eq_activeSource
    (R : ℕ) :
    (∑ n ∈ vfMidOneBlockActivePhysicalCarrier R,
      vfMidOddSignedSeatCharge R n) =
      vfMidOneBlockPrimeSeatCharge R +
        vfMidOneBlockProcessedSquarefreeCharge R := by
  unfold vfMidOneBlockActivePhysicalCarrier
  rw [Finset.sum_union
    (vfMidSquareWheelPrimes_disjoint_processedSquarefreePhysical R)]
  rw [vfMidProcessedSquarefreePhysicalCarrier_sum_eq_charge]
  rfl

theorem vfMidOneBlockActivePhysicalCarrier_subset_lowOwner_succ
    {R : ℕ} :
    vfMidOneBlockActivePhysicalCarrier R ⊆
      lowOwnerNonzeroMobiusCarrier (R + 1) := by
  intro n hn
  rcases Finset.mem_union.mp hn with hnPrime | hnProcessed
  · have hnSite := (Finset.mem_filter.mp hnPrime).1
    have hnP : n.Prime := (Finset.mem_filter.mp hnPrime).2
    have hnIoo := Finset.mem_Ioo.mp hnSite
    unfold lowOwnerNonzeroMobiusCarrier
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_Icc.mpr
      constructor
      · omega
      · unfold squareRootEndpoint
        omega
    · unfold realMoebiusStep
      rw [ArithmeticFunction.moebius_apply_prime hnP]
      norm_num
  · rcases Finset.mem_biUnion.mp hnProcessed with ⟨p, _hp, hnp⟩
    have hnSq : Squarefree n := (Finset.mem_filter.mp hnp).2
    have hnOwner := (Finset.mem_filter.mp hnp).1
    have hnComp := (Finset.mem_filter.mp hnOwner).1
    have hnSite := (Finset.mem_filter.mp hnComp).1
    have hnIoo := Finset.mem_Ioo.mp hnSite
    unfold lowOwnerNonzeroMobiusCarrier
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_Icc.mpr
      constructor
      · omega
      · unfold squareRootEndpoint
        omega
    · unfold realMoebiusStep
      exact_mod_cast
        (ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hnSq)

theorem vfMidOneBlockActivePhysicalCarrier_mem_squareBandSites
    {R n : ℕ}
    (hn : n ∈ vfMidOneBlockActivePhysicalCarrier R) :
    n ∈ vfMidSquareBandSites R := by
  unfold vfMidOneBlockActivePhysicalCarrier at hn
  rcases Finset.mem_union.mp hn with hnPrime | hnProcessed
  · have hnSite : n ∈ vfMidSquareWheelSites R :=
      (Finset.mem_filter.mp hnPrime).1
    simpa [vfMidSquareWheelSites, vfMidSquareBandSites] using hnSite
  · rcases Finset.mem_biUnion.mp hnProcessed with ⟨p, _hp, hnp⟩
    have hnOwner : n ∈ vfMidSquareBandCompositeOwner R p :=
      (Finset.mem_filter.mp hnp).1
    have hnComp : n ∈ vfMidSquareBandComposites R :=
      (Finset.mem_filter.mp hnOwner).1
    exact (Finset.mem_filter.mp hnComp).1

theorem vfMidOneBlockActivePhysical_two_mul_gt_endpoint
    {R n : ℕ} (hR : 3 ≤ R)
    (hn : n ∈ vfMidOneBlockActivePhysicalCarrier R) :
    squareRootEndpoint (R + 1) < 2 * n := by
  have hnBand :=
    vfMidOneBlockActivePhysicalCarrier_mem_squareBandSites hn
  have hnLow : R ^ 2 < n := by
    exact (Finset.mem_Ioo.mp hnBand).1
  have h2R : 2 * R ≤ R ^ 2 := by
    calc
      2 * R ≤ R * R := Nat.mul_le_mul_right R (by omega : 2 ≤ R)
      _ = R ^ 2 := by ring
  have hend :
      squareRootEndpoint (R + 1) = R ^ 2 + 2 * R := by
    unfold squareRootEndpoint
    have hexpand :
        (R + 1) ^ 2 = R ^ 2 + 2 * R + 1 := by ring
    rw [hexpand]
    omega
  rw [hend]
  omega

theorem lowOwnerZeroFrequencyMobiusWeight_eq_one_on_vfMidActivePhysical
    {R n : ℕ} (hR : 3 ≤ R)
    (hn : n ∈ vfMidOneBlockActivePhysicalCarrier R) :
    lowOwnerZeroFrequencyMobiusWeight (R + 1) n = 1 := by
  exact
    lowOwnerZeroFrequencyMobiusWeight_eq_one_of_ownerTwo_clipped
      (R := R + 1) (a := n) (by omega : 2 ≤ R + 1)
      (vfMidOneBlockActivePhysical_two_mul_gt_endpoint hR hn)

theorem lowOwnerFirstOwnerDirichletBaseSite_eq_moebius_on_vfMidActivePhysical
    {R n : ℕ} (hR : 3 ≤ R)
    (hn : n ∈ vfMidOneBlockActivePhysicalCarrier R) :
    lowOwnerFirstOwnerDirichletBaseSite (R + 1) n =
      realMoebiusStep n := by
  have hnCar :
      n ∈ lowOwnerNonzeroMobiusCarrier (R + 1) :=
    vfMidOneBlockActivePhysicalCarrier_subset_lowOwner_succ hn
  have hnX :
      n ≤ squareRootEndpoint (R + 1) :=
    (Finset.mem_Icc.mp (Finset.mem_filter.mp hnCar).1).2
  unfold lowOwnerFirstOwnerDirichletBaseSite
  rw [lowOwnerPhysicalDirichletWeight_eq_weight_of_le hnX,
    lowOwnerZeroFrequencyMobiusWeight_eq_one_on_vfMidActivePhysical hR hn]
  ring

theorem lowOwnerFirstOwnerDirichletReturnedChildSite_div_eq_moebius_on_vfMidActivePhysical
    {R p b : ℕ} {sig : Finset ℕ}
    (hR : 3 ≤ R) (hp : p.Prime)
    (hbActive : b ∈ vfMidOneBlockActivePhysicalCarrier R)
    (hbChild : b ∈ lowOwnerFirstOwnerChildFiber (R + 1) p sig) :
    lowOwnerFirstOwnerDirichletReturnedChildSite
        (R + 1) p (b / p) =
      realMoebiusStep (b / p) := by
  have hcAdm :
      b / p ∈ lowOwnerFirstOwnerAdmittedBaseFiber (R + 1) p sig :=
    lowOwnerFirstOwner_div_mem_admitted_of_child hp hbChild
  have hbDvd : p ∣ b :=
    (Finset.mem_filter.mp hbChild).2.2
  have hcancel : p * (b / p) = b :=
    Nat.mul_div_cancel' hbDvd
  rw [lowOwnerFirstOwnerDirichletReturnedChildSite_eq_returned_of_admitted hcAdm]
  rw [hcancel,
    lowOwnerZeroFrequencyMobiusWeight_eq_one_on_vfMidActivePhysical hR hbActive]
  ring

theorem vfMidOneBlockActivePhysical_mem_clippedBase
    {R p a : ℕ} {sig : Finset ℕ}
    (hR : 3 ≤ R) (hp : p.Prime)
    (haActive : a ∈ vfMidOneBlockActivePhysicalCarrier R)
    (haBase : a ∈ lowOwnerFirstOwnerBaseFiber (R + 1) p sig) :
    a ∈ lowOwnerFirstOwnerClippedBaseFiber (R + 1) p sig := by
  unfold lowOwnerFirstOwnerClippedBaseFiber
  apply Finset.mem_filter.mpr
  refine ⟨haBase, ?_⟩
  have htwo :=
    vfMidOneBlockActivePhysical_two_mul_gt_endpoint hR haActive
  have h2p : 2 * a ≤ p * a :=
    Nat.mul_le_mul_right a hp.two_le
  exact htwo.trans_le h2p

def vfMidOneBlockActivePhysicalSite (R n : ℕ) : ℝ :=
  if n ∈ vfMidOneBlockActivePhysicalCarrier R then
    vfMidOddSignedSeatCharge R n
  else 0

theorem vfMidOneBlockActivePhysicalSite_sum_eq_activeSource
    {R : ℕ} :
    (∑ n ∈ lowOwnerNonzeroMobiusCarrier (R + 1),
      vfMidOneBlockActivePhysicalSite R n) =
      vfMidOneBlockPrimeSeatCharge R +
        vfMidOneBlockProcessedSquarefreeCharge R := by
  have hsub :=
    vfMidOneBlockActivePhysicalCarrier_subset_lowOwner_succ (R := R)
  have hzero :
      ∀ n ∈ lowOwnerNonzeroMobiusCarrier (R + 1),
        n ∉ vfMidOneBlockActivePhysicalCarrier R →
          vfMidOneBlockActivePhysicalSite R n = 0 := by
    intro n _hn hnot
    simp [vfMidOneBlockActivePhysicalSite, hnot]
  have hs :=
    Finset.sum_subset hsub hzero
  have hinside :
      (∑ n ∈ vfMidOneBlockActivePhysicalCarrier R,
        vfMidOneBlockActivePhysicalSite R n) =
      ∑ n ∈ vfMidOneBlockActivePhysicalCarrier R,
        vfMidOddSignedSeatCharge R n := by
    apply Finset.sum_congr rfl
    intro n hn
    simp [vfMidOneBlockActivePhysicalSite, hn]
  calc
    (∑ n ∈ lowOwnerNonzeroMobiusCarrier (R + 1),
      vfMidOneBlockActivePhysicalSite R n) =
      ∑ n ∈ vfMidOneBlockActivePhysicalCarrier R,
        vfMidOneBlockActivePhysicalSite R n := hs.symm
    _ = ∑ n ∈ vfMidOneBlockActivePhysicalCarrier R,
        vfMidOddSignedSeatCharge R n := hinside
    _ = vfMidOneBlockPrimeSeatCharge R +
        vfMidOneBlockProcessedSquarefreeCharge R :=
      vfMidOneBlockActivePhysicalCarrier_sum_eq_activeSource R

theorem one_mem_lowOwnerNonzeroMobiusCarrier_succ
    {R : ℕ} (hR : 1 ≤ R) :
    1 ∈ lowOwnerNonzeroMobiusCarrier (R + 1) := by
  unfold lowOwnerNonzeroMobiusCarrier
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_Icc.mpr
    constructor
    · norm_num
    · unfold squareRootEndpoint
      have hsq : 1 + 1 ≤ (R + 1) ^ 2 := by
        nlinarith
      exact Nat.le_sub_of_add_le hsq
  · unfold realMoebiusStep
    norm_num

def vfMidOneBlockAnchoredUpperPhysicalSite (R n : ℕ) : ℝ :=
  vfMidOneBlockActivePhysicalSite R n +
    if n = 1 then -vfMidActualPrimeEndpointDefect R else 0

def vfMidAnchoredUpperMobiusScale (R n : ℕ) : ℝ :=
  vfMidOneBlockAnchoredUpperPhysicalSite R n * realMoebiusStep n

theorem vfMidAnchoredUpperMobiusScale_mul_moebius
    {R n : ℕ}
    (hn : n ∈ lowOwnerNonzeroMobiusCarrier (R + 1)) :
    vfMidAnchoredUpperMobiusScale R n * realMoebiusStep n =
      vfMidOneBlockAnchoredUpperPhysicalSite R n := by
  have hmu : realMoebiusStep n ≠ 0 :=
    (Finset.mem_filter.mp hn).2
  have hsq : realMoebiusStep n ^ 2 = 1 := by
    rcases ArithmeticFunction.moebius_eq_or n with h0 | h1 | hm1
    · exfalso
      apply hmu
      simp [realMoebiusStep, h0]
    · simp [realMoebiusStep, h1]
    · simp [realMoebiusStep, hm1]
  unfold vfMidAnchoredUpperMobiusScale
  calc
    (vfMidOneBlockAnchoredUpperPhysicalSite R n * realMoebiusStep n) *
        realMoebiusStep n =
      vfMidOneBlockAnchoredUpperPhysicalSite R n *
        realMoebiusStep n ^ 2 := by ring
    _ = vfMidOneBlockAnchoredUpperPhysicalSite R n := by
      rw [hsq]
      ring

theorem vfMidAnchoredUpperPhysicalPair_eq_scale_mul_moebiusPair
    {R a b : ℕ}
    (ha : a ∈ lowOwnerNonzeroMobiusCarrier (R + 1))
    (hb : b ∈ lowOwnerNonzeroMobiusCarrier (R + 1)) :
    vfMidOneBlockAnchoredUpperPhysicalSite R a *
        vfMidOneBlockAnchoredUpperPhysicalSite R b =
      (vfMidAnchoredUpperMobiusScale R a *
        vfMidAnchoredUpperMobiusScale R b) *
        (realMoebiusStep a * realMoebiusStep b) := by
  rw [← vfMidAnchoredUpperMobiusScale_mul_moebius ha,
    ← vfMidAnchoredUpperMobiusScale_mul_moebius hb]
  ring

theorem vfMidAnchoredUpperActivePair_eq_scaledDirichletPolarizationAtom
    {R p a b : ℕ} {sig : Finset ℕ}
    (hR : 3 ≤ R) (hp : p.Prime)
    (haActive : a ∈ vfMidOneBlockActivePhysicalCarrier R)
    (hbActive : b ∈ vfMidOneBlockActivePhysicalCarrier R)
    (haBase : a ∈ lowOwnerFirstOwnerBaseFiber (R + 1) p sig)
    (hbChild : b ∈ lowOwnerFirstOwnerChildFiber (R + 1) p sig) :
    vfMidOneBlockAnchoredUpperPhysicalSite R a *
        vfMidOneBlockAnchoredUpperPhysicalSite R b =
      (vfMidAnchoredUpperMobiusScale R a *
        vfMidAnchoredUpperMobiusScale R b) *
        lowOwnerFirstOwnerDirichletPolarizationAtom
          (R + 1) p (a, b / p) := by
  have haCar :
      a ∈ lowOwnerNonzeroMobiusCarrier (R + 1) :=
    vfMidOneBlockActivePhysicalCarrier_subset_lowOwner_succ haActive
  have hbCar :
      b ∈ lowOwnerNonzeroMobiusCarrier (R + 1) :=
    vfMidOneBlockActivePhysicalCarrier_subset_lowOwner_succ hbActive
  have haClip :
      a ∈ lowOwnerFirstOwnerClippedBaseFiber (R + 1) p sig :=
    vfMidOneBlockActivePhysical_mem_clippedBase hR hp haActive haBase
  have hcAdm :
      b / p ∈ lowOwnerFirstOwnerAdmittedBaseFiber (R + 1) p sig :=
    lowOwnerFirstOwner_div_mem_admitted_of_child hp hbChild
  have hbDvd : p ∣ b :=
    (Finset.mem_filter.mp hbChild).2.2
  have hcancel : p * (b / p) = b :=
    Nat.mul_div_cancel' hbDvd
  have hcBase := (Finset.mem_filter.mp hcAdm).1
  have hpc : ¬ p ∣ b / p :=
    (Finset.mem_filter.mp hcBase).2.2
  have hmu :
      realMoebiusStep b = -realMoebiusStep (b / p) := by
    calc
      realMoebiusStep b =
          realMoebiusStep (p * (b / p)) := by rw [hcancel]
      _ = -realMoebiusStep (b / p) :=
        realMoebiusStep_mul_prime_eq_neg hp hpc
  have hbase :
      lowOwnerFirstOwnerDirichletBaseSite (R + 1) a =
        realMoebiusStep a :=
    lowOwnerFirstOwnerDirichletBaseSite_eq_moebius_on_vfMidActivePhysical
      hR haActive
  have hret :
      lowOwnerFirstOwnerDirichletReturnedChildSite
          (R + 1) p (b / p) =
        realMoebiusStep (b / p) :=
    lowOwnerFirstOwnerDirichletReturnedChildSite_div_eq_moebius_on_vfMidActivePhysical
      hR hp hbActive hbChild
  have hatom :=
    lowOwnerFirstOwnerDirichletPolarizationAtom_eq_clipped_left
      haClip hcAdm
  calc
    vfMidOneBlockAnchoredUpperPhysicalSite R a *
        vfMidOneBlockAnchoredUpperPhysicalSite R b =
      (vfMidAnchoredUpperMobiusScale R a *
        vfMidAnchoredUpperMobiusScale R b) *
        (realMoebiusStep a * realMoebiusStep b) :=
          vfMidAnchoredUpperPhysicalPair_eq_scale_mul_moebiusPair haCar hbCar
    _ =
      (vfMidAnchoredUpperMobiusScale R a *
        vfMidAnchoredUpperMobiusScale R b) *
        (-(realMoebiusStep a * realMoebiusStep (b / p))) := by
          rw [hmu]
          ring
    _ =
      (vfMidAnchoredUpperMobiusScale R a *
        vfMidAnchoredUpperMobiusScale R b) *
        lowOwnerFirstOwnerDirichletPolarizationAtom
          (R + 1) p (a, b / p) := by
          rw [hatom, hbase, hret]
          ring

theorem vfMidOneBlockAnchoredUpperPhysicalSite_sum_eq
    {R : ℕ} (hR : 1 ≤ R) :
    (∑ n ∈ lowOwnerNonzeroMobiusCarrier (R + 1),
      vfMidOneBlockAnchoredUpperPhysicalSite R n) =
      vfMidOneBlockPrimeSeatCharge R +
        vfMidOneBlockProcessedSquarefreeCharge R -
          vfMidActualPrimeEndpointDefect R := by
  unfold vfMidOneBlockAnchoredUpperPhysicalSite
  rw [Finset.sum_add_distrib]
  rw [vfMidOneBlockActivePhysicalSite_sum_eq_activeSource (R := R)]
  have h1 := one_mem_lowOwnerNonzeroMobiusCarrier_succ hR
  have hanchor :
      (∑ n ∈ lowOwnerNonzeroMobiusCarrier (R + 1),
        if n = 1 then -vfMidActualPrimeEndpointDefect R else 0) =
        -vfMidActualPrimeEndpointDefect R := by
    rw [Finset.sum_ite_eq']
    simp [h1]
  rw [hanchor]
  ring

theorem vfMidUpperFirstBadSourceBill_add_anchorSq_eq_anchoredSite_sq
    {R : ℕ} (hR : 1 ≤ R) :
    vfMidUpperFirstBadSourceBill R +
        vfMidActualPrimeEndpointDefect R ^ 2 =
      (∑ n ∈ lowOwnerNonzeroMobiusCarrier (R + 1),
        vfMidOneBlockAnchoredUpperPhysicalSite R n) ^ 2 := by
  rw [vfMidOneBlockAnchoredUpperPhysicalSite_sum_eq hR]
  unfold vfMidUpperFirstBadSourceBill
  ring

theorem vfMidUpperFirstBadSourceBill_add_anchorSq_eq_diagonal_add_firstOwnerCells
    {R : ℕ} (hR : 1 ≤ R) :
    vfMidUpperFirstBadSourceBill R +
        vfMidActualPrimeEndpointDefect R ^ 2 =
      lowOwnerGlobalDiagonalPairMassWith (R + 1)
          (vfMidOneBlockAnchoredUpperPhysicalSite R) +
        ∑ p ∈ primesUpTo (squareRootEndpoint (R + 1)),
          2 * ∑ sig ∈ lowOwnerFirstOwnerSignatureSet (R + 1) p,
            lowOwnerFirstOwnerCellGramWith (R + 1) p sig
              (vfMidOneBlockAnchoredUpperPhysicalSite R) := by
  calc
    vfMidUpperFirstBadSourceBill R +
        vfMidActualPrimeEndpointDefect R ^ 2 =
      (∑ n ∈ lowOwnerNonzeroMobiusCarrier (R + 1),
        vfMidOneBlockAnchoredUpperPhysicalSite R n) ^ 2 :=
          vfMidUpperFirstBadSourceBill_add_anchorSq_eq_anchoredSite_sq hR
    _ = lowOwnerRevealedPairMassWith (R + 1) ∅
        (vfMidOneBlockAnchoredUpperPhysicalSite R) := by
          symm
          exact lowOwnerRevealedPairMassWith_empty_eq_sum_sq
            (R + 1) (vfMidOneBlockAnchoredUpperPhysicalSite R)
    _ = lowOwnerGlobalDiagonalPairMassWith (R + 1)
          (vfMidOneBlockAnchoredUpperPhysicalSite R) +
        ∑ p ∈ primesUpTo (squareRootEndpoint (R + 1)),
          lowOwnerGlobalFirstOwnerPairMassWith (R + 1) p
            (vfMidOneBlockAnchoredUpperPhysicalSite R) :=
          lowOwnerRevealedPairMassWith_empty_eq_diagonal_add_firstOwners
            (R + 1) (vfMidOneBlockAnchoredUpperPhysicalSite R)
    _ = lowOwnerGlobalDiagonalPairMassWith (R + 1)
          (vfMidOneBlockAnchoredUpperPhysicalSite R) +
        ∑ p ∈ primesUpTo (squareRootEndpoint (R + 1)),
          2 * ∑ sig ∈ lowOwnerFirstOwnerSignatureSet (R + 1) p,
            lowOwnerFirstOwnerCellGramWith (R + 1) p sig
              (vfMidOneBlockAnchoredUpperPhysicalSite R) := by
          apply congrArg
            (fun x : ℝ =>
              lowOwnerGlobalDiagonalPairMassWith (R + 1)
                (vfMidOneBlockAnchoredUpperPhysicalSite R) + x)
          apply Finset.sum_congr rfl
          intro p hpMem
          exact lowOwnerGlobalFirstOwnerPairMassWith_eq_two_sum_cells
            (mem_primesUpTo.mp hpMem).1
            (vfMidOneBlockAnchoredUpperPhysicalSite R)

theorem vfMidScaledFirstOwnerSignedCellTelescope_le_half_dirichletIncidence_sq
    {R p : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) (scale : ℝ) :
    scale ^ 2 * lowOwnerFirstOwnerSignedCellTelescope R p sig ≤
      (1 / 2 : ℝ) *
        (scale * lowOwnerFirstOwnerDirichletIncidenceAmplitude R p sig) ^ 2 := by
  have hcore :=
    lowOwnerFirstOwnerSignedCellTelescope_le_half_dirichletIncidence_sq
      (R := R) (p := p) (sig := sig) hp
  have hscale : 0 ≤ scale ^ 2 := sq_nonneg scale
  have hscaled :=
    mul_le_mul_of_nonneg_left hcore hscale
  calc
    scale ^ 2 * lowOwnerFirstOwnerSignedCellTelescope R p sig ≤
        scale ^ 2 *
          ((1 / 2 : ℝ) *
            lowOwnerFirstOwnerDirichletIncidenceAmplitude R p sig ^ 2) :=
      hscaled
    _ = (1 / 2 : ℝ) *
        (scale * lowOwnerFirstOwnerDirichletIncidenceAmplitude R p sig) ^ 2 := by
      ring

def vfMidFirstOwnerCellBaseAmplitudeWith
    (R p : ℕ) (sig : Finset ℕ) (v : ℕ → ℝ) : ℝ :=
  ∑ a ∈ lowOwnerFirstOwnerBaseFiber R p sig, v a

def vfMidFirstOwnerCellChildAmplitudeWith
    (R p : ℕ) (sig : Finset ℕ) (v : ℕ → ℝ) : ℝ :=
  ∑ b ∈ lowOwnerFirstOwnerChildFiber R p sig, v b

theorem vfMidFirstOwnerCellGramWith_eq_base_mul_child
    (R p : ℕ) (sig : Finset ℕ) (v : ℕ → ℝ) :
    lowOwnerFirstOwnerCellGramWith R p sig v =
      vfMidFirstOwnerCellBaseAmplitudeWith R p sig v *
        vfMidFirstOwnerCellChildAmplitudeWith R p sig v := by
  unfold lowOwnerFirstOwnerCellGramWith
    vfMidFirstOwnerCellBaseAmplitudeWith
    vfMidFirstOwnerCellChildAmplitudeWith
  rw [Finset.product_eq_sprod, Finset.sum_product, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [Finset.mul_sum]

theorem vfMidFirstOwnerCellGramWith_le_half_branchSum_sq
    (R p : ℕ) (sig : Finset ℕ) (v : ℕ → ℝ) :
    2 * lowOwnerFirstOwnerCellGramWith R p sig v ≤
      (1 / 2 : ℝ) *
        (vfMidFirstOwnerCellBaseAmplitudeWith R p sig v +
          vfMidFirstOwnerCellChildAmplitudeWith R p sig v) ^ 2 := by
  rw [vfMidFirstOwnerCellGramWith_eq_base_mul_child]
  nlinarith [sq_nonneg
    (vfMidFirstOwnerCellBaseAmplitudeWith R p sig v -
      vfMidFirstOwnerCellChildAmplitudeWith R p sig v)]

def vfMidOneBlockUpperActiveAbsMass (R : ℕ) : ℝ :=
  ∑ n ∈ vfMidOneBlockActivePhysicalCarrier R,
    |vfMidOddSignedSeatCharge R n|

@[simp] theorem vfMidOneBlockUpperActiveAbsMass_nonneg
    (R : ℕ) :
    0 ≤ vfMidOneBlockUpperActiveAbsMass R := by
  unfold vfMidOneBlockUpperActiveAbsMass
  positivity

theorem one_not_mem_vfMidOneBlockActivePhysicalCarrier
    {R : ℕ} (hR : 1 ≤ R) :
    1 ∉ vfMidOneBlockActivePhysicalCarrier R := by
  intro h1
  have hband :=
    vfMidOneBlockActivePhysicalCarrier_mem_squareBandSites h1
  have hlow : R ^ 2 < 1 := (Finset.mem_Ioo.mp hband).1
  have hsq : 1 ≤ R ^ 2 := by nlinarith
  omega

theorem vfMidAnchoredUpperPhysicalSite_absSum_eq
    {R : ℕ} (hR : 3 ≤ R) :
    (∑ n ∈ lowOwnerNonzeroMobiusCarrier (R + 1),
      |vfMidOneBlockAnchoredUpperPhysicalSite R n|) =
      |vfMidActualPrimeEndpointDefect R| +
        vfMidOneBlockUpperActiveAbsMass R := by
  have h1 :
      1 ∈ lowOwnerNonzeroMobiusCarrier (R + 1) :=
    one_mem_lowOwnerNonzeroMobiusCarrier_succ (by omega : 1 ≤ R)
  have h1not :
      1 ∉ vfMidOneBlockActivePhysicalCarrier R :=
    one_not_mem_vfMidOneBlockActivePhysicalCarrier
      (by omega : 1 ≤ R)
  have hsub :
      insert 1 (vfMidOneBlockActivePhysicalCarrier R) ⊆
        lowOwnerNonzeroMobiusCarrier (R + 1) := by
    intro n hn
    rcases Finset.mem_insert.mp hn with rfl | hnActive
    · exact h1
    · exact
        vfMidOneBlockActivePhysicalCarrier_subset_lowOwner_succ hnActive
  have hzero :
      ∀ n ∈ lowOwnerNonzeroMobiusCarrier (R + 1),
        n ∉ insert 1 (vfMidOneBlockActivePhysicalCarrier R) →
          |vfMidOneBlockAnchoredUpperPhysicalSite R n| = 0 := by
    intro n _hn hnot
    have hn1 : n ≠ 1 := by
      intro hn
      subst n
      exact hnot (Finset.mem_insert_self 1 _)
    have hnActive :
        n ∉ vfMidOneBlockActivePhysicalCarrier R := by
      intro hn
      exact hnot (Finset.mem_insert_of_mem hn)
    simp [vfMidOneBlockAnchoredUpperPhysicalSite,
      vfMidOneBlockActivePhysicalSite, hn1, hnActive]
  have hsupport :=
    Finset.sum_subset hsub hzero
  have hactive :
      (∑ n ∈ vfMidOneBlockActivePhysicalCarrier R,
        |vfMidOneBlockAnchoredUpperPhysicalSite R n|) =
        vfMidOneBlockUpperActiveAbsMass R := by
    unfold vfMidOneBlockUpperActiveAbsMass
    apply Finset.sum_congr rfl
    intro n hn
    have hn1 : n ≠ 1 := by
      intro hnEq
      subst n
      exact h1not hn
    simp [vfMidOneBlockAnchoredUpperPhysicalSite,
      vfMidOneBlockActivePhysicalSite, hn, hn1]
  have hanchor :
      |vfMidOneBlockAnchoredUpperPhysicalSite R 1| =
        |vfMidActualPrimeEndpointDefect R| := by
    simp [vfMidOneBlockAnchoredUpperPhysicalSite,
      vfMidOneBlockActivePhysicalSite, h1not]
  calc
    (∑ n ∈ lowOwnerNonzeroMobiusCarrier (R + 1),
      |vfMidOneBlockAnchoredUpperPhysicalSite R n|) =
      ∑ n ∈ insert 1 (vfMidOneBlockActivePhysicalCarrier R),
        |vfMidOneBlockAnchoredUpperPhysicalSite R n| := hsupport.symm
    _ =
      |vfMidOneBlockAnchoredUpperPhysicalSite R 1| +
        ∑ n ∈ vfMidOneBlockActivePhysicalCarrier R,
          |vfMidOneBlockAnchoredUpperPhysicalSite R n| := by
            rw [Finset.sum_insert h1not]
    _ =
      |vfMidActualPrimeEndpointDefect R| +
        vfMidOneBlockUpperActiveAbsMass R := by
          rw [hanchor, hactive]

theorem vfMidOneBlockActivePhysicalCarrier_subset_oddCandidates
    {R : ℕ} (hR : 3 ≤ R) :
    vfMidOneBlockActivePhysicalCarrier R ⊆ vfMidOddCandidateSeats R := by
  intro n hn
  unfold vfMidOneBlockActivePhysicalCarrier at hn
  rcases Finset.mem_union.mp hn with hnPrime | hnProcessed
  · have hfilter :
        n ∈ (vfMidOddCandidateSeats R).filter Nat.Prime := by
      rw [vfMidOddCandidateSeats_filter_prime R (by omega : 2 ≤ R)]
      exact hnPrime
    exact (Finset.mem_filter.mp hfilter).1
  · rcases Finset.mem_biUnion.mp hnProcessed with ⟨p, hp, hnSq⟩
    have hnOwner : n ∈ vfMidSquareBandCompositeOwner R p :=
      (Finset.mem_filter.mp hnSq).1
    have hnComp : n ∈ vfMidSquareBandComposites R :=
      (Finset.mem_filter.mp hnOwner).1
    have hmin : n.minFac = p :=
      (Finset.mem_filter.mp hnOwner).2
    have hpLate : p ∈ vfMidSquareBandLateOwnerPrimes 2 R := by
      rw [← vfMidFrozenProcessedOwnerPrimes_self_eq_allOddOwners R]
      exact hp
    have hpGt : 2 < p :=
      (mem_vfMidSquareBandLateOwnerPrimes.mp hpLate).2
    have hsurv : lowWheelHighSurvivor 2 n := by
      apply (vfMidSquareBandComposite_survives_prefix_iff_minFac_gt
        (z := 2) (R := R) (n := n) (by omega : 2 ≤ R) hnComp).2
      simpa [hmin] using hpGt
    unfold vfMidOddCandidateSeats vfMidSquarePrefixWheelSurvivors
    apply Finset.mem_filter.mpr
    constructor
    · have hsite : n ∈ vfMidSquareBandSites R :=
        (Finset.mem_filter.mp hnComp).1
      simpa [vfMidSquareBandSites, vfMidSquareWheelSites] using hsite
    · exact hsurv

/-! ## Exact weighted demand and capacity on the adjacent clock -/

/-- Arbitrary-site Fubini, including the physical diagonal. -/
theorem vfMidWeightedSiteSquare_eq_diagonal_add_firstOwnerCells
    (C : ℕ) (v : ℕ → ℝ) :
    (∑ n ∈ lowOwnerNonzeroMobiusCarrier C, v n) ^ 2 =
      lowOwnerGlobalDiagonalPairMassWith C v +
        ∑ p ∈ primesUpTo (squareRootEndpoint C),
          ∑ sig ∈ lowOwnerFirstOwnerSignatureSet C p,
            2 * lowOwnerFirstOwnerCellGramWith C p sig v := by
  rw [← lowOwnerRevealedPairMassWith_empty_eq_sum_sq,
    lowOwnerRevealedPairMassWith_empty_eq_diagonal_add_firstOwners]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  rw [lowOwnerGlobalFirstOwnerPairMassWith_eq_two_sum_cells
    (mem_primesUpTo.mp hp).1, Finset.mul_sum]

/-- Ordered cell contribution to twice the actual source square.  Every VF
weight stays inside its physical branch, at clock R+1. -/
def weightedCellDemand (R p : ℕ) (sig : Finset ℕ) : ℝ :=
  4 * lowOwnerFirstOwnerCellGramWith (R + 1) p sig
    (vfMidOneBlockAnchoredUpperPhysicalSite R)

/-- Absolute pair capacity on exactly the same cell.  This is the literal
denominator partition; it is not the bare no-persistence safe mass. -/
def weightedSafeCapacity (R p : ℕ) (sig : Finset ℕ) : ℝ :=
  2 * lowOwnerFirstOwnerCellGramWith (R + 1) p sig
    (fun n => |vfMidOneBlockAnchoredUpperPhysicalSite R n|)

/-- Current odd seats omitted by the squarefree first-owner clock. -/
def vfMidWeightedOmittedSeatAbsMass (R : ℕ) : ℝ :=
  ∑ n ∈ vfMidOddCandidateSeats R \ vfMidOneBlockActivePhysicalCarrier R,
    |vfMidOddSignedSeatCharge R n|

/-- The diagonal and squareful correction in the exact actual source.  Neither
term belongs to a unique off-diagonal first-owner cell. -/
def vfMidWeightedDemandResidual (R : ℕ) : ℝ :=
  2 * lowOwnerGlobalDiagonalPairMassWith (R + 1)
      (vfMidOneBlockAnchoredUpperPhysicalSite R) -
    2 * vfMidOneBlockProcessedSquarefulCharge R *
      (2 * vfMidActualPrimeEndpointDefect (R + 1) +
        vfMidOneBlockProcessedSquarefulCharge R)

/-- Denominator terms outside the off-diagonal squarefree cell partition:
the diagonal and all absolute products involving an omitted current seat. -/
def vfMidWeightedSafeCapacityResidual (R : ℕ) : ℝ :=
  lowOwnerGlobalDiagonalPairMassWith (R + 1)
      (vfMidOneBlockAnchoredUpperPhysicalSite R) +
    vfMidWeightedOmittedSeatAbsMass R *
      (2 * (|vfMidActualPrimeEndpointDefect R| +
        vfMidOneBlockUpperActiveAbsMass R) +
        vfMidWeightedOmittedSeatAbsMass R)

/-- Exact actual demand identity.  The source is twice D_(R+1)^2, rather than
twice the upper active source square.  The residual is retained explicitly. -/
theorem vfMid_globalDemand_eq_sum_weightedCells
    {R : ℕ} (hR : 3 ≤ R) :
    2 * vfMidActualPrimeEndpointDefect (R + 1) ^ 2 =
      vfMidWeightedDemandResidual R +
        ∑ p ∈ primesUpTo (squareRootEndpoint (R + 1)),
          ∑ sig ∈ lowOwnerFirstOwnerSignatureSet (R + 1) p,
            weightedCellDemand R p sig := by
  have hsource :=
    vfMidFirstBadNormalizedProduct_eq_upperActive_sub_squarefulRestoring hR
  rw [vfMidFirstBadNormalizedProduct_eq_nextEndpointDefect_sq hR] at hsource
  have hfubini :=
    vfMidUpperFirstBadSourceBill_add_anchorSq_eq_diagonal_add_firstOwnerCells
      (R := R) (by omega : 1 ≤ R)
  have hcells :
      (∑ p ∈ primesUpTo (squareRootEndpoint (R + 1)),
        ∑ sig ∈ lowOwnerFirstOwnerSignatureSet (R + 1) p,
          weightedCellDemand R p sig) =
        2 * ∑ p ∈ primesUpTo (squareRootEndpoint (R + 1)),
          2 * ∑ sig ∈ lowOwnerFirstOwnerSignatureSet (R + 1) p,
            lowOwnerFirstOwnerCellGramWith (R + 1) p sig
              (vfMidOneBlockAnchoredUpperPhysicalSite R) := by
    simp only [weightedCellDemand, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _hp
    apply Finset.sum_congr rfl
    intro sig _hsig
    ring
  rw [hcells]
  unfold vfMidWeightedDemandResidual
  linarith

/-- Exact full odd-seat absolute mass, with the omitted seats kept. -/
theorem vfMidOddSeatAbsMass_eq_active_add_omitted
    {R : ℕ} (hR : 3 ≤ R) :
    (∑ n ∈ vfMidOddCandidateSeats R, |vfMidOddSignedSeatCharge R n|) =
      vfMidOneBlockUpperActiveAbsMass R +
        vfMidWeightedOmittedSeatAbsMass R := by
  have hpart := Finset.sum_sdiff
    (f := fun n => |vfMidOddSignedSeatCharge R n|)
    (vfMidOneBlockActivePhysicalCarrier_subset_oddCandidates hR)
  unfold vfMidOneBlockUpperActiveAbsMass vfMidWeightedOmittedSeatAbsMass
  linarith

/-- Taking absolute values preserves every diagonal product. -/
theorem vfMidWeightedDiagonal_abs_eq (C : ℕ) (v : ℕ → ℝ) :
    lowOwnerGlobalDiagonalPairMassWith C (fun n => |v n|) =
      lowOwnerGlobalDiagonalPairMassWith C v := by
  unfold lowOwnerGlobalDiagonalPairMassWith
  apply Finset.sum_congr rfl
  intro mn hmn
  have heq := (Finset.mem_filter.mp hmn).2
  rw [heq]
  simpa only [pow_two] using sq_abs (v mn.2)

/-- Exact capacity identity for the unchanged #897 denominator.  Local
half-gate branch squares do not replace these absolute pair capacities. -/
theorem vfMid_globalSafeCapacity_eq_sum_safeCells
    {R : ℕ} (hR : 3 ≤ R) :
    vfMidFirstBadZeroTargetTotalMass R =
      vfMidWeightedSafeCapacityResidual R +
        ∑ p ∈ primesUpTo (squareRootEndpoint (R + 1)),
          ∑ sig ∈ lowOwnerFirstOwnerSignatureSet (R + 1) p,
            weightedSafeCapacity R p sig := by
  have hfubini := vfMidWeightedSiteSquare_eq_diagonal_add_firstOwnerCells
    (R + 1) (fun n => |vfMidOneBlockAnchoredUpperPhysicalSite R n|)
  rw [vfMidAnchoredUpperPhysicalSite_absSum_eq hR,
    vfMidWeightedDiagonal_abs_eq] at hfubini
  rw [vfMidFirstBadZeroTargetTotalMass_eq,
    vfMidOddSeatAbsMass_eq_active_add_omitted hR]
  unfold vfMidWeightedSafeCapacityResidual weightedSafeCapacity
  nlinarith only [hfubini]

/-- The requested local arbitrary-site gate, at the adjacent clock and with
the exact factor used by weightedCellDemand. -/
theorem weightedCellDemand_le_weightedBranchSum_sq
    (R p : ℕ) (sig : Finset ℕ) :
    weightedCellDemand R p sig ≤
      (vfMidFirstOwnerCellBaseAmplitudeWith (R + 1) p sig
          (vfMidOneBlockAnchoredUpperPhysicalSite R) +
        vfMidFirstOwnerCellChildAmplitudeWith (R + 1) p sig
          (vfMidOneBlockAnchoredUpperPhysicalSite R)) ^ 2 := by
  have hgate := vfMidFirstOwnerCellGramWith_le_half_branchSum_sq
    (R + 1) p sig (vfMidOneBlockAnchoredUpperPhysicalSite R)
  unfold weightedCellDemand
  linarith

/-! ## Finite overflow without changing weights or dropping residuals -/

/-- Finite nested pigeonhole in the literal weighted currency. -/
theorem vfMidWeightedOwnerCellOverflow_of_sum_excess
    (C : ℕ) (demand capacity : ℕ → Finset ℕ → ℝ)
    (hexcess :
      (∑ p ∈ primesUpTo (squareRootEndpoint C),
        ∑ sig ∈ lowOwnerFirstOwnerSignatureSet C p, capacity p sig) <
      ∑ p ∈ primesUpTo (squareRootEndpoint C),
        ∑ sig ∈ lowOwnerFirstOwnerSignatureSet C p, demand p sig) :
    ∃ p ∈ primesUpTo (squareRootEndpoint C),
      ∃ sig ∈ lowOwnerFirstOwnerSignatureSet C p,
        capacity p sig < demand p sig := by
  by_contra hnot
  push_neg at hnot
  have hle :
      (∑ p ∈ primesUpTo (squareRootEndpoint C),
        ∑ sig ∈ lowOwnerFirstOwnerSignatureSet C p, demand p sig) ≤
      ∑ p ∈ primesUpTo (squareRootEndpoint C),
        ∑ sig ∈ lowOwnerFirstOwnerSignatureSet C p, capacity p sig := by
    apply Finset.sum_le_sum
    intro p hp
    apply Finset.sum_le_sum
    intro sig hsig
    exact hnot p hp sig hsig
  exact (not_lt_of_ge hle) hexcess

/-- A global actual-source excess forces a cell excess or an excess in the
explicit residual.  The latter alternative cannot be discarded by Fubini. -/
theorem vfMidFirstBadWeightedExcess_forces_residual_or_cell
    {R : ℕ} (hR : 3 ≤ R)
    (hexcess : vfMidFirstBadZeroTargetTotalMass R <
      2 * vfMidActualPrimeEndpointDefect (R + 1) ^ 2) :
    vfMidWeightedSafeCapacityResidual R < vfMidWeightedDemandResidual R ∨
      ∃ p ∈ primesUpTo (squareRootEndpoint (R + 1)),
        ∃ sig ∈ lowOwnerFirstOwnerSignatureSet (R + 1) p,
          weightedSafeCapacity R p sig < weightedCellDemand R p sig := by
  by_cases hres :
      vfMidWeightedSafeCapacityResidual R < vfMidWeightedDemandResidual R
  · exact Or.inl hres
  · apply Or.inr
    have hresle := le_of_not_gt hres
    rw [vfMid_globalSafeCapacity_eq_sum_safeCells hR,
      vfMid_globalDemand_eq_sum_weightedCells hR] at hexcess
    apply vfMidWeightedOwnerCellOverflow_of_sum_excess (R + 1)
      (weightedCellDemand R) (weightedSafeCapacity R)
    linarith

/-- Consume a separately proved residual budget without altering either
global source or denominator.  This is finite bookkeeping, not an assertion
that the budget or the weighted-to-sector-six transport has been proved. -/
theorem vfMidFirstBadWeightedCellOverflow_of_residual_budget
    {R : ℕ} (hR : 3 ≤ R)
    (hexcess : vfMidFirstBadZeroTargetTotalMass R <
      2 * vfMidActualPrimeEndpointDefect (R + 1) ^ 2)
    (hres : vfMidWeightedDemandResidual R ≤
      vfMidWeightedSafeCapacityResidual R) :
    ∃ p ∈ primesUpTo (squareRootEndpoint (R + 1)),
      ∃ sig ∈ lowOwnerFirstOwnerSignatureSet (R + 1) p,
        weightedSafeCapacity R p sig < weightedCellDemand R p sig := by
  rcases vfMidFirstBadWeightedExcess_forces_residual_or_cell hR hexcess with
    hbad | hcell
  · exact False.elim ((not_lt_of_ge hres) hbad)
  · exact hcell

/-! ## Regression: the identity diagonal has no first owner -/

/-- An identity-only site has zero mass in every p-divisible child branch. -/
theorem vfMidFirstOwnerCellGram_identitySite_eq_zero
    {C p : ℕ} (hp : p.Prime) (sig : Finset ℕ) :
    lowOwnerFirstOwnerCellGramWith C p sig
      (fun n => if n = 1 then (1 : ℝ) else 0) = 0 := by
  unfold lowOwnerFirstOwnerCellGramWith
  apply Finset.sum_eq_zero
  intro ab hab
  have hb := (Finset.mem_product.mp hab).2
  have hpdiv : p ∣ ab.2 := (Finset.mem_filter.mp hb).2.2
  have hb1 : ab.2 ≠ 1 := by
    intro h
    rw [h] at hpdiv
    exact hp.ne_one (Nat.dvd_one.mp hpdiv)
  simp [hb1]

/-- Executable symbolic counterexample to a cell-only square reassembly.
The identity site has square one and off-diagonal first-owner mass zero. -/
theorem vfMidWeightedFirstOwnerCells_omit_identityDiagonal
    {R : ℕ} (hR : 1 ≤ R) :
    (∑ n ∈ lowOwnerNonzeroMobiusCarrier (R + 1),
      if n = 1 then (1 : ℝ) else 0) ^ 2 = 1 ∧
    (∑ p ∈ primesUpTo (squareRootEndpoint (R + 1)),
      ∑ sig ∈ lowOwnerFirstOwnerSignatureSet (R + 1) p,
        2 * lowOwnerFirstOwnerCellGramWith (R + 1) p sig
          (fun n => if n = 1 then (1 : ℝ) else 0)) = 0 := by
  constructor
  · simp [one_mem_lowOwnerNonzeroMobiusCarrier_succ hR]
  · apply Finset.sum_eq_zero
    intro p hp
    apply Finset.sum_eq_zero
    intro sig _hsig
    rw [vfMidFirstOwnerCellGram_identitySite_eq_zero
      (mem_primesUpTo.mp hp).1]
    ring

end RHLean.Analysis
