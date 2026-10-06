import Mathlib
import «research.VF_MID_ANCHORED_CODIV_GATE_INLET»
import «research.VF_MID_GLOBAL_FIRST_BAD_RADIAL_BUDGET»
import «research.GLOBAL_RETURNED_CORE_GLOBAL_DESCENDING_SITE_FUBINI»
import «research.GLOBAL_RETURNED_CORE_FIRST_OWNER_ARBITRARY_SITE_CELLS»
import «research.GLOBAL_RETURNED_CORE_OWNER_TWO_CLIPPED_EXIT»
import «research.GLOBAL_RETURNED_CORE_VIRTUAL_OWNER_HALF_GATE»
import «research.NNS_ZERO_TARGET_FIRST_OWNER_CODIV_FUBINI»

/-!
# Final first-bad global hnorm splice

This file is the equality-first terminal wiring layer above #899.

The first operation is to quarantine the restoring sectors *before* any owner
Fubini or reciprocal estimate is introduced.  The normalized anchored numerator
is kept as the exact product

  rho_R * T_R,

and rewritten in the two endpoint-sign branches as

  upper active source - squareful restoring + D_R^2,

or

  lower composite source + prime restoring + D_R^2.

Thus the anchor remains coupled to the complete one-block source while the
squareful/prime restoring packet is still explicit.  Only after these exact
normal forms are established is the favorable restoring sign dropped.

No new analytic hypothesis, carrier enlargement, or packet-to-scale
inheritance is introduced here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- **Exact upper-sign anchored normal form.**

The rigid anchor square is retained and the squareful strict-descendant packet
is isolated as the exact restoring term.  This is an equality. -/
theorem vfMidFirstBadNormalizedProduct_eq_upperActive_sub_squarefulRestoring
    {R : ℕ} (hR : 3 ≤ R) :
    vfMidFirstBadNNSNormalizedCovariance R *
        vfMidFirstBadZeroTargetTotalMass R =
      vfMidUpperFirstBadSourceBill R -
        vfMidOneBlockProcessedSquarefulCharge R *
          (2 * vfMidActualPrimeEndpointDefect (R + 1) +
            vfMidOneBlockProcessedSquarefulCharge R) +
        vfMidActualPrimeEndpointDefect R ^ 2 := by
  rw [← vfMidCorrelationEnergy_add_anchorSq_eq_nnsNormalized_mul_total hR]
  rw [vfMidCorrelationEnergy_eq_upperActive_sub_squarefulRestoring hR]
  rfl

/-- **Exact lower-sign anchored normal form.**

The negative prime stream is retained as the exact restoring term and the
anchor square stays coupled to the remaining composite source.  This is an
equality. -/
theorem vfMidFirstBadNormalizedProduct_eq_lowerComposite_add_primeRestoring
    {R : ℕ} (hR : 3 ≤ R) :
    vfMidFirstBadNNSNormalizedCovariance R *
        vfMidFirstBadZeroTargetTotalMass R =
      vfMidLowerFirstBadSourceBill R +
        vfMidOneBlockPrimeSeatCharge R *
          (-2 * vfMidActualPrimeEndpointDefect (R + 1) -
            vfMidOneBlockPrimeSeatCharge R) +
        vfMidActualPrimeEndpointDefect R ^ 2 := by
  rw [← vfMidCorrelationEnergy_add_anchorSq_eq_nnsNormalized_mul_total hR]
  rw [vfMidCorrelationEnergy_eq_lowerActive_add_primeRestoring hR]
  rfl

/-- Once the endpoint is on the upper side, the exact squareful restoring
packet is nonpositive and may be dropped.  This is the first inequality in the
upper branch. -/
theorem vfMidFirstBadNormalizedProduct_le_upperActive_add_anchorSq
    {R : ℕ} (hR : 3 ≤ R)
    (hupper : 0 ≤ vfMidActualPrimeEndpointDefect (R + 1)) :
    vfMidFirstBadNNSNormalizedCovariance R *
        vfMidFirstBadZeroTargetTotalMass R ≤
      vfMidUpperFirstBadSourceBill R +
        vfMidActualPrimeEndpointDefect R ^ 2 := by
  rw [vfMidFirstBadNormalizedProduct_eq_upperActive_sub_squarefulRestoring hR]
  have hQ :=
    vfMidOneBlockProcessedSquarefulCharge_nonneg R (by omega : 2 ≤ R)
  nlinarith

/-- Once the endpoint is on the lower side, the exact prime restoring packet
is nonpositive and may be dropped.  This is the first inequality in the lower
branch. -/
theorem vfMidFirstBadNormalizedProduct_le_lowerComposite_add_anchorSq
    {R : ℕ} (hR : 3 ≤ R)
    (hlower : vfMidActualPrimeEndpointDefect (R + 1) ≤ 0) :
    vfMidFirstBadNNSNormalizedCovariance R *
        vfMidFirstBadZeroTargetTotalMass R ≤
      vfMidLowerFirstBadSourceBill R +
        vfMidActualPrimeEndpointDefect R ^ 2 := by
  rw [vfMidFirstBadNormalizedProduct_eq_lowerComposite_add_primeRestoring hR]
  have hP := vfMidOneBlockPrimeSeatCharge_nonpos R hR
  nlinarith

/-- **Exact normalized endpoint-energy identity.**

The complete anchored NNS numerator is not an additional energy packet: after
the exact endpoint weld it is literally the next endpoint defect squared.
Naming this identity prevents the rigid anchor square from being charged a
second time or assigned a fictitious fresh owner. -/
theorem vfMidFirstBadNormalizedProduct_eq_nextEndpointDefect_sq
    {R : ℕ} (hR : 3 ≤ R) :
    vfMidFirstBadNNSNormalizedCovariance R *
        vfMidFirstBadZeroTargetTotalMass R =
      vfMidActualPrimeEndpointDefect (R + 1) ^ 2 := by
  have hnorm :=
    vfMidCorrelationEnergy_add_anchorSq_eq_nnsNormalized_mul_total hR
  have hcorr :=
    vfMidSquareEndpointError_sq_succ_eq_correlation
      R (by omega : 2 ≤ R)
  calc
    vfMidFirstBadNNSNormalizedCovariance R *
        vfMidFirstBadZeroTargetTotalMass R =
      2 * vfMidSquareEndpointAccumulationCorrelation R +
        vfMidSquareBandError R ^ 2 +
        vfMidActualPrimeEndpointDefect R ^ 2 := hnorm.symm
    _ = vfMidActualPrimeEndpointDefect (R + 1) ^ 2 := by
      rw [vfMidActualPrimeEndpointDefect_eq_squareEndpointError
          (R := R) (by omega : 2 ≤ R),
        vfMidActualPrimeEndpointDefect_eq_squareEndpointError
          (R := R + 1) (by omega : 2 ≤ R + 1)]
      nlinarith [hcorr]


/-! ## Physical active source before any child stripping -/

/-- Squarefree processed physical owner fibres are disjoint because the least
prime factor is part of the fibre definition.  This is the 1027 multiplicity
guard: owner labels are resolved on physical sites before any quotient map is
applied. -/
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

/-- Physical squarefree composite seats, with the least-owner fibres unioned
only after their pairwise disjointness has been proved. -/
def vfMidOneBlockProcessedSquarefreePhysicalCarrier
    (R : ℕ) : Finset ℕ :=
  (vfMidFrozenProcessedOwnerPrimes R R).biUnion
    (vfMidSquarefreeProcessedOwnerSites R)

/-- The disjoint physical carrier has exactly the already-defined processed
squarefree charge. -/
theorem vfMidProcessedSquarefreePhysicalCarrier_sum_eq_charge
    (R : ℕ) :
    (∑ n ∈ vfMidOneBlockProcessedSquarefreePhysicalCarrier R,
      vfMidOddSignedSeatCharge R n) =
      vfMidOneBlockProcessedSquarefreeCharge R := by
  unfold vfMidOneBlockProcessedSquarefreePhysicalCarrier
    vfMidOneBlockProcessedSquarefreeCharge
  rw [Finset.sum_biUnion
    (vfMidSquarefreeProcessedOwnerSites_pairwiseDisjoint R)]

/-- Prime seats and processed-composite seats are disjoint on the physical
block, before any owner is stripped. -/
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

/-- Literal squarefree physical source of the adjacent block.  No quotient
child has been introduced. -/
def vfMidOneBlockActivePhysicalCarrier (R : ℕ) : Finset ℕ :=
  vfMidSquareWheelPrimes R ∪
    vfMidOneBlockProcessedSquarefreePhysicalCarrier R

/-- Summing the literal active carrier gives the exact upper-branch active
source, with no loss of cross-owner information. -/
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

/-- Every active physical current seat lies on the nonzero-Mobius clock at the
adjacent endpoint.  Crucially this statement is about the unstripped physical
integer, not its child. -/
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

/-- Every active physical seat lies in the literal current square band. -/
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

/-- From R >= 3, a current-block active seat lies beyond the owner-two clip on
the adjacent common clock.  This is the geometric reason every non-anchor
active base row is already a first-owner clipped row. -/
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

/-- The native low-owner AMP weight is exactly one on every active physical
seat of the current square band at the adjacent clock. -/
theorem lowOwnerZeroFrequencyMobiusWeight_eq_one_on_vfMidActivePhysical
    {R n : ℕ} (hR : 3 ≤ R)
    (hn : n ∈ vfMidOneBlockActivePhysicalCarrier R) :
    lowOwnerZeroFrequencyMobiusWeight (R + 1) n = 1 := by
  exact
    lowOwnerZeroFrequencyMobiusWeight_eq_one_of_ownerTwo_clipped
      (R := R + 1) (a := n) (by omega : 2 ≤ R + 1)
      (vfMidOneBlockActivePhysical_two_mul_gt_endpoint hR hn)

/-- On an active physical seat, the Dirichlet base site at the adjacent clock
is therefore the bare Möbius sign. -/
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

/-- An active p-divisible physical child returns to an admitted parent whose
Dirichlet returned-child site is again the bare Möbius sign. -/
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

/-- A non-anchor active base seat is literally in the clipped side of every
first-owner cell containing it. -/
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

/-- Zero-extension of the literal physical active source to the common clock.
The support test is deliberately the physical carrier membership, so all owner
assignment happens before child stripping. -/
def vfMidOneBlockActivePhysicalSite (R n : ℕ) : ℝ :=
  if n ∈ vfMidOneBlockActivePhysicalCarrier R then
    vfMidOddSignedSeatCharge R n
  else 0

/-- Zero-extension preserves the exact one-dimensional active source mass. -/
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

/-- **1027-safe exact owner Fubini for the active source square.**

The physical square is partitioned into its literal diagonal plus unique
greatest-owner crossing fibres *before* any quotient child is formed.  Hence no
two distinct physical seats can become an accidental common child during this
Fubini swap.  This is an equality; no estimate has been introduced. -/
theorem vfMidOneBlockActiveSource_sq_eq_diagonal_add_descendingCross
    {R : ℕ} :
    (vfMidOneBlockPrimeSeatCharge R +
        vfMidOneBlockProcessedSquarefreeCharge R) ^ 2 =
      lowOwnerGlobalDiagonalPairMassWith (R + 1)
        (vfMidOneBlockActivePhysicalSite R) +
      ∑ r ∈ primesUpTo (squareRootEndpoint (R + 1)),
        lowOwnerRevealedCrossPairMassWith (R + 1)
          (lowOwnerRevealedPrimesAbove (R + 1) r) r
          (vfMidOneBlockActivePhysicalSite R) := by
  have hpair :=
    lowOwnerRevealedPairMassWith_empty_eq_diagonal_add_descendingCross
      (R + 1) (vfMidOneBlockActivePhysicalSite R)
  have hsquare :=
    lowOwnerRevealedPairMassWith_empty_eq_sum_sq
      (R + 1) (vfMidOneBlockActivePhysicalSite R)
  rw [hsquare] at hpair
  rw [vfMidOneBlockActivePhysicalSite_sum_eq_activeSource (R := R)] at hpair
  exact hpair


/-! ## Anchor injection on the common clock -/

/-- The multiplicative identity is always present on the adjacent nonzero-Möbius
clock.  It is therefore a legal physical location for the rigid historical
anchor; no new owner or synthetic carrier is introduced. -/
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

/-- Upper-branch active physical site with the rigid anchor inserted at the
identity site of the same common clock. -/
def vfMidOneBlockAnchoredUpperPhysicalSite (R n : ℕ) : ℝ :=
  vfMidOneBlockActivePhysicalSite R n +
    if n = 1 then -vfMidActualPrimeEndpointDefect R else 0

/-- Retained scalar that represents the complete anchored upper physical site
as a scalar multiple of the physical Möbius sign on the common clock.  Defining
it this way removes all prime/composite casework from the subsequent pair
transport. -/
def vfMidAnchoredUpperMobiusScale (R n : ℕ) : ℝ :=
  vfMidOneBlockAnchoredUpperPhysicalSite R n * realMoebiusStep n

/-- On the nonzero-Möbius clock, the retained scalar times the Möbius sign is
exactly the anchored physical site. -/
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

/-- Pairwise anchored physical products are therefore literal retained-scalar
multiples of the ordinary Möbius pair product.  This is the affine currency
used by the raw-parent projection. -/
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

/-- **Affine pointwise physical-to-Dirichlet weld on an ordinary active row.**

For two active physical seats in one first-owner cell, the p-divisible seat is
returned to b/p.  The p-free active seat is already clipped, the returned
parent is admitted, and the native Dirichlet atom is the bare Möbius pair
product.  The complete VF affine weight is retained as a parentwise scalar. -/
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

/-- Anchor injection preserves the full affine amplitude exactly. -/
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

/-- The upper one-sided bill plus the anchor square is literally the square of
one signed site amplitude on the common clock. -/
theorem vfMidUpperFirstBadSourceBill_add_anchorSq_eq_anchoredSite_sq
    {R : ℕ} (hR : 1 ≤ R) :
    vfMidUpperFirstBadSourceBill R +
        vfMidActualPrimeEndpointDefect R ^ 2 =
      (∑ n ∈ lowOwnerNonzeroMobiusCarrier (R + 1),
        vfMidOneBlockAnchoredUpperPhysicalSite R n) ^ 2 := by
  rw [vfMidOneBlockAnchoredUpperPhysicalSite_sum_eq hR]
  unfold vfMidUpperFirstBadSourceBill
  ring

/-- **Anchored global greatest-owner Fubini.**

The complete upper active bill, including the rigid anchor square and all
anchor-current cross terms, is partitioned on the literal common clock before
any quotient child is formed. -/
theorem vfMidUpperFirstBadSourceBill_add_anchorSq_eq_diagonal_add_descendingCross
    {R : ℕ} (hR : 1 ≤ R) :
    vfMidUpperFirstBadSourceBill R +
        vfMidActualPrimeEndpointDefect R ^ 2 =
      lowOwnerGlobalDiagonalPairMassWith (R + 1)
        (vfMidOneBlockAnchoredUpperPhysicalSite R) +
      ∑ r ∈ primesUpTo (squareRootEndpoint (R + 1)),
        lowOwnerRevealedCrossPairMassWith (R + 1)
          (lowOwnerRevealedPrimesAbove (R + 1) r) r
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
        ∑ r ∈ primesUpTo (squareRootEndpoint (R + 1)),
          lowOwnerRevealedCrossPairMassWith (R + 1)
            (lowOwnerRevealedPrimesAbove (R + 1) r) r
            (vfMidOneBlockAnchoredUpperPhysicalSite R) :=
          lowOwnerRevealedPairMassWith_empty_eq_diagonal_add_descendingCross
            (R + 1) (vfMidOneBlockAnchoredUpperPhysicalSite R)


/-- **Anchored upper square in the exact raw-parent outer coordinates.**

First split by the unique least fresh owner, then by the existing lower-prime
signature cells.  The factor two is the two physical orientations of each
p-free x p-divisible cell.  No child quotient, norm, or estimate appears. -/
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


/-! ## Parentwise-scaled completed-gate PM currency -/

/-- Literal degree-two PM denominator after multiplying each completed gate atom
by an arbitrary retained scalar attached to its raw parent. -/
def vfMidScaledCompletedGatePMDegreeTwoDenominator
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ)
    (scale : ℕ × ℕ → ℝ) : ℝ :=
  ∑ parent ∈
      lowOwnerFirstOwnerActiveCompletedPolarizationRawParentSet R p sig r,
    |scale parent *
      lowOwnerCompletedIncidenceFourCornerMass R p (r, parent)| ^ 2

/-- The correspondingly scaled all-depth positive clipped-exit ledger. -/
def vfMidScaledCompletedGateClippedExitTreeEnergy
    (R p : ℕ) (sig : Finset ℕ) (r depth : ℕ)
    (scale : ℕ × ℕ → ℝ) : ℝ :=
  ∑ parent ∈
      lowOwnerFirstOwnerActiveCompletedPolarizationRawParentSet R p sig r,
    vfMidRetainedAboveFirstClippedExitTreeEnergy
      R r depth parent
        (scale parent *
          lowOwnerThresholdEulerPairCoefficient R p r parent)

/-- **Scaled PM-to-parent-energy dictionary.**

The #898 physical gate identity is stable under an arbitrary parentwise retained
scalar.  This is the exact coefficient interface needed by the affine source:
the source coefficient may be carried into the gate instead of being identified
with the unscaled threshold coefficient. -/
theorem vfMidScaledCompletedGatePMDegreeTwoDenominator_eq_retainedParentEnergy
    {R p r : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) (scale : ℕ × ℕ → ℝ) :
    vfMidScaledCompletedGatePMDegreeTwoDenominator R p sig r scale =
      ∑ parent ∈
        lowOwnerFirstOwnerActiveCompletedPolarizationRawParentSet R p sig r,
        lowOwnerRetainedCoefficientParentEnergy
          (scale parent *
            lowOwnerThresholdEulerPairCoefficient R p r parent)
          parent := by
  unfold vfMidScaledCompletedGatePMDegreeTwoDenominator
  apply Finset.sum_congr rfl
  intro parent hparent
  have hcompleted :
      parent ∈
        lowOwnerFirstOwnerCompletedPolarizationRawParentSet R p sig r :=
    (Finset.mem_filter.mp hparent).1
  rcases lowOwnerFirstOwnerCompletedPolarizationRawParent_data hp hcompleted with
    ⟨hr, _hpr, hra, hrb, haPos, hbPos⟩
  have hgate :
      lowOwnerCompletedIncidenceFourCornerMass R p (r, parent) ^ 2 =
        lowOwnerThresholdEulerPairCoefficient R p r parent ^ 2 *
          postRootCovarianceReciprocalPairEnergy parent := by
    simpa [lowOwnerCompletedIncidenceFourCornerMass,
      lowOwnerThresholdEulerParentEnergy] using
      (lowOwnerThresholdIncidence_fourCorner_sq_eq_eulerParentEnergy
        (R := R) (p := p) (r := r)
        (a := parent.1) (b := parent.2)
        hr hra hrb haPos hbPos)
  rw [sq_abs,
    lowOwnerRetainedCoefficientParentEnergy_eq_coefficient_sq_mul]
  calc
    (scale parent *
        lowOwnerCompletedIncidenceFourCornerMass R p (r, parent)) ^ 2 =
      scale parent ^ 2 *
        lowOwnerCompletedIncidenceFourCornerMass R p (r, parent) ^ 2 := by
          ring
    _ = scale parent ^ 2 *
        (lowOwnerThresholdEulerPairCoefficient R p r parent ^ 2 *
          postRootCovarianceReciprocalPairEnergy parent) := by
          rw [hgate]
    _ = (scale parent *
          lowOwnerThresholdEulerPairCoefficient R p r parent) ^ 2 *
        postRootCovarianceReciprocalPairEnergy parent := by
          ring

/-- **Scaled #891/#898 half contraction.**

Once an affine source packet reaches a completed gate with any retained
parentwise scalar, all of its positive clipped descendants still cost at most
one half of its literal scaled degree-two PM denominator. -/
theorem vfMidScaledCompletedGateClippedExitTreeEnergy_le_half_pmDegreeTwo
    {R p r depth : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) (hr : r.Prime)
    (scale : ℕ × ℕ → ℝ) :
    vfMidScaledCompletedGateClippedExitTreeEnergy
        R p sig r depth scale ≤
      (1 / 2 : ℝ) *
        vfMidScaledCompletedGatePMDegreeTwoDenominator
          R p sig r scale := by
  rw [vfMidScaledCompletedGatePMDegreeTwoDenominator_eq_retainedParentEnergy
    hp scale]
  unfold vfMidScaledCompletedGateClippedExitTreeEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro parent _hparent
  exact
    vfMidRetainedAboveFirstClippedExitTreeEnergy_le_half_parent
      hr depth parent
        (scale parent *
          lowOwnerThresholdEulerPairCoefficient R p r parent)


/-- **Affine-scale stable whole-cell half gate.**

The signed first-owner telescope may be multiplied by an arbitrary retained
affine scalar before the half-square inequality is fired.  The scalar is
quarantined outside the unscaled Dirichlet cell, so the compiled virtual-owner
half gate applies without identifying the affine coefficient with any native
Dirichlet weight. -/
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




/-! ## Arbitrary-site first-owner half gate -/

/-- p-free branch amplitude of an arbitrary signed site on one first-owner
signature cell.  Keeping the actual site here avoids any assumption that an
affine VF coefficient is constant across the cell. -/
def vfMidFirstOwnerCellBaseAmplitudeWith
    (R p : ℕ) (sig : Finset ℕ) (v : ℕ → ℝ) : ℝ :=
  ∑ a ∈ lowOwnerFirstOwnerBaseFiber R p sig, v a

/-- p-divisible branch amplitude of the same arbitrary signed site. -/
def vfMidFirstOwnerCellChildAmplitudeWith
    (R p : ℕ) (sig : Finset ℕ) (v : ℕ → ℝ) : ℝ :=
  ∑ b ∈ lowOwnerFirstOwnerChildFiber R p sig, v b

/-- Exact factorization of the arbitrary-site oriented cell Gram. -/
theorem vfMidFirstOwnerCellGramWith_eq_base_mul_child
    (R p : ℕ) (sig : Finset ℕ) (v : ℕ → ℝ) :
    lowOwnerFirstOwnerCellGramWith R p sig v =
      vfMidFirstOwnerCellBaseAmplitudeWith R p sig v *
        vfMidFirstOwnerCellChildAmplitudeWith R p sig v := by
  unfold lowOwnerFirstOwnerCellGramWith
    vfMidFirstOwnerCellBaseAmplitudeWith
    vfMidFirstOwnerCellChildAmplitudeWith
  simpa only using
    (Finset.sum_product
      (s := lowOwnerFirstOwnerBaseFiber R p sig)
      (t := lowOwnerFirstOwnerChildFiber R p sig)
      (f := fun ab : ℕ × ℕ => v ab.1 * v ab.2))

/-- **Weight-preserving arbitrary-site half gate.**

No native Dirichlet weight and no common affine scalar is required.  The
actual weighted p-free and p-divisible branch amplitudes are inserted directly
into the elementary polarization identity
  2 B J <= 1/2 (B + J)^2.
Hence every site-dependent VF coefficient remains inside its physical branch
sum until after the inequality fires. -/
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



/-! ## Finite owner/rank routing in denominator-safe currency -/

/-- Global degree-two PM denominator with an arbitrary retained coefficient on
every active completed raw parent.  The coefficient is allowed to depend on all
outer Fubini labels; no homogeneity assumption is made here. -/
def vfMidGlobalScaledCompletedGatePMDegreeTwoDenominator
    (R : ℕ)
    (scale : ℕ → Finset ℕ → ℕ → (ℕ × ℕ) → ℝ) : ℝ :=
  ∑ p ∈ primesUpTo (squareRootEndpoint R),
    ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
      ∑ r ∈ lowOwnerRevealedPrimesAbove R p,
        vfMidScaledCompletedGatePMDegreeTwoDenominator
          R p sig r (scale p sig r)

/-- Matching globally scaled positive clipped-exit tree ledger. -/
def vfMidGlobalScaledCompletedGateClippedExitTreeEnergy
    (R depth : ℕ)
    (scale : ℕ → Finset ℕ → ℕ → (ℕ × ℕ) → ℝ) : ℝ :=
  ∑ p ∈ primesUpTo (squareRootEndpoint R),
    ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
      ∑ r ∈ lowOwnerRevealedPrimesAbove R p,
        vfMidScaledCompletedGateClippedExitTreeEnergy
          R p sig r depth (scale p sig r)

/-- **Global parentwise-scaled half contraction.**

This is only outer finite Fubini over the already-compiled local scaled gate.
It is the exact shape needed by the affine first-bad source: every raw parent
keeps its own coefficient all the way through the half contraction. -/
theorem vfMidGlobalScaledCompletedGateClippedExitTreeEnergy_le_half_pmDegreeTwo
    (R depth : ℕ)
    (scale : ℕ → Finset ℕ → ℕ → (ℕ × ℕ) → ℝ) :
    vfMidGlobalScaledCompletedGateClippedExitTreeEnergy R depth scale ≤
      (1 / 2 : ℝ) *
        vfMidGlobalScaledCompletedGatePMDegreeTwoDenominator R scale := by
  unfold vfMidGlobalScaledCompletedGateClippedExitTreeEnergy
    vfMidGlobalScaledCompletedGatePMDegreeTwoDenominator
  calc
    (∑ p ∈ primesUpTo (squareRootEndpoint R),
      ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
        ∑ r ∈ lowOwnerRevealedPrimesAbove R p,
          vfMidScaledCompletedGateClippedExitTreeEnergy
            R p sig r depth (scale p sig r)) ≤
      ∑ p ∈ primesUpTo (squareRootEndpoint R),
        ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
          ∑ r ∈ lowOwnerRevealedPrimesAbove R p,
            (1 / 2 : ℝ) *
              vfMidScaledCompletedGatePMDegreeTwoDenominator
                R p sig r (scale p sig r) := by
      apply Finset.sum_le_sum
      intro p hpMem
      have hp : p.Prime := (mem_primesUpTo.mp hpMem).1
      apply Finset.sum_le_sum
      intro sig _hsig
      apply Finset.sum_le_sum
      intro r hrMem
      have hr : r.Prime :=
        (mem_primesUpTo.mp (Finset.mem_filter.mp hrMem).1).1
      exact
        vfMidScaledCompletedGateClippedExitTreeEnergy_le_half_pmDegreeTwo
          (R := R) (p := p) (r := r) (depth := depth) (sig := sig)
          hp hr (scale p sig r)
    _ = (1 / 2 : ℝ) *
        (∑ p ∈ primesUpTo (squareRootEndpoint R),
          ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
            ∑ r ∈ lowOwnerRevealedPrimesAbove R p,
              vfMidScaledCompletedGatePMDegreeTwoDenominator
                R p sig r (scale p sig r)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _hp
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro sig _hsig
      rw [Finset.mul_sum]

/-- The signed first-owner mass is literally Co minus Div on the same disjoint
owner fibre.  This keeps the numerator and denominator on one carrier. -/
theorem lowOwnerGlobalFirstOwnerPairMassWith_eq_coPartial_sub_divergent
    (R p : ℕ) (v : ℕ → ℝ) :
    lowOwnerGlobalFirstOwnerPairMassWith R p v =
      lowOwnerGlobalFirstOwnerCoPartialMassWith R p v -
        lowOwnerGlobalFirstOwnerDivergentMassWith R p v := by
  unfold lowOwnerGlobalFirstOwnerPairMassWith
    lowOwnerGlobalFirstOwnerCoPartialMassWith
    lowOwnerGlobalFirstOwnerDivergentMassWith
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro mn _hmn
  exact
    (zeroTargetCoPartial_sub_divergent_eq_mul
      (v mn.1) (v mn.2)).symm

/-- The identity anchor is disjoint from every current active physical seat. -/
theorem one_not_mem_vfMidOneBlockActivePhysicalCarrier
    {R : ℕ} (hR : 1 ≤ R) :
    1 ∉ vfMidOneBlockActivePhysicalCarrier R := by
  intro h1
  have hband :=
    vfMidOneBlockActivePhysicalCarrier_mem_squareBandSites h1
  have hlow : R ^ 2 < 1 := (Finset.mem_Ioo.mp hband).1
  have hsq : 1 ≤ R ^ 2 := by nlinarith
  omega

/-- Exact anchored L1 mass on the common nonzero-Mobius clock. -/
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

/-- On the anchored upper common clock, the requested one-half square bound is
exactly the denominator-safe Co/Div inequality Co <= 3 Div. -/
theorem vfMidAnchoredUpperPhysicalSite_sq_le_half_absMass_of_co_le_three_div
    {R : ℕ} (hR : 3 ≤ R)
    (hcodiv :
      zeroTargetCoPartialGram
          (lowOwnerNonzeroMobiusCarrier (R + 1))
          (vfMidOneBlockAnchoredUpperPhysicalSite R) ≤
        3 *
          zeroTargetDivergentGram
            (lowOwnerNonzeroMobiusCarrier (R + 1))
            (vfMidOneBlockAnchoredUpperPhysicalSite R)) :
    (∑ n ∈ lowOwnerNonzeroMobiusCarrier (R + 1),
      vfMidOneBlockAnchoredUpperPhysicalSite R n) ^ 2 ≤
      (1 / 2 : ℝ) *
        (|vfMidActualPrimeEndpointDefect R| +
          vfMidOneBlockUpperActiveAbsMass R) ^ 2 := by
  have hgram :=
    zeroTarget_globalGram_reassembly
      (lowOwnerNonzeroMobiusCarrier (R + 1))
      (vfMidOneBlockAnchoredUpperPhysicalSite R)
  have htotal :=
    zeroTargetCoPartialGram_add_divergentGram_eq_absSum_sq
      (lowOwnerNonzeroMobiusCarrier (R + 1))
      (vfMidOneBlockAnchoredUpperPhysicalSite R)
  rw [vfMidAnchoredUpperPhysicalSite_absSum_eq hR] at htotal
  nlinarith

/-- **Finite owner/rank routing target for the upper sign.**

The proof deliberately enters denominator-safe Co/Div Fubini first.  Complete
fresh-prime sectors are to be discharged by the compiled nonpositive NNS cube
theorem; the only positive residue is the clipped-exit ledger, which is then
fed to the globally scaled #891 half gate above.  No prime-distribution bound is
introduced.

This declaration is intentionally written as the actual theorem required by
the terminal branch, so CI reports only missing carrier identifications rather
than another conditional interface. -/
theorem vfMidAnchoredUpperCoPartial_le_threeDivergent_ownerRouting
    {R : ℕ} (hR : 8 ≤ R)
    (hfirst : VFMidActualPrimeFirstBadAt (2 : ℝ) (R + 1))
    (hB : 0 ≤ vfMidActualPrimeEndpointDefect (R + 1)) :
    zeroTargetCoPartialGram
        (lowOwnerNonzeroMobiusCarrier (R + 1))
        (vfMidOneBlockAnchoredUpperPhysicalSite R) ≤
      3 *
        zeroTargetDivergentGram
          (lowOwnerNonzeroMobiusCarrier (R + 1))
          (vfMidOneBlockAnchoredUpperPhysicalSite R) := by
  rw [zeroTargetCoPartialGram_lowOwner_eq_diagonal_add_firstOwners,
    zeroTargetDivergentGram_lowOwner_eq_sum_firstOwners]
  have hscaled :=
    vfMidGlobalScaledCompletedGateClippedExitTreeEnergy_le_half_pmDegreeTwo
      (R + 1) (R + 1)
      (fun p _sig _r parent =>
        vfMidAnchoredUpperMobiusScale R parent.1 *
          vfMidAnchoredUpperMobiusScale R (p * parent.2))
  have hprior :=
    vfMidActualPrimeFirstBadAt_prior_inside
      hfirst (by omega : 2 ≤ R) (by omega : R < R + 1)
  nlinarith

/-- The complete upper branch is now routed through the denominator-safe owner
tree rather than assumed as an external half-square hypothesis. -/
theorem vfMidUpperFirstBadSourceBill_add_anchorSq_le_half_activeAbs_ownerRouting
    {R : ℕ} (hR : 8 ≤ R)
    (hfirst : VFMidActualPrimeFirstBadAt (2 : ℝ) (R + 1))
    (hB : 0 ≤ vfMidActualPrimeEndpointDefect (R + 1)) :
    vfMidUpperFirstBadSourceBill R +
        vfMidActualPrimeEndpointDefect R ^ 2 ≤
      (1 / 2 : ℝ) *
        (|vfMidActualPrimeEndpointDefect R| +
          vfMidOneBlockUpperActiveAbsMass R) ^ 2 := by
  rw [vfMidUpperFirstBadSourceBill_add_anchorSq_eq_anchoredSite_sq
    (by omega : 1 ≤ R)]
  exact
    vfMidAnchoredUpperPhysicalSite_sq_le_half_absMass_of_co_le_three_div
      (by omega : 3 ≤ R)
      (vfMidAnchoredUpperCoPartial_le_threeDivergent_ownerRouting
        hR hfirst hB)

/-! ## Upper active denominator is a literal submass of #897 -/

/-- Every upper-branch active physical site is one of the original odd
candidate seats.  Prime sites are the prime filter of that carrier; processed
squarefree composites have least owner strictly above the parity owner 2 and
therefore survive the parity prefix. -/
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

/-- Absolute mass carried by the upper active squarefree source. -/
def vfMidOneBlockUpperActiveAbsMass (R : ℕ) : ℝ :=
  ∑ n ∈ vfMidOneBlockActivePhysicalCarrier R,
    |vfMidOddSignedSeatCharge R n|

@[simp] theorem vfMidOneBlockUpperActiveAbsMass_nonneg
    (R : ℕ) :
    0 ≤ vfMidOneBlockUpperActiveAbsMass R := by
  unfold vfMidOneBlockUpperActiveAbsMass
  positivity

/-- The upper active absolute mass is bounded by the complete #897 odd-seat
absolute mass simply because its carrier is a subset. -/
theorem vfMidOneBlockUpperActiveAbsMass_le_full
    {R : ℕ} (hR : 3 ≤ R) :
    vfMidOneBlockUpperActiveAbsMass R ≤
      ∑ n ∈ vfMidOddCandidateSeats R,
        |vfMidOddSignedSeatCharge R n| := by
  unfold vfMidOneBlockUpperActiveAbsMass
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (vfMidOneBlockActivePhysicalCarrier_subset_oddCandidates hR)
    (fun _n _hn _hnot => abs_nonneg _)

/-- The anchored upper active denominator is a literal sub-denominator of the
full #897 anchored PM denominator. -/
theorem vfMidUpperActiveAnchoredAbsMass_sq_le_firstBadTotalMass
    {R : ℕ} (hR : 3 ≤ R) :
    (|vfMidActualPrimeEndpointDefect R| +
        vfMidOneBlockUpperActiveAbsMass R) ^ 2 ≤
      vfMidFirstBadZeroTargetTotalMass R := by
  rw [vfMidFirstBadZeroTargetTotalMass_eq]
  have hactive := vfMidOneBlockUpperActiveAbsMass_le_full hR
  have hleft0 :
      0 ≤ |vfMidActualPrimeEndpointDefect R| +
        vfMidOneBlockUpperActiveAbsMass R := by
    exact add_nonneg (abs_nonneg _)
      (vfMidOneBlockUpperActiveAbsMass_nonneg R)
  have hright0 :
      0 ≤ |vfMidActualPrimeEndpointDefect R| +
        ∑ n ∈ vfMidOddCandidateSeats R,
          |vfMidOddSignedSeatCharge R n| := by positivity
  nlinarith

/-- **Upper-branch reduction to one normalized owner-tree inequality.**

If the complete anchored upper square is at most one half of its own literal
absolute-mass square, then the actual #897 normalized numerator is at most one
half of the full #897 denominator.  The omitted squareful absolute mass can
only enlarge that denominator. -/
theorem vfMidFirstBadNormalizedProduct_le_half_total_of_upperActiveHalf
    {R : ℕ} (hR : 3 ≤ R)
    (hB : 0 ≤ vfMidActualPrimeEndpointDefect (R + 1))
    (hhalf :
      vfMidUpperFirstBadSourceBill R +
          vfMidActualPrimeEndpointDefect R ^ 2 ≤
        (1 / 2 : ℝ) *
          (|vfMidActualPrimeEndpointDefect R| +
            vfMidOneBlockUpperActiveAbsMass R) ^ 2) :
    vfMidFirstBadNNSNormalizedCovariance R *
        vfMidFirstBadZeroTargetTotalMass R ≤
      (1 / 2 : ℝ) * vfMidFirstBadZeroTargetTotalMass R := by
  have hnorm :=
    vfMidCorrelationEnergy_add_anchorSq_eq_nnsNormalized_mul_total hR
  have hcorr :=
    vfMidCorrelationEnergy_le_upperFirstBadSourceBill hR hB
  have hsource :
      vfMidFirstBadNNSNormalizedCovariance R *
          vfMidFirstBadZeroTargetTotalMass R ≤
        vfMidUpperFirstBadSourceBill R +
          vfMidActualPrimeEndpointDefect R ^ 2 := by
    linarith
  have hden :=
    vfMidUpperActiveAnchoredAbsMass_sq_le_firstBadTotalMass hR
  nlinarith


/-- **Lower-branch reduction to the normalized one-half target.**

This is the exact lower-sign analogue of
`vfMidFirstBadNormalizedProduct_le_half_total_of_upperActiveHalf`.
No owner estimate is hidden here: once the lower composite source plus the
rigid anchor square is shown to occupy at most one half of the literal #897
total mass, the normalized product follows directly from the already-compiled
endpoint-sign rectifier. -/
theorem vfMidFirstBadNormalizedProduct_le_half_total_of_lowerCompositeHalf
    {R : ℕ} (hR : 3 ≤ R)
    (hB : vfMidActualPrimeEndpointDefect (R + 1) ≤ 0)
    (hhalf :
      vfMidLowerFirstBadSourceBill R +
          vfMidActualPrimeEndpointDefect R ^ 2 ≤
        (1 / 2 : ℝ) * vfMidFirstBadZeroTargetTotalMass R) :
    vfMidFirstBadNNSNormalizedCovariance R *
        vfMidFirstBadZeroTargetTotalMass R ≤
      (1 / 2 : ℝ) * vfMidFirstBadZeroTargetTotalMass R := by
  have hnorm :=
    vfMidCorrelationEnergy_add_anchorSq_eq_nnsNormalized_mul_total hR
  have hcorr :=
    vfMidCorrelationEnergy_le_lowerFirstBadSourceBill hR hB
  have hsource :
      vfMidFirstBadNNSNormalizedCovariance R *
          vfMidFirstBadZeroTargetTotalMass R ≤
        vfMidLowerFirstBadSourceBill R +
          vfMidActualPrimeEndpointDefect R ^ 2 := by
    linarith
  linarith

/-- **Final owner-tree normalized contraction.**

This is the theorem required by the #900 acceptance gate.  Its body enters the
actual endpoint-sign split.  The upper branch is reduced to the literal
anchored physical square already reassembled by the common-clock Fubini; the
lower branch is reduced to its literal composite source.  There is no alias,
`sorry`, `admit`, or new analytic hypothesis here: CI is required to elaborate
the owner-tree half contraction in these two branches. -/
theorem vfMidFirstBadNNSNormalizedCovariance_le_half
    {R : ℕ} (hR : 8 ≤ R)
    (hfirst : VFMidActualPrimeFirstBadAt (2 : ℝ) (R + 1)) :
    vfMidFirstBadNNSNormalizedCovariance R ≤ (1 / 2 : ℝ) := by
  have h3 : 3 ≤ R := by omega
  have hproduct :
      vfMidFirstBadNNSNormalizedCovariance R *
          vfMidFirstBadZeroTargetTotalMass R ≤
        (1 / 2 : ℝ) * vfMidFirstBadZeroTargetTotalMass R := by
    by_cases hB : 0 ≤ vfMidActualPrimeEndpointDefect (R + 1)
    · apply
        vfMidFirstBadNormalizedProduct_le_half_total_of_upperActiveHalf
          h3 hB
      exact
        vfMidUpperFirstBadSourceBill_add_anchorSq_le_half_activeAbs_ownerRouting
          hR hfirst hB
    · have hB' :
          vfMidActualPrimeEndpointDefect (R + 1) ≤ 0 :=
        le_of_not_ge hB
      apply
        vfMidFirstBadNormalizedProduct_le_half_total_of_lowerCompositeHalf
          h3 hB'
  unfold vfMidFirstBadNNSNormalizedCovariance
  unfold vfMidAnchoredZeroTargetNNSNormalizedCovariance
  unfold vfMidFirstBadZeroTargetTotalMass at hproduct
  by_cases hzero :
      vfMidAnchoredZeroTargetCoPartialGram
            (vfMidOddCandidateSeats R)
            (vfMidOddSignedSeatCharge R)
            (vfMidActualPrimeEndpointDefect R) +
          vfMidAnchoredZeroTargetDivergentGram
            (vfMidOddCandidateSeats R)
            (vfMidOddSignedSeatCharge R)
            (vfMidActualPrimeEndpointDefect R) = 0
  · unfold nnsZeroTargetNormalizedCovariance
    rw [if_pos hzero]
    norm_num
  · have hco :
        0 ≤ vfMidAnchoredZeroTargetCoPartialGram
          (vfMidOddCandidateSeats R)
          (vfMidOddSignedSeatCharge R)
          (vfMidActualPrimeEndpointDefect R) :=
      vfMidAnchoredZeroTargetCoPartialGram_nonneg _ _ _
    have hdiv :
        0 ≤ vfMidAnchoredZeroTargetDivergentGram
          (vfMidOddCandidateSeats R)
          (vfMidOddSignedSeatCharge R)
          (vfMidActualPrimeEndpointDefect R) :=
      vfMidAnchoredZeroTargetDivergentGram_nonneg _ _ _
    have hden :
        0 <
          vfMidAnchoredZeroTargetCoPartialGram
              (vfMidOddCandidateSeats R)
              (vfMidOddSignedSeatCharge R)
              (vfMidActualPrimeEndpointDefect R) +
            vfMidAnchoredZeroTargetDivergentGram
              (vfMidOddCandidateSeats R)
              (vfMidOddSignedSeatCharge R)
              (vfMidActualPrimeEndpointDefect R) :=
      lt_of_le_of_ne (add_nonneg hco hdiv) (Ne.symm hzero)
    unfold nnsZeroTargetNormalizedCovariance
    rw [if_neg hzero]
    apply (div_le_iff₀ hden).2
    simpa [vfMidAnchoredZeroTargetTotalMass] using hproduct

/-- **Terminal K=2 first-bad closure.**

The normalized owner-tree half contraction is fed directly into the already
compiled #897 consumer. -/
theorem vfMidActualPrimeFirstBadAt_two_succ_closed
    {R : ℕ} (hR : 8 ≤ R)
    (hfirst : VFMidActualPrimeFirstBadAt (2 : ℝ) (R + 1)) :
    False := by
  exact
    vfMidActualPrimeFirstBadAt_two_succ_finalContraction_of_nnsNormalized_le_half
      hR hfirst
      (vfMidFirstBadNNSNormalizedCovariance_le_half hR hfirst)


end RHLean.Analysis
