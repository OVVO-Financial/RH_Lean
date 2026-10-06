import Mathlib
import «research.VF_MID_ANCHORED_CODIV_GATE_INLET»
import «research.VF_MID_GLOBAL_FIRST_BAD_RADIAL_BUDGET»
import «research.GLOBAL_RETURNED_CORE_GLOBAL_DESCENDING_SITE_FUBINI»

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
    {R : ℕ} (hR : 3 ≤ R) :
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

/-- Zero-extension of the literal physical active source to the common clock.
The support test is deliberately the physical carrier membership, so all owner
assignment happens before child stripping. -/
def vfMidOneBlockActivePhysicalSite (R n : ℕ) : ℝ :=
  if n ∈ vfMidOneBlockActivePhysicalCarrier R then
    vfMidOddSignedSeatCharge R n
  else 0

/-- Zero-extension preserves the exact one-dimensional active source mass. -/
theorem vfMidOneBlockActivePhysicalSite_sum_eq_activeSource
    {R : ℕ} (hR : 3 ≤ R) :
    (∑ n ∈ lowOwnerNonzeroMobiusCarrier (R + 1),
      vfMidOneBlockActivePhysicalSite R n) =
      vfMidOneBlockPrimeSeatCharge R +
        vfMidOneBlockProcessedSquarefreeCharge R := by
  have hsub :=
    vfMidOneBlockActivePhysicalCarrier_subset_lowOwner_succ hR
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
    {R : ℕ} (hR : 3 ≤ R) :
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
  rw [vfMidOneBlockActivePhysicalSite_sum_eq_activeSource hR] at hpair
  exact hpair


end RHLean.Analysis
