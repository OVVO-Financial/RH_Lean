import Mathlib
import «research.VF_MID_RECURSIVE_SCALE_DESCENT»
import «research.VF_MID_SQUARE_WHEEL_BACKLOG»
import «research.VF_MID_ALIGNED_STEP_GRAPH»

/-!
# Recursive VF remainder bound by dynamic prefix wheels

For a fixed parent square block R, collect all children stripped from the
parity-late recursive owner fibres.  PR #850 proves those owner fibres are
pairwise disjoint for R >= 7.

This file groups the recursive child population by the repository's native
square blocks

    S^2 < m <= (S+1)^2.

On each child block S, the parent uniform charge w_R is transferred to the
native lower-scale VF charge w_S - 1_Prime(m).  The exact discrepancy is

    prime-child correction + population * (w_R - w_S).

The prime-child correction is a subset of the actual prime population P_S in
that square block, hence is bounded by every prefix-wheel envelope available at
scale S.  Thus, for every wheel cutoff T <= S,

    |Rem_{R,S}| <= E_T(S) + N_{R,S} |w_R - w_S|,

where

    E_T(S) = phi(Q_T) * (floor(2S / Q_T) + 1).

No probabilistic independence, PNT-rate estimate, Li approximation, or RH
hypothesis is used.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Union of every parity-late recursive stripped-child fibre in parent block R. -/
def vfMidRecursiveChildCarrier (R : ℕ) : Finset ℕ :=
  (vfMidSquareBandLateRecursiveOwners R).biUnion
    (vfMidSquareBandCompositeOwnerChildren R)

/-- #850 disjointness upgraded to pairwise disjointness of the whole recursive
owner family. -/
theorem vfMidRecursiveChildFibers_pairwiseDisjoint
    (R : ℕ) (hR : 7 ≤ R) :
    Set.PairwiseDisjoint (↑(vfMidSquareBandLateRecursiveOwners R))
      (vfMidSquareBandCompositeOwnerChildren R) := by
  intro p hp q hq hpq
  exact vfMidLateRecursiveOwner_children_disjoint hR hp hq hpq

/-- Therefore the union child population is exactly the sum of the owner-fibre
populations: no multiplicity is lost when the recursive tree is flattened. -/
theorem vfMidRecursiveChildCarrier_card_eq_sum
    (R : ℕ) (hR : 7 ≤ R) :
    (vfMidRecursiveChildCarrier R).card =
      ∑ p ∈ vfMidSquareBandLateRecursiveOwners R,
        (vfMidSquareBandCompositeOwnerChildren R p).card := by
  unfold vfMidRecursiveChildCarrier
  have h := Finset.sum_biUnion
    (vfMidRecursiveChildFibers_pairwiseDisjoint R hR)
    (f := fun _ : ℕ => (1 : ℕ))
  simpa using h

/-- Descended children from R which land in the repository square block
(S^2,(S+1)^2].  This convention covers square children at the previous block's
right endpoint and matches the exact prime-supply API. -/
def vfMidRecursiveChildrenInBlock (R S : ℕ) : Finset ℕ :=
  (vfMidRecursiveChildCarrier R) ∩
    Finset.Ioc (S ^ 2) ((S + 1) ^ 2)

/-- Any populated child block lies strictly below its parent scale. -/
theorem vfMidRecursiveChild_block_lt
    {R S m : ℕ} (hR : 7 ≤ R)
    (hm : m ∈ vfMidRecursiveChildrenInBlock R S) :
    S < R := by
  rcases Finset.mem_inter.mp hm with ⟨hmCarrier, hmBlock⟩
  rcases Finset.mem_biUnion.mp hmCarrier with ⟨p, hp, hmChild⟩
  have hmLt : m < R ^ 2 :=
    vfMidLateRecursiveOwner_child_lt_square hR hp hmChild
  have hSLt : S ^ 2 < m := (Finset.mem_Ioc.mp hmBlock).1
  by_contra hnot
  have hRS : R ≤ S := Nat.le_of_not_gt hnot
  have hSq : R ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left hRS 2
  omega

/-- Distinct native child square blocks are disjoint.  This is the physical
population separation behind the later budget contraction. -/
theorem vfMidRecursiveChildrenInBlock_pairwiseDisjoint
    (R : ℕ) :
    Set.PairwiseDisjoint (↑(Finset.Ico 2 R))
      (vfMidRecursiveChildrenInBlock R) := by
  intro S hS T hT hST
  rw [Finset.disjoint_left]
  intro m hmS hmT
  rcases Finset.mem_inter.mp hmS with ⟨_hmCarS, hmBlockS⟩
  rcases Finset.mem_inter.mp hmT with ⟨_hmCarT, hmBlockT⟩
  rcases Finset.mem_Ioc.mp hmBlockS with ⟨hmSLow, hmSHigh⟩
  rcases Finset.mem_Ioc.mp hmBlockT with ⟨hmTLow, hmTHigh⟩
  rcases lt_or_gt_of_ne hST with hSLT | hTLS
  · have hSucc : S + 1 ≤ T := by omega
    have hSq : (S + 1) ^ 2 ≤ T ^ 2 :=
      Nat.pow_le_pow_left hSucc 2
    omega
  · have hSucc : T + 1 ≤ S := by omega
    have hSq : (T + 1) ^ 2 ≤ S ^ 2 :=
      Nat.pow_le_pow_left hSucc 2
    omega

/-- Descended child populations in distinct native square blocks cannot
double-count.  Hence the sum of all child-block populations below R is bounded
by the flattened #850 recursive child population. -/
theorem vfMidRecursiveChildrenInBlock_sum_card_le_carrier
    (R : ℕ) :
    (∑ S ∈ Finset.Ico 2 R,
      (vfMidRecursiveChildrenInBlock R S).card) ≤
        (vfMidRecursiveChildCarrier R).card := by
  let I : Finset ℕ := Finset.Ico 2 R
  let F : ℕ → Finset ℕ := vfMidRecursiveChildrenInBlock R
  have hpair : Set.PairwiseDisjoint (↑I) F := by
    simpa [I, F] using vfMidRecursiveChildrenInBlock_pairwiseDisjoint R
  have hunion :
      (I.biUnion F).card = ∑ S ∈ I, (F S).card := by
    have h := Finset.sum_biUnion hpair (f := fun _ : ℕ => (1 : ℕ))
    simpa using h
  have hsubset : I.biUnion F ⊆ vfMidRecursiveChildCarrier R := by
    intro m hm
    rcases Finset.mem_biUnion.mp hm with ⟨S, _hS, hmF⟩
    exact (Finset.mem_inter.mp hmF).1
  calc
    (∑ S ∈ Finset.Ico 2 R,
      (vfMidRecursiveChildrenInBlock R S).card) =
        (I.biUnion F).card := by
          rw [hunion]
          rfl
    _ ≤ (vfMidRecursiveChildCarrier R).card :=
      Finset.card_le_card hsubset

/-- For R >= 7 every recursive child belongs to one of the native direct
square blocks indexed by 2 <= S < R.  The right-closed block convention is
handled canonically by S = floor(sqrt(m-1)). -/
theorem vfMidRecursiveChildCarrier_subset_childBlocks
    (R : ℕ) (hR : 7 ≤ R) :
    vfMidRecursiveChildCarrier R ⊆
      (Finset.Ico 2 R).biUnion (vfMidRecursiveChildrenInBlock R) := by
  intro m hm
  rcases Finset.mem_biUnion.mp hm with ⟨p, hp, hmChild⟩
  have hmGt : 2 * R < m :=
    vfMidLateRecursiveOwner_child_gt_two_mul hR hp hmChild
  have hmLt : m < R ^ 2 :=
    vfMidLateRecursiveOwner_child_lt_square hR hp hmChild
  let S : ℕ := Nat.sqrt (m - 1)
  have hSsq : S ^ 2 ≤ m - 1 := by
    dsimp [S]
    exact Nat.sqrt_le' (m - 1)
  have hmNext : m - 1 < (S + 1) ^ 2 := by
    dsimp [S]
    exact Nat.lt_succ_sqrt' (m - 1)
  have hS2 : 2 ≤ S := by
    dsimp [S]
    apply (Nat.le_sqrt).2
    omega
  have hSR : S < R := by
    by_contra hnot
    have hRS : R ≤ S := Nat.le_of_not_gt hnot
    have hpow : R ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left hRS 2
    omega
  apply Finset.mem_biUnion.mpr
  refine ⟨S, Finset.mem_Ico.mpr ⟨hS2, hSR⟩, ?_⟩
  apply Finset.mem_inter.mpr
  constructor
  · exact hm
  · apply Finset.mem_Ioc.mpr
    constructor <;> omega

/-- Conversely every indexed child block is a subset of the flattened
recursive child carrier. -/
theorem vfMidRecursiveChildBlocks_subset_carrier
    (R : ℕ) :
    (Finset.Ico 2 R).biUnion (vfMidRecursiveChildrenInBlock R) ⊆
      vfMidRecursiveChildCarrier R := by
  intro m hm
  rcases Finset.mem_biUnion.mp hm with ⟨S, _hS, hmBlock⟩
  exact (Finset.mem_inter.mp hmBlock).1

/-- **Exact child-scale partition.**  For R >= 7 the native direct square
blocks 2 <= S < R partition the entire recursive child carrier. -/
theorem vfMidRecursiveChildBlocks_biUnion_eq_carrier
    (R : ℕ) (hR : 7 ≤ R) :
    (Finset.Ico 2 R).biUnion (vfMidRecursiveChildrenInBlock R) =
      vfMidRecursiveChildCarrier R := by
  apply Finset.Subset.antisymm
  · exact vfMidRecursiveChildBlocks_subset_carrier R
  · exact vfMidRecursiveChildCarrier_subset_childBlocks R hR

/-- Exact population conservation across native child square scales. -/
theorem vfMidRecursiveChildrenInBlock_sum_card_eq_carrier
    (R : ℕ) (hR : 7 ≤ R) :
    (∑ S ∈ Finset.Ico 2 R,
      (vfMidRecursiveChildrenInBlock R S).card) =
        (vfMidRecursiveChildCarrier R).card := by
  let I : Finset ℕ := Finset.Ico 2 R
  let F : ℕ → Finset ℕ := vfMidRecursiveChildrenInBlock R
  have hpair : Set.PairwiseDisjoint (↑I) F := by
    simpa [I, F] using vfMidRecursiveChildrenInBlock_pairwiseDisjoint R
  have hunion :
      (I.biUnion F).card = ∑ S ∈ I, (F S).card := by
    have h := Finset.sum_biUnion hpair (f := fun _ : ℕ => (1 : ℕ))
    simpa using h
  have heq : I.biUnion F = vfMidRecursiveChildCarrier R := by
    simpa [I, F] using vfMidRecursiveChildBlocks_biUnion_eq_carrier R hR
  calc
    (∑ S ∈ Finset.Ico 2 R,
      (vfMidRecursiveChildrenInBlock R S).card) =
        (I.biUnion F).card := by
          rw [hunion]
          rfl
    _ = (vfMidRecursiveChildCarrier R).card := by rw [heq]

/-- Prime children in one descended square block. -/
def vfMidRecursivePrimeChildrenInBlock (R S : ℕ) : Finset ℕ :=
  (vfMidRecursiveChildrenInBlock R S).filter Nat.Prime

/-- Every prime child in descended block S is literally an element of the
repository direct prime band at S. -/
theorem vfMidRecursivePrimeChildrenInBlock_subset_directPrimeBand
    (R S : ℕ) :
    vfMidRecursivePrimeChildrenInBlock R S ⊆
      vfMidDirectPrimeBand S := by
  intro m hm
  rcases Finset.mem_filter.mp hm with ⟨hmChild, hmPrime⟩
  rcases Finset.mem_inter.mp hmChild with ⟨_hmCarrier, hmBlock⟩
  exact Finset.mem_filter.mpr ⟨hmBlock, hmPrime⟩

/-- The prime-correction population on a descended block cannot exceed the
actual prime supply of that block. -/
theorem vfMidRecursivePrimeChildrenInBlock_card_le_primeSupply
    (R S : ℕ) :
    (vfMidRecursivePrimeChildrenInBlock R S).card ≤
      vfMidIntegerBlockPrimeSupply S := by
  unfold vfMidIntegerBlockPrimeSupply
  exact Finset.card_le_card
    (vfMidRecursivePrimeChildrenInBlock_subset_directPrimeBand R S)

/-- Dynamic multi-resolution cap: every prefix wheel T <= S bounds the prime
correction channel on the descended child block S. -/
theorem vfMidRecursivePrimeChildrenInBlock_card_le_prefixWheelEnvelope
    (R S T : ℕ) (hS : 2 ≤ S) (hTS : T ≤ S) :
    (vfMidRecursivePrimeChildrenInBlock R S).card ≤
      vfMidPrefixWheelEnvelope T S := by
  exact
    (vfMidRecursivePrimeChildrenInBlock_card_le_primeSupply R S).trans
      (vfMidIntegerBlockPrimeSupply_le_prefixWheelEnvelope T S hS hTS)

/-- Prime children are also bounded by the actual descended population in
their child block. -/
theorem vfMidRecursivePrimeChildrenInBlock_card_le_population
    (R S : ℕ) :
    (vfMidRecursivePrimeChildrenInBlock R S).card ≤
      (vfMidRecursiveChildrenInBlock R S).card := by
  unfold vfMidRecursivePrimeChildrenInBlock
  exact Finset.card_filter_le _ _

/-- **Population-clipped dynamic wheel cap.**  The prime-correction channel is
bounded simultaneously by the actual child population and by every admissible
prefix-wheel envelope.  This is the useful form for descent because empty or
sparse child blocks pay no artificial wheel cost. -/
theorem vfMidRecursivePrimeChildrenInBlock_card_le_min_population_prefixWheel
    (R S T : ℕ) (hS : 2 ≤ S) (hTS : T ≤ S) :
    (vfMidRecursivePrimeChildrenInBlock R S).card ≤
      min (vfMidRecursiveChildrenInBlock R S).card
        (vfMidPrefixWheelEnvelope T S) := by
  apply le_min
  · exact vfMidRecursivePrimeChildrenInBlock_card_le_population R S
  · exact
      vfMidRecursivePrimeChildrenInBlock_card_le_prefixWheelEnvelope
        R S T hS hTS

/-- Crude but universal fallback: the prime correction on child block S is at
most S. -/
theorem vfMidRecursivePrimeChildrenInBlock_card_le_S
    (R S : ℕ) (hS : 2 ≤ S) :
    (vfMidRecursivePrimeChildrenInBlock R S).card ≤ S := by
  exact
    (vfMidRecursivePrimeChildrenInBlock_card_le_primeSupply R S).trans
      (vfMidIntegerBlockPrimeSupply_le_R S hS)

/-- Native lower-scale signed VF charge carried by the descended population in
block S. -/
def vfMidRecursiveNativeChargeInBlock (R S : ℕ) : ℝ :=
  ∑ m ∈ vfMidRecursiveChildrenInBlock R S,
    vfMidOddSignedSeatCharge S m

/-- Exact number of prime children, cast to the charge field. -/
def vfMidRecursivePrimeCorrectionInBlock (R S : ℕ) : ℝ :=
  ((vfMidRecursivePrimeChildrenInBlock R S).card : ℝ)

/-- Explicit change of uniform VF seat weight when the parent charge is
re-expressed at child scale S. -/
def vfMidRecursiveWeightTransferInBlock (R S : ℕ) : ℝ :=
  ((vfMidRecursiveChildrenInBlock R S).card : ℝ) *
    (vfMidOddFractionalPrimeSeatWeight R -
      vfMidOddFractionalPrimeSeatWeight S)

/-- The complete local transfer remainder. -/
def vfMidRecursiveRemainderInBlock (R S : ℕ) : ℝ :=
  vfMidRecursivePrimeCorrectionInBlock R S +
    vfMidRecursiveWeightTransferInBlock R S

/-- Pointwise transfer identity replacing the unavailable Möbius sign-isometry. -/
theorem vfMidParentRecursiveCharge_transfer
    (R S m : ℕ) :
    vfMidOddFractionalPrimeSeatWeight R =
      vfMidOddSignedSeatCharge S m +
        vfMidActualPrimeSeatMass m +
        (vfMidOddFractionalPrimeSeatWeight R -
          vfMidOddFractionalPrimeSeatWeight S) := by
  unfold vfMidOddSignedSeatCharge
  ring

/-- On an arbitrary descended child block, the total actual 0/1 prime mass is
exactly the prime-child cardinality. -/
theorem vfMidActualPrimeSeatMass_sum_recursiveChildrenInBlock
    (R S : ℕ) :
    (∑ m ∈ vfMidRecursiveChildrenInBlock R S,
      vfMidActualPrimeSeatMass m) =
        vfMidRecursivePrimeCorrectionInBlock R S := by
  classical
  unfold vfMidRecursivePrimeCorrectionInBlock
    vfMidRecursivePrimeChildrenInBlock
    vfMidActualPrimeSeatMass
  simp

/-- Exact blockwise parent-to-native-child transfer:

    w_R N_{R,S} = G^native_{R,S} + Rem_{R,S}.

This is an identity before any norm or inequality is taken. -/
theorem vfMidRecursiveParentCharge_eq_native_add_remainder
    (R S : ℕ) :
    vfMidOddFractionalPrimeSeatWeight R *
        ((vfMidRecursiveChildrenInBlock R S).card : ℝ) =
      vfMidRecursiveNativeChargeInBlock R S +
        vfMidRecursiveRemainderInBlock R S := by
  have hprime :=
    vfMidActualPrimeSeatMass_sum_recursiveChildrenInBlock R S
  unfold vfMidRecursiveNativeChargeInBlock
    vfMidRecursiveRemainderInBlock
    vfMidRecursiveWeightTransferInBlock
  rw [← hprime]
  unfold vfMidOddSignedSeatCharge
  rw [Finset.sum_sub_distrib]
  simp
  ring

/-- **Prefix-wheel remainder bound.**  For every admissible wheel cutoff T <= S,

    |Rem_{R,S}| <= E_T(S) + N_{R,S} |w_R-w_S|.

The first term bounds every possible prime child by the deterministic prefix
wheel; the second is the completely explicit change of VF seat weight. -/
theorem abs_vfMidRecursiveRemainderInBlock_le_prefixWheel
    (R S T : ℕ) (hS : 2 ≤ S) (hTS : T ≤ S) :
    |vfMidRecursiveRemainderInBlock R S| ≤
      (vfMidPrefixWheelEnvelope T S : ℝ) +
        ((vfMidRecursiveChildrenInBlock R S).card : ℝ) *
          |vfMidOddFractionalPrimeSeatWeight R -
            vfMidOddFractionalPrimeSeatWeight S| := by
  have hcapNat :=
    vfMidRecursivePrimeChildrenInBlock_card_le_prefixWheelEnvelope
      R S T hS hTS
  have hcap :
      vfMidRecursivePrimeCorrectionInBlock R S ≤
        (vfMidPrefixWheelEnvelope T S : ℝ) := by
    unfold vfMidRecursivePrimeCorrectionInBlock
    exact_mod_cast hcapNat
  have hprime0 :
      0 ≤ vfMidRecursivePrimeCorrectionInBlock R S := by
    unfold vfMidRecursivePrimeCorrectionInBlock
    positivity
  unfold vfMidRecursiveRemainderInBlock
    vfMidRecursiveWeightTransferInBlock
  calc
    |vfMidRecursivePrimeCorrectionInBlock R S +
        ((vfMidRecursiveChildrenInBlock R S).card : ℝ) *
          (vfMidOddFractionalPrimeSeatWeight R -
            vfMidOddFractionalPrimeSeatWeight S)|
        ≤ |vfMidRecursivePrimeCorrectionInBlock R S| +
            |((vfMidRecursiveChildrenInBlock R S).card : ℝ) *
              (vfMidOddFractionalPrimeSeatWeight R -
                vfMidOddFractionalPrimeSeatWeight S)| := abs_add_le _ _
    _ = vfMidRecursivePrimeCorrectionInBlock R S +
          ((vfMidRecursiveChildrenInBlock R S).card : ℝ) *
            |vfMidOddFractionalPrimeSeatWeight R -
              vfMidOddFractionalPrimeSeatWeight S| := by
          rw [abs_of_nonneg hprime0, abs_mul,
            abs_of_nonneg (by positivity :
              0 ≤ ((vfMidRecursiveChildrenInBlock R S).card : ℝ))]
    _ ≤ (vfMidPrefixWheelEnvelope T S : ℝ) +
          ((vfMidRecursiveChildrenInBlock R S).card : ℝ) *
            |vfMidOddFractionalPrimeSeatWeight R -
              vfMidOddFractionalPrimeSeatWeight S| := by
          linarith

/-- **Population-clipped prefix-wheel remainder bound.**

This sharpens the raw wheel estimate by charging the prime-correction channel
only for seats which actually occur in the descended child population:

    |Rem_{R,S}| <= min(N_{R,S}, E_T(S)) + N_{R,S}|w_R-w_S|.

It is therefore zero in the prime-correction channel whenever the child block
is empty, which is the form required for a global budget contraction. -/
theorem abs_vfMidRecursiveRemainderInBlock_le_minPopulationPrefixWheel
    (R S T : ℕ) (hS : 2 ≤ S) (hTS : T ≤ S) :
    |vfMidRecursiveRemainderInBlock R S| ≤
      ((min (vfMidRecursiveChildrenInBlock R S).card
        (vfMidPrefixWheelEnvelope T S) : ℕ) : ℝ) +
        ((vfMidRecursiveChildrenInBlock R S).card : ℝ) *
          |vfMidOddFractionalPrimeSeatWeight R -
            vfMidOddFractionalPrimeSeatWeight S| := by
  have hcapNat :=
    vfMidRecursivePrimeChildrenInBlock_card_le_min_population_prefixWheel
      R S T hS hTS
  have hcap :
      vfMidRecursivePrimeCorrectionInBlock R S ≤
        ((min (vfMidRecursiveChildrenInBlock R S).card
          (vfMidPrefixWheelEnvelope T S) : ℕ) : ℝ) := by
    unfold vfMidRecursivePrimeCorrectionInBlock
    exact_mod_cast hcapNat
  have hprime0 :
      0 ≤ vfMidRecursivePrimeCorrectionInBlock R S := by
    unfold vfMidRecursivePrimeCorrectionInBlock
    positivity
  unfold vfMidRecursiveRemainderInBlock
    vfMidRecursiveWeightTransferInBlock
  calc
    |vfMidRecursivePrimeCorrectionInBlock R S +
        ((vfMidRecursiveChildrenInBlock R S).card : ℝ) *
          (vfMidOddFractionalPrimeSeatWeight R -
            vfMidOddFractionalPrimeSeatWeight S)|
        ≤ |vfMidRecursivePrimeCorrectionInBlock R S| +
            |((vfMidRecursiveChildrenInBlock R S).card : ℝ) *
              (vfMidOddFractionalPrimeSeatWeight R -
                vfMidOddFractionalPrimeSeatWeight S)| := abs_add_le _ _
    _ = vfMidRecursivePrimeCorrectionInBlock R S +
          ((vfMidRecursiveChildrenInBlock R S).card : ℝ) *
            |vfMidOddFractionalPrimeSeatWeight R -
              vfMidOddFractionalPrimeSeatWeight S| := by
          rw [abs_of_nonneg hprime0, abs_mul,
            abs_of_nonneg (by positivity :
              0 ≤ ((vfMidRecursiveChildrenInBlock R S).card : ℝ))]
    _ ≤ ((min (vfMidRecursiveChildrenInBlock R S).card
          (vfMidPrefixWheelEnvelope T S) : ℕ) : ℝ) +
          ((vfMidRecursiveChildrenInBlock R S).card : ℝ) *
            |vfMidOddFractionalPrimeSeatWeight R -
              vfMidOddFractionalPrimeSeatWeight S| := by
          linarith

/-- Universal half-width fallback for the same remainder. -/
theorem abs_vfMidRecursiveRemainderInBlock_le_S
    (R S : ℕ) (hS : 2 ≤ S) :
    |vfMidRecursiveRemainderInBlock R S| ≤
      (S : ℝ) +
        ((vfMidRecursiveChildrenInBlock R S).card : ℝ) *
          |vfMidOddFractionalPrimeSeatWeight R -
            vfMidOddFractionalPrimeSeatWeight S| := by
  have hcapNat :=
    vfMidRecursivePrimeChildrenInBlock_card_le_S R S hS
  have hcap :
      vfMidRecursivePrimeCorrectionInBlock R S ≤ (S : ℝ) := by
    unfold vfMidRecursivePrimeCorrectionInBlock
    exact_mod_cast hcapNat
  have hprime0 :
      0 ≤ vfMidRecursivePrimeCorrectionInBlock R S := by
    unfold vfMidRecursivePrimeCorrectionInBlock
    positivity
  unfold vfMidRecursiveRemainderInBlock
    vfMidRecursiveWeightTransferInBlock
  calc
    |vfMidRecursivePrimeCorrectionInBlock R S +
        ((vfMidRecursiveChildrenInBlock R S).card : ℝ) *
          (vfMidOddFractionalPrimeSeatWeight R -
            vfMidOddFractionalPrimeSeatWeight S)|
        ≤ |vfMidRecursivePrimeCorrectionInBlock R S| +
            |((vfMidRecursiveChildrenInBlock R S).card : ℝ) *
              (vfMidOddFractionalPrimeSeatWeight R -
                vfMidOddFractionalPrimeSeatWeight S)| := abs_add_le _ _
    _ = vfMidRecursivePrimeCorrectionInBlock R S +
          ((vfMidRecursiveChildrenInBlock R S).card : ℝ) *
            |vfMidOddFractionalPrimeSeatWeight R -
              vfMidOddFractionalPrimeSeatWeight S| := by
          rw [abs_of_nonneg hprime0, abs_mul,
            abs_of_nonneg (by positivity :
              0 ≤ ((vfMidRecursiveChildrenInBlock R S).card : ℝ))]
    _ ≤ (S : ℝ) +
          ((vfMidRecursiveChildrenInBlock R S).card : ℝ) *
            |vfMidOddFractionalPrimeSeatWeight R -
              vfMidOddFractionalPrimeSeatWeight S| := by
          linarith


/-! ## Uniform recursive population and weight budgets -/

/-- The complete recursive stripped-child population in parent block R cannot
exceed the R odd candidate seats.  Stripping preserves each owner-fibre
cardinality, recursive owners are a subfamily of all parity-late owners, and
the latter census is exactly the parity-surviving composite population. -/
theorem vfMidRecursiveChildCarrier_card_le_R
    (R : ℕ) (hR : 7 ≤ R) :
    (vfMidRecursiveChildCarrier R).card ≤ R := by
  have hcard :=
    vfMidRecursiveChildCarrier_card_eq_sum R hR
  have hstrip :
      (∑ p ∈ vfMidSquareBandLateRecursiveOwners R,
        (vfMidSquareBandCompositeOwnerChildren R p).card) =
      ∑ p ∈ vfMidSquareBandLateRecursiveOwners R,
        (vfMidSquareBandCompositeOwner R p).card := by
    apply Finset.sum_congr rfl
    intro p _hp
    exact vfMidSquareBandCompositeOwnerChildren_card R p
  have hrec :
      (vfMidRecursiveChildCarrier R).card =
        ∑ p ∈ vfMidSquareBandLateRecursiveOwners R,
          (vfMidSquareBandCompositeOwner R p).card := by
    calc
      (vfMidRecursiveChildCarrier R).card =
          ∑ p ∈ vfMidSquareBandLateRecursiveOwners R,
            (vfMidSquareBandCompositeOwnerChildren R p).card := hcard
      _ = _ := hstrip
  have howners :=
    vfMidSquareBandPrefixComposite_card_eq_sum_lateOwnerCards
      2 R (by omega : 2 ≤ R)
  have hsplit :
      (∑ p ∈ vfMidSquareBandLateOwnerPrimes 2 R,
        (vfMidSquareBandCompositeOwner R p).card) =
      (∑ p ∈ vfMidSquareBandLateTerminalOwners R,
        (vfMidSquareBandCompositeOwner R p).card) +
      (∑ p ∈ vfMidSquareBandLateRecursiveOwners R,
        (vfMidSquareBandCompositeOwner R p).card) := by
    rw [vfMidSquareBandLateOwnerPrimes_eq_terminal_union_recursive,
      Finset.sum_union (vfMidSquareBandLateTerminal_recursive_disjoint R)]
  have hpart :=
    vfMidOddActualComposite_card_add_primeSupply R (by omega : 2 ≤ R)
  rw [hrec]
  rw [← howners] at hsplit
  omega

/-- The odd VF seat weight is nonnegative on every nontrivial square block. -/
theorem vfMidOddFractionalPrimeSeatWeight_nonneg
    (R : ℕ) (hR : 2 ≤ R) :
    0 ≤ vfMidOddFractionalPrimeSeatWeight R := by
  unfold vfMidOddFractionalPrimeSeatWeight
  exact div_nonneg
    (vfMidBandMass_nonneg_of_two_le R hR)
    (by positivity)

/-- Uniform elementary ceiling for every odd VF seat weight. -/
theorem vfMidOddFractionalPrimeSeatWeight_le_three_div_log_four
    (R : ℕ) (hR : 2 ≤ R) :
    vfMidOddFractionalPrimeSeatWeight R ≤
      3 / Real.log 4 := by
  have hmass :=
    vfMidBandMass_le_three_mul_div_log_four R hR
  have hRpos : (0 : ℝ) < (R : ℝ) := by
    exact_mod_cast (show 0 < R by omega)
  unfold vfMidOddFractionalPrimeSeatWeight
  apply (div_le_iff₀ hRpos).2
  calc
    vfMidBandMass R ≤ 3 * (R : ℝ) / Real.log 4 := hmass
    _ = (3 / Real.log 4) * (R : ℝ) := by ring

/-- Two native VF seat weights can differ by at most the common uniform
ceiling, not twice that ceiling, because both weights lie in the same
nonnegative interval [0, 3/log 4]. -/
theorem abs_vfMidOddFractionalPrimeSeatWeight_sub_le_three_div_log_four
    (R S : ℕ) (hR : 2 ≤ R) (hS : 2 ≤ S) :
    |vfMidOddFractionalPrimeSeatWeight R -
      vfMidOddFractionalPrimeSeatWeight S| ≤
        3 / Real.log 4 := by
  have hR0 := vfMidOddFractionalPrimeSeatWeight_nonneg R hR
  have hS0 := vfMidOddFractionalPrimeSeatWeight_nonneg S hS
  have hRu :=
    vfMidOddFractionalPrimeSeatWeight_le_three_div_log_four R hR
  have hSu :=
    vfMidOddFractionalPrimeSeatWeight_le_three_div_log_four S hS
  rw [abs_le]
  constructor <;> linarith

/-- The full scale-transfer weight budget is linear in the parent scale. -/
theorem vfMidRecursiveAggregateWeightTransferBudget_le
    (R : ℕ) (hR : 7 ≤ R) :
    (∑ S ∈ Finset.Ico 2 R,
      ((vfMidRecursiveChildrenInBlock R S).card : ℝ) *
        |vfMidOddFractionalPrimeSeatWeight R -
          vfMidOddFractionalPrimeSeatWeight S|) ≤
      (3 / Real.log 4) * (R : ℝ) := by
  have hC0 : 0 ≤ 3 / Real.log 4 := by
    have hlog : 0 < Real.log 4 := Real.log_pos (by norm_num)
    positivity
  calc
    (∑ S ∈ Finset.Ico 2 R,
      ((vfMidRecursiveChildrenInBlock R S).card : ℝ) *
        |vfMidOddFractionalPrimeSeatWeight R -
          vfMidOddFractionalPrimeSeatWeight S|)
        ≤ ∑ S ∈ Finset.Ico 2 R,
            ((vfMidRecursiveChildrenInBlock R S).card : ℝ) *
              (3 / Real.log 4) := by
          apply Finset.sum_le_sum
          intro S hS
          apply mul_le_mul_of_nonneg_left
          · exact
              abs_vfMidOddFractionalPrimeSeatWeight_sub_le_three_div_log_four
                R S (by omega) (Finset.mem_Ico.mp hS).1
          · positivity
    _ = ((∑ S ∈ Finset.Ico 2 R,
            (vfMidRecursiveChildrenInBlock R S).card : ℕ) : ℝ) *
          (3 / Real.log 4) := by
          push_cast
          rw [Finset.sum_mul]
    _ ≤ (R : ℝ) * (3 / Real.log 4) := by
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast
              (vfMidRecursiveChildrenInBlock_sum_card_le_carrier R).trans
                (vfMidRecursiveChildCarrier_card_le_R R hR)
          · exact hC0
    _ = (3 / Real.log 4) * (R : ℝ) := by ring

/-! ## Aggregate descended remainder -/

/-- Sum of the transfer remainders over every nontrivial child block below R. -/
def vfMidRecursiveAggregateRemainder (R : ℕ) : ℝ :=
  ∑ S ∈ Finset.Ico 2 R, vfMidRecursiveRemainderInBlock R S

/-- Aggregate native lower-scale charge over the same descended square blocks. -/
def vfMidRecursiveAggregateNativeCharge (R : ℕ) : ℝ :=
  ∑ S ∈ Finset.Ico 2 R, vfMidRecursiveNativeChargeInBlock R S

/-- Parent weight carried by the descended populations, grouped by child block. -/
def vfMidRecursiveAggregateParentCharge (R : ℕ) : ℝ :=
  ∑ S ∈ Finset.Ico 2 R,
    vfMidOddFractionalPrimeSeatWeight R *
      ((vfMidRecursiveChildrenInBlock R S).card : ℝ)

/-- Summing the exact local transfer identities gives an exact aggregate
parent/native/remainder ledger before any absolute value is taken. -/
theorem vfMidRecursiveAggregateParentCharge_eq_native_add_remainder
    (R : ℕ) :
    vfMidRecursiveAggregateParentCharge R =
      vfMidRecursiveAggregateNativeCharge R +
        vfMidRecursiveAggregateRemainder R := by
  unfold vfMidRecursiveAggregateParentCharge
    vfMidRecursiveAggregateNativeCharge
    vfMidRecursiveAggregateRemainder
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S _hS
  exact vfMidRecursiveParentCharge_eq_native_add_remainder R S

/-- The aggregate parent charge is exactly the uniform parent weight times
the complete recursive child population. -/
theorem vfMidRecursiveAggregateParentCharge_eq_fullRecursiveCharge
    (R : ℕ) (hR : 7 ≤ R) :
    vfMidRecursiveAggregateParentCharge R =
      vfMidOddFractionalPrimeSeatWeight R *
        ((vfMidRecursiveChildCarrier R).card : ℝ) := by
  unfold vfMidRecursiveAggregateParentCharge
  rw [← Finset.mul_sum]
  have hcard :=
    vfMidRecursiveChildrenInBlock_sum_card_eq_carrier R hR
  have hcardR :
      (∑ S ∈ Finset.Ico 2 R,
        ((vfMidRecursiveChildrenInBlock R S).card : ℝ)) =
          ((vfMidRecursiveChildCarrier R).card : ℝ) := by
    exact_mod_cast hcard
  rw [hcardR]

/-- Hence the aggregate transfer ledger covers the entire recursive child
sector, not merely a selected subfamily of child scales. -/
theorem vfMidFullRecursiveParentCharge_eq_native_add_remainder
    (R : ℕ) (hR : 7 ≤ R) :
    vfMidOddFractionalPrimeSeatWeight R *
        ((vfMidRecursiveChildCarrier R).card : ℝ) =
      vfMidRecursiveAggregateNativeCharge R +
        vfMidRecursiveAggregateRemainder R := by
  rw [← vfMidRecursiveAggregateParentCharge_eq_fullRecursiveCharge R hR]
  exact vfMidRecursiveAggregateParentCharge_eq_native_add_remainder R

/-- The aggregate deterministic budget obtained by choosing a possibly
different prefix-wheel cutoff T(S) at each child scale. -/
def vfMidRecursiveAggregatePrefixWheelBudget
    (R : ℕ) (T : ℕ → ℕ) : ℝ :=
  ∑ S ∈ Finset.Ico 2 R,
    ((vfMidPrefixWheelEnvelope (T S) S : ℕ) : ℝ) +
      ((vfMidRecursiveChildrenInBlock R S).card : ℝ) *
        |vfMidOddFractionalPrimeSeatWeight R -
          vfMidOddFractionalPrimeSeatWeight S|

/-- **Aggregate prefix-wheel remainder bound.**

For any scale-dependent choice of admissible prefix cutoffs T(S) <= S,

    |sum_{2 <= S < R} Rem_{R,S}|
      <= sum_{2 <= S < R}
           (E_{T(S)}(S) + N_{R,S}|w_R-w_S|).

This is the exact deterministic remainder estimate needed before the
Cauchy--Schwarz budget-contraction step. -/
theorem abs_vfMidRecursiveAggregateRemainder_le_prefixWheelBudget
    (R : ℕ) (T : ℕ → ℕ)
    (hT : ∀ S ∈ Finset.Ico 2 R, T S ≤ S) :
    |vfMidRecursiveAggregateRemainder R| ≤
      vfMidRecursiveAggregatePrefixWheelBudget R T := by
  unfold vfMidRecursiveAggregateRemainder
    vfMidRecursiveAggregatePrefixWheelBudget
  calc
    |∑ S ∈ Finset.Ico 2 R, vfMidRecursiveRemainderInBlock R S|
        ≤ ∑ S ∈ Finset.Ico 2 R,
            |vfMidRecursiveRemainderInBlock R S| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ S ∈ Finset.Ico 2 R,
          ((vfMidPrefixWheelEnvelope (T S) S : ℕ) : ℝ) +
            ((vfMidRecursiveChildrenInBlock R S).card : ℝ) *
              |vfMidOddFractionalPrimeSeatWeight R -
                vfMidOddFractionalPrimeSeatWeight S| := by
          apply Finset.sum_le_sum
          intro S hS
          have hS2 : 2 ≤ S := (Finset.mem_Ico.mp hS).1
          exact
            abs_vfMidRecursiveRemainderInBlock_le_prefixWheel
              R S (T S) hS2 (hT S hS)

/-- Population-clipped aggregate budget.  This is strictly the relevant
multi-scale quantity for Cauchy--Schwarz: a child scale contributes at most its
actual population, and the expanding prefix wheel can only lower that charge. -/
def vfMidRecursiveAggregateClippedPrefixWheelBudget
    (R : ℕ) (T : ℕ → ℕ) : ℝ :=
  ∑ S ∈ Finset.Ico 2 R,
    ((min (vfMidRecursiveChildrenInBlock R S).card
      (vfMidPrefixWheelEnvelope (T S) S) : ℕ) : ℝ) +
      ((vfMidRecursiveChildrenInBlock R S).card : ℝ) *
        |vfMidOddFractionalPrimeSeatWeight R -
          vfMidOddFractionalPrimeSeatWeight S|

/-- **Tight aggregate deterministic remainder bound.**

For arbitrary admissible scale-dependent wheel cutoffs T(S) <= S,

    |sum Rem_{R,S}|
      <= sum [ min(N_{R,S}, E_{T(S)}(S))
               + N_{R,S}|w_R-w_S| ].

This removes the spurious cost of prefix-wheel residue classes on child blocks
which are not actually populated by the recursive descent. -/
theorem abs_vfMidRecursiveAggregateRemainder_le_clippedPrefixWheelBudget
    (R : ℕ) (T : ℕ → ℕ)
    (hT : ∀ S ∈ Finset.Ico 2 R, T S ≤ S) :
    |vfMidRecursiveAggregateRemainder R| ≤
      vfMidRecursiveAggregateClippedPrefixWheelBudget R T := by
  unfold vfMidRecursiveAggregateRemainder
    vfMidRecursiveAggregateClippedPrefixWheelBudget
  calc
    |∑ S ∈ Finset.Ico 2 R, vfMidRecursiveRemainderInBlock R S|
        ≤ ∑ S ∈ Finset.Ico 2 R,
            |vfMidRecursiveRemainderInBlock R S| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ S ∈ Finset.Ico 2 R,
          ((min (vfMidRecursiveChildrenInBlock R S).card
            (vfMidPrefixWheelEnvelope (T S) S) : ℕ) : ℝ) +
            ((vfMidRecursiveChildrenInBlock R S).card : ℝ) *
              |vfMidOddFractionalPrimeSeatWeight R -
                vfMidOddFractionalPrimeSeatWeight S| := by
          apply Finset.sum_le_sum
          intro S hS
          have hS2 : 2 ≤ S := (Finset.mem_Ico.mp hS).1
          exact
            abs_vfMidRecursiveRemainderInBlock_le_minPopulationPrefixWheel
              R S (T S) hS2 (hT S hS)

/-- The total population-clipped prime-correction budget can never exceed
the entire recursive child population, independently of how the wheel cutoff is
chosen at each scale.  Prefix wheels may only improve this bound. -/
theorem vfMidRecursiveAggregateClippedPrimeBudget_le_childCarrier
    (R : ℕ) (T : ℕ → ℕ) :
    (∑ S ∈ Finset.Ico 2 R,
      min (vfMidRecursiveChildrenInBlock R S).card
        (vfMidPrefixWheelEnvelope (T S) S)) ≤
      (vfMidRecursiveChildCarrier R).card := by
  calc
    (∑ S ∈ Finset.Ico 2 R,
      min (vfMidRecursiveChildrenInBlock R S).card
        (vfMidPrefixWheelEnvelope (T S) S))
        ≤ ∑ S ∈ Finset.Ico 2 R,
            (vfMidRecursiveChildrenInBlock R S).card := by
          apply Finset.sum_le_sum
          intro S _hS
          exact min_le_left _ _
    _ ≤ (vfMidRecursiveChildCarrier R).card :=
      vfMidRecursiveChildrenInBlock_sum_card_le_carrier R

/-- Real-valued version of the preceding population budget. -/
theorem vfMidRecursiveAggregateClippedPrimeBudget_cast_le_childCarrier
    (R : ℕ) (T : ℕ → ℕ) :
    (∑ S ∈ Finset.Ico 2 R,
      (((min (vfMidRecursiveChildrenInBlock R S).card
        (vfMidPrefixWheelEnvelope (T S) S) : ℕ) : ℝ))) ≤
      ((vfMidRecursiveChildCarrier R).card : ℝ) := by
  have h :=
    vfMidRecursiveAggregateClippedPrimeBudget_le_childCarrier R T
  exact_mod_cast h

/-- Consequently the tight aggregate remainder budget is at most one total
child-population unit plus the explicit VF weight-transfer budget. -/
theorem vfMidRecursiveAggregateClippedPrefixWheelBudget_le_population_add_weight
    (R : ℕ) (T : ℕ → ℕ) :
    vfMidRecursiveAggregateClippedPrefixWheelBudget R T ≤
      ((vfMidRecursiveChildCarrier R).card : ℝ) +
        ∑ S ∈ Finset.Ico 2 R,
          ((vfMidRecursiveChildrenInBlock R S).card : ℝ) *
            |vfMidOddFractionalPrimeSeatWeight R -
              vfMidOddFractionalPrimeSeatWeight S| := by
  unfold vfMidRecursiveAggregateClippedPrefixWheelBudget
  rw [Finset.sum_add_distrib]
  have hprime :=
    vfMidRecursiveAggregateClippedPrimeBudget_cast_le_childCarrier R T
  linarith

/-- Aggregate fallback using only the universal P_S <= S ceiling. -/
theorem abs_vfMidRecursiveAggregateRemainder_le_halfWidthBudget
    (R : ℕ) :
    |vfMidRecursiveAggregateRemainder R| ≤
      ∑ S ∈ Finset.Ico 2 R,
        (S : ℝ) +
          ((vfMidRecursiveChildrenInBlock R S).card : ℝ) *
            |vfMidOddFractionalPrimeSeatWeight R -
              vfMidOddFractionalPrimeSeatWeight S| := by
  unfold vfMidRecursiveAggregateRemainder
  calc
    |∑ S ∈ Finset.Ico 2 R, vfMidRecursiveRemainderInBlock R S|
        ≤ ∑ S ∈ Finset.Ico 2 R,
            |vfMidRecursiveRemainderInBlock R S| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ S ∈ Finset.Ico 2 R,
          (S : ℝ) +
            ((vfMidRecursiveChildrenInBlock R S).card : ℝ) *
              |vfMidOddFractionalPrimeSeatWeight R -
                vfMidOddFractionalPrimeSeatWeight S| := by
          apply Finset.sum_le_sum
          intro S hS
          exact abs_vfMidRecursiveRemainderInBlock_le_S
            R S (Finset.mem_Ico.mp hS).1

/-- **Explicit linear recursive-transfer remainder bound.**

Choosing the fixed admissible 2-wheel cutoff inside the already proved clipped
multi-resolution estimate and then using population conservation gives

    |Rem_R| <= (1 + 3/log 4) R.

The prefix-wheel family can only improve the prime-correction part of this
universal bound. -/
theorem abs_vfMidRecursiveAggregateRemainder_le_linear
    (R : ℕ) (hR : 7 ≤ R) :
    |vfMidRecursiveAggregateRemainder R| ≤
      (1 + 3 / Real.log 4) * (R : ℝ) := by
  let T : ℕ → ℕ := fun _ => 2
  have hT : ∀ S ∈ Finset.Ico 2 R, T S ≤ S := by
    intro S hS
    dsimp [T]
    exact (Finset.mem_Ico.mp hS).1
  have hrem :=
    abs_vfMidRecursiveAggregateRemainder_le_clippedPrefixWheelBudget
      R T hT
  have hbudget :=
    vfMidRecursiveAggregateClippedPrefixWheelBudget_le_population_add_weight
      R T
  have hcarrierNat := vfMidRecursiveChildCarrier_card_le_R R hR
  have hcarrier :
      ((vfMidRecursiveChildCarrier R).card : ℝ) ≤ (R : ℝ) := by
    exact_mod_cast hcarrierNat
  have hweight :=
    vfMidRecursiveAggregateWeightTransferBudget_le R hR
  calc
    |vfMidRecursiveAggregateRemainder R|
        ≤ vfMidRecursiveAggregateClippedPrefixWheelBudget R T := hrem
    _ ≤ ((vfMidRecursiveChildCarrier R).card : ℝ) +
          ∑ S ∈ Finset.Ico 2 R,
            ((vfMidRecursiveChildrenInBlock R S).card : ℝ) *
              |vfMidOddFractionalPrimeSeatWeight R -
                vfMidOddFractionalPrimeSeatWeight S| := hbudget
    _ ≤ (R : ℝ) + (3 / Real.log 4) * (R : ℝ) := by
          exact add_le_add hcarrier hweight
    _ = (1 + 3 / Real.log 4) * (R : ℝ) := by ring

/-- A simpler integer-constant version: the recursive transfer remainder is at
most 4R.  This avoids carrying logarithmic constants into downstream Gram
budgets. -/
theorem abs_vfMidRecursiveAggregateRemainder_le_four_mul
    (R : ℕ) (hR : 7 ≤ R) :
    |vfMidRecursiveAggregateRemainder R| ≤ 4 * (R : ℝ) := by
  have h :=
    abs_vfMidRecursiveAggregateRemainder_le_linear R hR
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
  have hdiv : 3 / Real.log 4 ≤ (3 : ℝ) := by
    rw [div_le_iff₀ hlogPos]
    nlinarith
  have hC : 1 + 3 / Real.log 4 ≤ (4 : ℝ) := by
    linarith
  calc
    |vfMidRecursiveAggregateRemainder R|
        ≤ (1 + 3 / Real.log 4) * (R : ℝ) := h
    _ ≤ 4 * (R : ℝ) := by
          exact mul_le_mul_of_nonneg_right hC (by positivity)


end RHLean.Analysis
