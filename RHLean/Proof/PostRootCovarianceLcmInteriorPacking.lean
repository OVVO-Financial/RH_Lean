import Mathlib
import RHLean.Proof.PostRootCovarianceLcmBoundary

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Analysis
open RHLean.Arithmetic
open Finset Nat

attribute [local instance] Classical.propDecidable

/-- The part of one removed post-root prime family whose pair lcm still fits
below the physical endpoint. -/
def postRootPrimePhysicalInteriorLcmCarrier
    (W p : ℕ) : Finset (ℕ × ℕ) :=
  (postRootPrimePhysicalPairCarrier W p).filter fun mn =>
    Nat.lcm mn.1 mn.2 ≤ W

@[simp] theorem mem_postRootPrimePhysicalInteriorLcmCarrier
    {W p : ℕ} {mn : ℕ × ℕ} :
    mn ∈ postRootPrimePhysicalInteriorLcmCarrier W p ↔
      mn ∈ postRootPrimePhysicalPairCarrier W p ∧
        Nat.lcm mn.1 mn.2 ≤ W := by
  simp [postRootPrimePhysicalInteriorLcmCarrier]

/-- **Exact quotient scaling of a post-root lcm interior.**  Multiplication by
`p` is a weight-preserving bijection from the complete positive lcm interior at
scale `W / p` onto the physical lcm interior of the removed `p`-family.

The two Möbius sign reversals cancel, while `lcm (p*a) (p*b) =
p*lcm(a,b)` transports the multiplicative cutoff exactly. -/
theorem sum_postRootPrimePhysicalInteriorLcmCarrier_eq_lower
    {W p : ℕ} (hp : p ∈ postRootPrimeFamilySet W) :
    (∑ mn ∈ postRootPrimePhysicalInteriorLcmCarrier W p,
      realMoebiusStep mn.1 * realMoebiusStep mn.2) =
      ∑ ab ∈ moebiusLcmInteriorPositiveCarrier (W / p),
        realMoebiusStep ab.1 * realMoebiusStep ab.2 := by
  rcases mem_postRootPrimeFamilySet.mp hp with ⟨hpRoot, _hpW, hpPrime⟩
  have hWpp : W < p * p := (Nat.sqrt_lt).1 hpRoot
  have hquotlt : W / p < p :=
    (Nat.div_lt_iff_lt_mul hpPrime.pos).2 hWpp
  symm
  refine Finset.sum_bij
    (fun ab _hab => (p * ab.1, p * ab.2)) ?_ ?_ ?_ ?_
  · intro ab hab
    rcases mem_moebiusLcmInteriorPositiveCarrier.mp hab with
      ⟨ha, hb, hablt, hlcm⟩
    rcases Finset.mem_Icc.mp ha with ⟨ha1, haQ⟩
    rcases Finset.mem_Icc.mp hb with ⟨hb1, hbQ⟩
    have haW : p * ab.1 ≤ W := by
      have h := (Nat.le_div_iff_mul_le hpPrime.pos).1 haQ
      simpa [Nat.mul_comm] using h
    have hbW : p * ab.2 ≤ W := by
      have h := (Nat.le_div_iff_mul_le hpPrime.pos).1 hbQ
      simpa [Nat.mul_comm] using h
    have habp : p * ab.1 < p * ab.2 :=
      (Nat.mul_lt_mul_left hpPrime.pos).2 hablt
    have hlcmW : Nat.lcm (p * ab.1) (p * ab.2) ≤ W := by
      have hmul : p * Nat.lcm ab.1 ab.2 ≤ W := by
        have h := (Nat.le_div_iff_mul_le hpPrime.pos).1 hlcm
        simpa [Nat.mul_comm] using h
      simpa [lcm_mul_left] using hmul
    apply mem_postRootPrimePhysicalInteriorLcmCarrier.mpr
    constructor
    · apply mem_postRootPrimePhysicalPairCarrier.mpr
      exact ⟨Nat.mul_pos hpPrime.pos (by omega), haW,
        Nat.mul_pos hpPrime.pos (by omega), hbW, habp,
        ⟨ab.1, by simp [Nat.mul_comm]⟩,
        ⟨ab.2, by simp [Nat.mul_comm]⟩⟩
    · exact hlcmW
  · intro a ha b hb hab
    apply Prod.ext
    · exact Nat.eq_of_mul_eq_mul_left hpPrime.pos (congrArg Prod.fst hab)
    · exact Nat.eq_of_mul_eq_mul_left hpPrime.pos (congrArg Prod.snd hab)
  · intro mn hmn
    rcases mem_postRootPrimePhysicalInteriorLcmCarrier.mp hmn with
      ⟨hfamily, hlcmW⟩
    rcases mem_postRootPrimePhysicalPairCarrier.mp hfamily with
      ⟨hm1, hmW, hn1, hnW, hmnlt, hpm, hpn⟩
    let a := mn.1 / p
    let b := mn.2 / p
    have hma : p * a = mn.1 := Nat.mul_div_cancel' hpm
    have hnb : p * b = mn.2 := Nat.mul_div_cancel' hpn
    have ha1 : 1 ≤ a := by
      by_contra h
      have ha0 : a = 0 := by omega
      rw [ha0, mul_zero] at hma
      omega
    have hb1 : 1 ≤ b := by
      by_contra h
      have hb0 : b = 0 := by omega
      rw [hb0, mul_zero] at hnb
      omega
    have haQ : a ≤ W / p := by
      apply (Nat.le_div_iff_mul_le hpPrime.pos).2
      simpa [Nat.mul_comm, hma] using hmW
    have hbQ : b ≤ W / p := by
      apply (Nat.le_div_iff_mul_le hpPrime.pos).2
      simpa [Nat.mul_comm, hnb] using hnW
    have hablt : a < b := by
      apply (Nat.mul_lt_mul_left hpPrime.pos).1
      simpa [hma, hnb] using hmnlt
    have hlcmQ : Nat.lcm a b ≤ W / p := by
      apply (Nat.le_div_iff_mul_le hpPrime.pos).2
      have hlcmScaled : Nat.lcm (p * a) (p * b) ≤ W := by
        simpa [hma, hnb] using hlcmW
      simpa [lcm_mul_left, Nat.mul_comm] using hlcmScaled
    refine ⟨(a, b), ?_, ?_⟩
    · exact mem_moebiusLcmInteriorPositiveCarrier.mpr ⟨
        Finset.mem_Icc.mpr ⟨ha1, haQ⟩,
        Finset.mem_Icc.mpr ⟨hb1, hbQ⟩,
        hablt, hlcmQ⟩
    · ext <;> simp [a, b, hma, hnb]
  · intro ab hab
    rcases mem_moebiusLcmInteriorPositiveCarrier.mp hab with
      ⟨ha, hb, _hablt, _hlcm⟩
    have haP : ab.1 < p :=
      (Finset.mem_Icc.mp ha).2.trans_lt hquotlt
    have hbP : ab.2 < p :=
      (Finset.mem_Icc.mp hb).2.trans_lt hquotlt
    exact (realMoebiusStep_prime_mul_pair hpPrime haP hbP).symm

/-- Every removed post-root family has nonpositive complete-lcm interior mass. -/
theorem sum_postRootPrimePhysicalInteriorLcmCarrier_nonpos
    {W p : ℕ} (hp : p ∈ postRootPrimeFamilySet W) :
    (∑ mn ∈ postRootPrimePhysicalInteriorLcmCarrier W p,
      realMoebiusStep mn.1 * realMoebiusStep mn.2) ≤ 0 := by
  rw [sum_postRootPrimePhysicalInteriorLcmCarrier_eq_lower hp]
  exact sum_realMoebiusStep_lcmInteriorPositive_nonpos (W / p)

/-- Its negative size is at most its quotient seat count `W / p`. -/
theorem neg_quotient_le_sum_postRootPrimePhysicalInteriorLcmCarrier
    {W p : ℕ} (hp : p ∈ postRootPrimeFamilySet W) :
    -((W / p : ℕ) : ℝ) ≤
      ∑ mn ∈ postRootPrimePhysicalInteriorLcmCarrier W p,
        realMoebiusStep mn.1 * realMoebiusStep mn.2 := by
  rw [sum_postRootPrimePhysicalInteriorLcmCarrier_eq_lower hp]
  exact neg_endpoint_le_sum_realMoebiusStep_lcmInteriorPositive (W / p)

/-! ## Aggregate product packing of all removed interiors -/

/-- The complete-lcm portion of the literal union removed by all post-root
prime families. -/
def postRootPrimePhysicalInteriorLcmUnion (W : ℕ) : Finset (ℕ × ℕ) :=
  (postRootPrimePhysicalPairUnion W).filter fun mn =>
    Nat.lcm mn.1 mn.2 ≤ W

@[simp] theorem mem_postRootPrimePhysicalInteriorLcmUnion
    {W : ℕ} {mn : ℕ × ℕ} :
    mn ∈ postRootPrimePhysicalInteriorLcmUnion W ↔
      mn ∈ postRootPrimePhysicalPairUnion W ∧
        Nat.lcm mn.1 mn.2 ≤ W := by
  simp [postRootPrimePhysicalInteriorLcmUnion]

/-- Filtering by the lcm cutoff commutes with the disjoint post-root family
union. -/
theorem postRootPrimePhysicalInteriorLcmUnion_eq_biUnion (W : ℕ) :
    postRootPrimePhysicalInteriorLcmUnion W =
      (postRootPrimeFamilySet W).biUnion
        (postRootPrimePhysicalInteriorLcmCarrier W) := by
  ext mn
  simp [postRootPrimePhysicalInteriorLcmUnion,
    postRootPrimePhysicalInteriorLcmCarrier]

/-- The filtered family interiors remain pairwise disjoint. -/
theorem postRootPrimePhysicalInteriorLcmCarrier_pairwiseDisjoint (W : ℕ) :
    Set.PairwiseDisjoint (↑(postRootPrimeFamilySet W))
      (postRootPrimePhysicalInteriorLcmCarrier W) := by
  intro p hp q hq hpq
  rw [Finset.disjoint_left]
  intro mn hmnp hmnq
  have hfullp : mn ∈ postRootPrimePhysicalPairCarrier W p :=
    (Finset.mem_filter.mp hmnp).1
  have hfullq : mn ∈ postRootPrimePhysicalPairCarrier W q :=
    (Finset.mem_filter.mp hmnq).1
  exact (Finset.disjoint_left.mp
    (postRootPrimePhysicalPairCarrier_disjoint hp hq hpq)) hfullp hfullq

/-- The complete positive lcm interior is the disjoint union of the #593
remainder interior and the filtered post-root family interiors. -/
theorem moebiusLcmInteriorPositiveCarrier_eq_remainder_union_removed
    (W : ℕ) :
    moebiusLcmInteriorPositiveCarrier W =
      postRootCovarianceRemainderInteriorLcmCarrier W ∪
        postRootPrimePhysicalInteriorLcmUnion W := by
  ext mn
  constructor
  · intro hmn
    have hbase : mn ∈ mertensPositivePhysicalPairCarrier W := by
      rw [moebiusLcmInteriorPositiveCarrier_eq_filter] at hmn
      exact (Finset.mem_filter.mp hmn).1
    have hlcm : Nat.lcm mn.1 mn.2 ≤ W := by
      rw [moebiusLcmInteriorPositiveCarrier_eq_filter] at hmn
      exact (Finset.mem_filter.mp hmn).2
    by_cases hremoved : mn ∈ postRootPrimePhysicalPairUnion W
    · exact Finset.mem_union_right _
        (mem_postRootPrimePhysicalInteriorLcmUnion.mpr ⟨hremoved, hlcm⟩)
    · apply Finset.mem_union_left
      exact mem_postRootCovarianceRemainderInteriorLcmCarrier.mpr ⟨
        mem_postRootCovarianceRemainderPhysicalPairCarrier.mpr
          ⟨hbase, hremoved⟩,
        hlcm⟩
  · intro hmn
    rcases Finset.mem_union.mp hmn with hrem | hremoved
    · rcases mem_postRootCovarianceRemainderInteriorLcmCarrier.mp hrem with
        ⟨hphys, hlcm⟩
      have hbase :=
        (mem_postRootCovarianceRemainderPhysicalPairCarrier.mp hphys).1
      rw [moebiusLcmInteriorPositiveCarrier_eq_filter]
      exact Finset.mem_filter.mpr ⟨hbase, hlcm⟩
    · rcases mem_postRootPrimePhysicalInteriorLcmUnion.mp hremoved with
        ⟨hunion, hlcm⟩
      have hbase := postRootPrimePhysicalPairUnion_subset W hunion
      rw [moebiusLcmInteriorPositiveCarrier_eq_filter]
      exact Finset.mem_filter.mpr ⟨hbase, hlcm⟩

/-- The two pieces in the complete-interior decomposition are disjoint. -/
theorem postRootCovarianceRemainderInteriorLcmCarrier_disjoint_removed
    (W : ℕ) :
    Disjoint (postRootCovarianceRemainderInteriorLcmCarrier W)
      (postRootPrimePhysicalInteriorLcmUnion W) := by
  rw [Finset.disjoint_left]
  intro mn hrem hremoved
  have hnot :=
    (mem_postRootCovarianceRemainderPhysicalPairCarrier.mp
      (mem_postRootCovarianceRemainderInteriorLcmCarrier.mp hrem).1).2
  exact hnot (mem_postRootPrimePhysicalInteriorLcmUnion.mp hremoved).1

/-- Exact signed partition of the full positive complete-lcm interior into the
remainder and all removed post-root interiors. -/
theorem sum_moebiusLcmInteriorPositiveCarrier_eq_remainder_add_removed
    (W : ℕ) :
    (∑ mn ∈ moebiusLcmInteriorPositiveCarrier W,
      realMoebiusStep mn.1 * realMoebiusStep mn.2) =
      (∑ mn ∈ postRootCovarianceRemainderInteriorLcmCarrier W,
        realMoebiusStep mn.1 * realMoebiusStep mn.2) +
      ∑ mn ∈ postRootPrimePhysicalInteriorLcmUnion W,
        realMoebiusStep mn.1 * realMoebiusStep mn.2 := by
  rw [moebiusLcmInteriorPositiveCarrier_eq_remainder_union_removed,
    Finset.sum_union
      (postRootCovarianceRemainderInteriorLcmCarrier_disjoint_removed W)]

/-- The removed complete-lcm mass is exactly the sum of the lower-scale family
interiors. -/
theorem sum_postRootPrimePhysicalInteriorLcmUnion_eq_familySum
    (W : ℕ) :
    (∑ mn ∈ postRootPrimePhysicalInteriorLcmUnion W,
      realMoebiusStep mn.1 * realMoebiusStep mn.2) =
      ∑ p ∈ postRootPrimeFamilySet W,
        ∑ mn ∈ postRootPrimePhysicalInteriorLcmCarrier W p,
          realMoebiusStep mn.1 * realMoebiusStep mn.2 := by
  rw [postRootPrimePhysicalInteriorLcmUnion_eq_biUnion,
    Finset.sum_biUnion
      (postRootPrimePhysicalInteriorLcmCarrier_pairwiseDisjoint W)]

/-- **Complete-lcm remainder interior is linearly bounded.**  Every removed
post-root family is a lower-scale complete interior of size `W / p`; their
negative costs pack into at most `W` quotient seats.  The full complete interior
is already nonpositive, so the #593 remainder interior is at most the endpoint.

This closes the entire `lcm(m,n) ≤ W` region without an iid assumption, prime-gap
hypothesis, PNT error term, or absolute-value estimate. -/
theorem sum_postRootCovarianceRemainderInteriorLcmCarrier_le_endpoint
    (W : ℕ) :
    (∑ mn ∈ postRootCovarianceRemainderInteriorLcmCarrier W,
      realMoebiusStep mn.1 * realMoebiusStep mn.2) ≤ (W : ℝ) := by
  have hfull := sum_realMoebiusStep_lcmInteriorPositive_nonpos W
  have hpart :=
    sum_moebiusLcmInteriorPositiveCarrier_eq_remainder_add_removed W
  have hremovedEq :=
    sum_postRootPrimePhysicalInteriorLcmUnion_eq_familySum W
  have hfamilyLower :
      -(∑ p ∈ postRootPrimeFamilySet W, ((W / p : ℕ) : ℝ)) ≤
        ∑ p ∈ postRootPrimeFamilySet W,
          ∑ mn ∈ postRootPrimePhysicalInteriorLcmCarrier W p,
            realMoebiusStep mn.1 * realMoebiusStep mn.2 := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun p hp =>
      neg_quotient_le_sum_postRootPrimePhysicalInteriorLcmCarrier hp
  have hpackNat := sum_postRootPrimeFamily_quotients_le_endpoint W
  have hpack :
      (∑ p ∈ postRootPrimeFamilySet W, ((W / p : ℕ) : ℝ)) ≤ (W : ℝ) := by
    exact_mod_cast hpackNat
  rw [hremovedEq] at hpart
  linarith

end RHLean.Proof
