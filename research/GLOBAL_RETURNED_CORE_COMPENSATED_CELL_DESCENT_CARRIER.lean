import Mathlib
import «research.GLOBAL_RETURNED_CORE_THRESHOLD_SIGNED_DESCENT»
import «research.GLOBAL_RETURNED_CORE_DIRICHLET_INCIDENCE_CLOSURE»

/-!
# Fresh-prime descent stays inside one compensated first-owner cell

The signed threshold descent is useful globally only if stripping its next
fresh owner does not leave the current compensated `p`-cell.  This file proves
that exact carrier fact.

Take two admitted p-free parents `a,b` in the same lower-p signature cell.  Any
prime coordinate on which they differ is strictly larger than p: below p their
signatures agree, and at p both are p-free.  If such a fresh prime `r` is
stripped from either endpoint, the stripped parent

* is still positive and on nonzero Mobius support,
* has the same lower-p signature,
* remains p-free, and
* remains admitted because it divides the original endpoint.

Thus arbitrary fresh-prime signed descent telescopes *inside the same actual
compensated cell*.  No norm or magnitude estimate is used.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Ordered/unordered admitted pair carrier of one compensated cell. -/
def lowOwnerFirstOwnerAdmittedPairCarrier
    (R p : ℕ) (sig : Finset ℕ) : Finset (ℕ × ℕ) :=
  (lowOwnerFirstOwnerAdmittedBaseFiber R p sig).product
    (lowOwnerFirstOwnerAdmittedBaseFiber R p sig)

/-- Any fresh prime between two admitted sites of the same p-cell lies strictly
above p. -/
theorem lowOwnerFirstOwnerAdmittedPair_freshPrime_gt_owner
    {R p r a b : ℕ} {sig : Finset ℕ}
    (hp : p.Prime)
    (ha : a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig)
    (hb : b ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig)
    (hrFresh : r ∈ squarefreePairFreshPrimeSet a b) :
    p < r := by
  rcases Finset.mem_filter.mp ha with ⟨haBase, _hpaX⟩
  rcases Finset.mem_filter.mp hb with ⟨hbBase, _hpbX⟩
  rcases Finset.mem_filter.mp haBase with ⟨haCar, haData⟩
  rcases Finset.mem_filter.mp hbBase with ⟨hbCar, hbData⟩
  have haPos := (lowOwnerNonzeroMobiusCarrier_squarefree_pos haCar).2
  have hbPos := (lowOwnerNonzeroMobiusCarrier_squarefree_pos hbCar).2
  have hrPrime := (freshPrime_of_nonzeroPhysicalPair haCar hbCar hrFresh).1
  have hxor :=
    (mem_squarefreePairFreshPrimeSet_iff_prime_dvd_xor
      hrPrime haPos hbPos).1 hrFresh
  by_contra hnot
  have hrle : r ≤ p := Nat.le_of_not_gt hnot
  by_cases hrp : r = p
  · subst r
    rcases hxor with h | h
    · exact h.1.elim haData.2
    · exact h.1.elim hbData.2
  · have hrlt : r < p := lt_of_le_of_ne hrle hrp
    have hsigEq : squarefreeLowerPrimeSignature p a =
        squarefreeLowerPrimeSignature p b := by
      rw [haData.1, hbData.1]
    rcases hxor with h | h
    · have hrFaceA : r ∈ squarefreePrimeFace a :=
        (prime_mem_squarefreePrimeFace_iff_dvd_public hrPrime haPos).2 h.1
      have hrLowA : r ∈ squarefreeLowerPrimeSignature p a :=
        Finset.mem_filter.mpr ⟨hrFaceA, hrlt⟩
      have hrLowB : r ∈ squarefreeLowerPrimeSignature p b := by
        rw [← hsigEq]
        exact hrLowA
      have hrFaceB := (Finset.mem_filter.mp hrLowB).1
      have hrDivB :=
        (prime_mem_squarefreePrimeFace_iff_dvd_public hrPrime hbPos).1 hrFaceB
      exact h.2 hrDivB
    · have hrFaceB : r ∈ squarefreePrimeFace b :=
        (prime_mem_squarefreePrimeFace_iff_dvd_public hrPrime hbPos).2 h.1
      have hrLowB : r ∈ squarefreeLowerPrimeSignature p b :=
        Finset.mem_filter.mpr ⟨hrFaceB, hrlt⟩
      have hrLowA : r ∈ squarefreeLowerPrimeSignature p a := by
        rw [hsigEq]
        exact hrLowB
      have hrFaceA := (Finset.mem_filter.mp hrLowA).1
      have hrDivA :=
        (prime_mem_squarefreePrimeFace_iff_dvd_public hrPrime haPos).1 hrFaceA
      exact h.2 hrDivA

/-- Stripping a larger prime from one admitted p-parent keeps it inside the same
admitted p-cell. -/
theorem lowOwnerFirstOwner_primeParent_mem_same_admitted
    {R p r a : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r)
    (ha : a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig) :
    squarefreePrimeFamilyParent r a ∈
      lowOwnerFirstOwnerAdmittedBaseFiber R p sig := by
  rcases Finset.mem_filter.mp ha with ⟨haBase, hpaX⟩
  rcases Finset.mem_filter.mp haBase with ⟨haCar, haData⟩
  rcases Finset.mem_filter.mp haCar with ⟨haIcc, hmuA⟩
  rcases lowOwnerNonzeroMobiusCarrier_squarefree_pos haCar with
    ⟨haSq, haPos⟩
  let u := squarefreePrimeFamilyParent r a
  have huPos : 0 < u := squarefreePrimeFamilyParent_pos_public hr haPos
  have huDvd : u ∣ a := squarefreePrimeFamilyParent_dvd_public r a
  have hua : u ≤ a := Nat.le_of_dvd haPos huDvd
  have huX : u ≤ squareRootEndpoint R :=
    hua.trans (Finset.mem_Icc.mp haIcc).2
  have hmuU : realMoebiusStep u ≠ 0 := by
    unfold squarefreePrimeFamilyParent at u
    by_cases hra : r ∣ a
    · rw [if_pos hra] at u
      have hrnot : ¬ r ∣ a / r :=
        prime_not_dvd_div_of_squarefree hr haSq hra
      have hsign := realMoebiusStep_mul_prime_eq_neg hr hrnot
      have heq : r * (a / r) = a := Nat.mul_div_cancel' hra
      intro hz
      apply hmuA
      rw [← heq, hsign, hz, neg_zero]
    · rw [if_neg hra] at u
      simpa [u] using hmuA
  have huCar : u ∈ lowOwnerNonzeroMobiusCarrier R :=
    Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨by omega, huX⟩, hmuU⟩
  have hsigU : squarefreeLowerPrimeSignature p u = sig := by
    unfold squarefreePrimeFamilyParent at u
    by_cases hra : r ∣ a
    · rw [if_pos hra] at u
      have heq : r * u = a := by
        dsimp [u]
        exact Nat.mul_div_cancel' hra
      have hlower := squarefreeLowerPrimeSignature_mul_larger_prime
        hr hpr huPos
      rw [heq] at hlower
      rw [← hlower, haData.1]
    · rw [if_neg hra] at u
      simpa [u] using haData.1
  have hpne : p ≠ r := by omega
  have hpFreeU : ¬ p ∣ u := by
    intro hpu
    have hiff := prime_dvd_squarefreePrimeFamilyParent_iff_of_ne_public
      hr hp hpne
    exact haData.2 (hiff.mp hpu)
  have huBase : u ∈ lowOwnerFirstOwnerBaseFiber R p sig :=
    Finset.mem_filter.mpr ⟨huCar, ⟨hsigU, hpFreeU⟩⟩
  have hpuX : p * u ≤ squareRootEndpoint R := by
    have hmul : p * u ≤ p * a := Nat.mul_le_mul_left p hua
    exact hmul.trans hpaX
  exact Finset.mem_filter.mpr ⟨huBase, hpuX⟩

/-- **Internal carrier closure.**  Stripping any fresh coordinate of a pair in
one compensated cell returns both endpoints to that same compensated cell. -/
theorem lowOwnerFirstOwnerAdmittedPair_freshPrime_parents_mem_same_cell
    {R p r a b : ℕ} {sig : Finset ℕ}
    (hp : p.Prime)
    (ha : a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig)
    (hb : b ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig)
    (hrFresh : r ∈ squarefreePairFreshPrimeSet a b) :
    let ua := squarefreePrimeFamilyParent r a
    let ub := squarefreePrimeFamilyParent r b
    ua ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig ∧
      ub ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig := by
  have hgt := lowOwnerFirstOwnerAdmittedPair_freshPrime_gt_owner
    hp ha hb hrFresh
  have haCar := (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).1
  have hbCar := (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).1
  have hrPrime := (freshPrime_of_nonzeroPhysicalPair haCar hbCar hrFresh).1
  dsimp only
  exact ⟨lowOwnerFirstOwner_primeParent_mem_same_admitted hp hrPrime hgt ha,
    lowOwnerFirstOwner_primeParent_mem_same_admitted hp hrPrime hgt hb⟩

/-- Pair-carrier form of the preceding closure. -/
theorem lowOwnerFirstOwnerAdmittedPair_freshPrime_parentPair_mem
    {R p r a b : ℕ} {sig : Finset ℕ}
    (hp : p.Prime)
    (hab : (a, b) ∈ lowOwnerFirstOwnerAdmittedPairCarrier R p sig)
    (hrFresh : r ∈ squarefreePairFreshPrimeSet a b) :
    (squarefreePrimeFamilyParent r a,
      squarefreePrimeFamilyParent r b) ∈
        lowOwnerFirstOwnerAdmittedPairCarrier R p sig := by
  rcases Finset.mem_product.mp hab with ⟨ha, hb⟩
  have hparents :=
    lowOwnerFirstOwnerAdmittedPair_freshPrime_parents_mem_same_cell
      hp ha hb hrFresh
  dsimp only at hparents
  exact Finset.mem_product.mpr hparents

end RHLean.Proof
