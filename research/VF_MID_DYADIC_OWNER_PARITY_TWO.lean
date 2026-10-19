import Mathlib
import «research.VF_MID_DYADIC_OWNER_EXACT»

/-!
# Two-slot parity bound for the genuine late least-prime-owner fibre

The existing dyadic exact-owner development puts each late owner's rough
children in four consecutive cofactor slots, and proves that on a strict
subdoubling run these children are actual primes.  All those primes exceed
three, so parity leaves at most two slots.  This file formalizes the sharper
owner count and its exact unsigned block/run consequences.

These statements count real composite occurrences with unit cardinality
weights; they DO NOT establish the original signed, VF-weighted historical
source payment or the canonical RH-scale bound.
-/

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- An arbitrary finite population of odd integers occupying four consecutive
integer slots has at most two members.  No probabilistic hypothesis is used. -/
private theorem finset_odd_four_consecutive_card_le_two
    (t : ℕ) (s : Finset ℕ)
    (hslots : s ⊆ Finset.Ioc t (t + 4))
    (hodd : ∀ m ∈ s, Odd m) :
    s.card ≤ 2 := by
  classical
  by_cases ht : t % 2 = 0
  · have hpair : s ⊆ ({t + 1, t + 3} : Finset ℕ) := by
      intro m hm
      have hmSlots : t < m ∧ m ≤ t + 4 :=
        Finset.mem_Ioc.mp (hslots hm)
      have hmOdd : m % 2 = 1 :=
        (Nat.odd_iff).mp (hodd m hm)
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    have hne : t + 1 ≠ t + 3 := by omega
    simpa [hne] using! (Finset.card_le_card hpair)
  · have htOne : t % 2 = 1 := by omega
    have hpair : s ⊆ ({t + 2, t + 4} : Finset ℕ) := by
      intro m hm
      have hmSlots : t < m ∧ m ≤ t + 4 :=
        Finset.mem_Ioc.mp (hslots hm)
      have hmOdd : m % 2 = 1 :=
        (Nat.odd_iff).mp (hodd m hm)
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    have hne : t + 2 ≠ t + 4 := by omega
    simpa [hne] using! (Finset.card_le_card hpair)

/-- The four-slot inclusion from the existing four-site count, now exported
in the precise child-carrier form needed to intersect with odd prime children.
The square-band endpoints stay strictly open. -/
theorem vfMidSquareBandLateOwner_roughChildren_subset_four_slots
    {A R p : ℕ} (hRlt : R < 2 * A)
    (hp : p ∈ vfMidSquareBandLateOwnerPrimes A R) :
    vfMidSquareBandOwnerRoughChildren R p ⊆
      Finset.Ioc (R ^ 2 / p) (R ^ 2 / p + 4) := by
  have hpData := mem_vfMidSquareBandLateOwnerPrimes.mp hp
  have hpOwner : p ∈ vfMidSquareBandOwnerPrimes R := hpData.1
  have hpGtA : A < p := hpData.2
  have hpPrime : p.Prime :=
    (mem_vfMidSquareBandOwnerPrimes.mp hpOwner).1
  have hpPos : 0 < p := hpPrime.pos
  have hRlt2p : R < 2 * p := by omega
  intro m hm
  rcases Finset.mem_filter.mp hm with ⟨_hmIcc, hdata⟩
  have hlo : R ^ 2 < p * m := hdata.1
  have hhi : p * m < (R + 1) ^ 2 := hdata.2.1
  have hmLower : R ^ 2 / p < m := by
    apply (Nat.div_lt_iff_lt_mul hpPos).2
    simpa [Nat.mul_comm] using! hlo
  have hfloor : R ^ 2 < (R ^ 2 / p + 1) * p := by
    apply (Nat.div_lt_iff_lt_mul hpPos).1
    omega
  have hgap : 2 * R + 1 ≤ 4 * p := by omega
  have hexp : (R + 1) ^ 2 = R ^ 2 + 2 * R + 1 := by ring
  have hmUpper : m ≤ R ^ 2 / p + 4 := by
    by_contra hnot
    have hmGe : R ^ 2 / p + 5 ≤ m := by omega
    have hmulGe :
        (R ^ 2 / p + 5) * p ≤ m * p :=
      Nat.mul_le_mul_right p hmGe
    have hq5 :
        (R ^ 2 / p + 5) * p =
          (R ^ 2 / p + 1) * p + 4 * p := by ring
    have hblockLt : (R + 1) ^ 2 < (R ^ 2 / p + 5) * p := by
      rw [hexp, hq5]
      omega
    have hprodHi : m * p < (R + 1) ^ 2 := by
      simpa [Nat.mul_comm] using! hhi
    omega
  exact Finset.mem_Ioc.mpr ⟨hmLower, hmUpper⟩

/-- Sharp two-slot owner capacity on a strict subdoubling run.  Every
admitted late rough child is an odd prime, so four consecutive slots
contain at most two admissible physical owner occurrences. -/
theorem vfMidSquareBandLateOwner_card_le_two_of_subdoubling
    {A R p : ℕ} (hA : 3 ≤ A) (hAR : A ≤ R)
    (hRlt : R < 2 * A)
    (hp : p ∈ vfMidSquareBandLateOwnerPrimes A R) :
    (vfMidSquareBandCompositeOwner R p).card ≤ 2 := by
  have hpOwner : p ∈ vfMidSquareBandOwnerPrimes R :=
    (mem_vfMidSquareBandLateOwnerPrimes.mp hp).1
  have hpGtA : A < p :=
    (mem_vfMidSquareBandLateOwnerPrimes.mp hp).2
  have hR3 : 3 ≤ R := hA.trans hAR
  have hroughEq :
      vfMidSquareBandCompositeOwnerChildren R p =
        vfMidSquareBandOwnerRoughChildren R p :=
    vfMidSquareBandCompositeOwnerChildren_eq_rough hR3 hpOwner
  have hodd :
      ∀ m ∈ vfMidSquareBandOwnerRoughChildren R p, Odd m := by
    intro m hm
    have hmPrime : m.Prime :=
      vfMidSquareBandLateOwnerRoughChild_prime_of_subdoubling
        hA hRlt hp hm
    have hmIcc := (Finset.mem_filter.mp hm).1
    have hpLeM : p ≤ m := (Finset.mem_Icc.mp hmIcc).1
    exact hmPrime.odd_of_ne_two (by omega)
  have htwo :=
    finset_odd_four_consecutive_card_le_two (R ^ 2 / p)
      (vfMidSquareBandOwnerRoughChildren R p)
      (vfMidSquareBandLateOwner_roughChildren_subset_four_slots
        hRlt hp) hodd
  calc
    (vfMidSquareBandCompositeOwner R p).card =
        (vfMidSquareBandCompositeOwnerChildren R p).card := by
          symm
          exact vfMidSquareBandCompositeOwnerChildren_card R p
    _ = (vfMidSquareBandOwnerRoughChildren R p).card := by
          exact congrArg Finset.card hroughEq
    _ ≤ 2 := htwo

/-- The exact disjoint least-prime-owner partition and two-slot fibre bound
yield only two late composites per integer of starting-root displacement. -/
theorem vfMidSquareBandPrefixComposite_start_card_le_two_mul_gap
    {A R : ℕ} (hA : 3 ≤ A) (hAR : A ≤ R)
    (hRlt : R < 2 * A) :
    (vfMidSquareBandPrefixCompositeSurvivors A R).card ≤
      2 * (R - A) := by
  have howners :=
    vfMidSquareBandPrefixComposite_card_eq_sum_lateOwnerCards
      A R (by omega : 2 ≤ R)
  have hownerSub :
      vfMidSquareBandLateOwnerPrimes A R ⊆ Finset.Ioc A R := by
    intro p hp
    have hpData := mem_vfMidSquareBandLateOwnerPrimes.mp hp
    have hpRoot : p ≤ R :=
      (mem_vfMidSquareBandOwnerPrimes.mp hpData.1).2
    exact Finset.mem_Ioc.mpr ⟨hpData.2, hpRoot⟩
  have hownerCard :
      (vfMidSquareBandLateOwnerPrimes A R).card ≤ R - A := by
    have hc := Finset.card_le_card hownerSub
    simpa using! hc
  rw [howners]
  calc
    (∑ p ∈ vfMidSquareBandLateOwnerPrimes A R,
        (vfMidSquareBandCompositeOwner R p).card) ≤
        ∑ _p ∈ vfMidSquareBandLateOwnerPrimes A R, 2 := by
          apply Finset.sum_le_sum
          intro p hp
          exact vfMidSquareBandLateOwner_card_le_two_of_subdoubling
            hA hAR hRlt hp
    _ = 2 * (vfMidSquareBandLateOwnerPrimes A R).card := by
          simp [Nat.mul_comm]
    _ ≤ 2 * (R - A) := Nat.mul_le_mul_left 2 hownerCard

/-- Exact arithmetic for the triangular budget: the sum of twice the
starting-root displacement over [A,B) is d(d-1), d=B-A. -/
private theorem vfMidTwoMulGap_sum_Ico
    (A B : ℕ) (hAB : A ≤ B) :
    (∑ r ∈ Finset.Ico A B, (2 : ℝ) * ((r - A : ℕ) : ℝ)) =
      ((B - A : ℕ) : ℝ) * (((B - A : ℕ) : ℝ) - 1) := by
  let F : ℕ → ℝ := fun r =>
    ((r - A : ℕ) : ℝ) * (((r - A : ℕ) : ℝ) - 1)
  have hstep (r : ℕ) (hr : A ≤ r) :
      (2 : ℝ) * ((r - A : ℕ) : ℝ) = F (r + 1) - F r := by
    have hsub : r + 1 - A = (r - A) + 1 := by omega
    dsimp [F]
    rw [hsub]
    push_cast
    ring
  calc
    (∑ r ∈ Finset.Ico A B, (2 : ℝ) * ((r - A : ℕ) : ℝ)) =
        ∑ r ∈ Finset.Ico A B, (F (r + 1) - F r) := by
          apply Finset.sum_congr rfl
          intro r hr
          exact hstep r (Finset.mem_Ico.mp hr).1
    _ = F B - F A := Finset.sum_Ico_sub F hAB
    _ = ((B - A : ℕ) : ℝ) *
          (((B - A : ℕ) : ℝ) - 1) := by simp [F]

/-- Exact triangular upper budget for physical unit-weight late-composite
occurrences over a subdoubling run.  At d=0 the displayed real polynomial
is zero; for positive natural d it is exactly d(d-1). -/
theorem vfMidDyadicLateRemoval_start_le_two_triangular
    {A B : ℕ} (hA : 3 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A) :
    vfMidDyadicLateRemoval A A B ≤
      ((B - A : ℕ) : ℝ) * (((B - A : ℕ) : ℝ) - 1) := by
  rw [vfMidDyadicLateRemoval_eq_ownerCensus A A B
    (by omega) le_rfl hAB]
  unfold vfMidDyadicOwnerLateRemoval
  calc
    (∑ r ∈ Finset.Ico A B,
        ∑ p ∈ vfMidSquareBandLateOwnerPrimes A r,
          ((vfMidSquareBandCompositeOwner r p).card : ℝ)) =
      ∑ r ∈ Finset.Ico A B,
        ((vfMidSquareBandPrefixCompositeSurvivors A r).card : ℝ) := by
          apply Finset.sum_congr rfl
          intro r hr
          have howners :=
            vfMidSquareBandPrefixComposite_card_eq_sum_lateOwnerCards
              A r (by
                have hAr : A ≤ r := (Finset.mem_Ico.mp hr).1
                omega : 2 ≤ r)
          exact_mod_cast howners.symm
    _ ≤ ∑ r ∈ Finset.Ico A B,
          (2 : ℝ) * ((r - A : ℕ) : ℝ) := by
          apply Finset.sum_le_sum
          intro r hr
          have hAr : A ≤ r := (Finset.mem_Ico.mp hr).1
          have hrB : r < B := (Finset.mem_Ico.mp hr).2
          have hr2A : r < 2 * A := hrB.trans_le hBA
          have hcard :=
            vfMidSquareBandPrefixComposite_start_card_le_two_mul_gap
              hA hAr hr2A
          exact_mod_cast hcard
    _ = ((B - A : ℕ) : ℝ) *
          (((B - A : ℕ) : ℝ) - 1) :=
            vfMidTwoMulGap_sum_Ico A B hAB

/-- Sharp deterministic lower prime-supply capacity derived from the
unsigned triangular late-composite budget, NOT a signed source payment. -/
theorem vfMidDyadicPrimeSupply_ge_startPrefix_sub_two_triangular
    {A B : ℕ} (hA : 3 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A) :
    vfMidDyadicPrefixSupply A A B -
        ((B - A : ℕ) : ℝ) * (((B - A : ℕ) : ℝ) - 1) ≤
      vfMidDyadicPrimeSupply A B := by
  have hlate :=
    vfMidDyadicLateRemoval_start_le_two_triangular
      hA hAB hBA
  unfold vfMidDyadicLateRemoval at hlate
  linarith

/-! ## Kernel axiom audit for the newly formalized arithmetic inequalities -/

#print axioms vfMidSquareBandLateOwner_card_le_two_of_subdoubling
#print axioms vfMidSquareBandPrefixComposite_start_card_le_two_mul_gap
#print axioms vfMidDyadicLateRemoval_start_le_two_triangular
#print axioms vfMidDyadicPrimeSupply_ge_startPrefix_sub_two_triangular

end RHLean.Analysis
