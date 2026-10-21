import Mathlib
import «research.VF_MID_SAME_TAG_SHARP_PACKET»

/-!
# Fixed-historical-prime dyadic fibre: exact floors and actual prime counts

This is the exact finite arithmetic portion of the 2026-10-14 Analytic
Type II result, with the referee-required small-q correction `q>=4096`.
The strict upper square boundary contributes the indispensable '-1'
inside the quotient numerator.

Do not confuse this exact finite formula with the distinct PAPER_PROOF
PNT and weighted asymptotic claims. Exact source admission and the
global signed first-bad/NNS source payment are not asserted.
-/

noncomputable section
namespace RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- The sharp run starts at the floor(q/4096) square root. -/
def vfMidSameTagDyadicStart (q : ℕ) : ℕ := q / 4096

/-- Strict lower and upper integer quotient endpoints for pq. -/
def vfMidSameTagDyadicLower (q : ℕ) : ℕ :=
  vfMidSameTagDyadicStart q ^ 2 / q

def vfMidSameTagDyadicUpper (q : ℕ) : ℕ :=
  ((2 * vfMidSameTagDyadicStart q) ^ 2 - 1) / q

/-- Actual odd prime owners, not a wheel approximation. -/
def vfMidSameTagDyadicFibre (q : ℕ) : Finset ℕ :=
  (Finset.Ioc (vfMidSameTagDyadicLower q)
    (vfMidSameTagDyadicUpper q)).filter
      (fun p => p.Prime ∧ 3 ≤ p)

/-- A repaired, nondegenerate finite domain for the quotient formula. -/
private theorem vfMidSameTagDyadic_domain
    {q : ℕ} (hq : 4096 ≤ q) :
    0 < q ∧ 1 ≤ vfMidSameTagDyadicStart q ∧
      vfMidSameTagDyadicLower q ≤ vfMidSameTagDyadicUpper q := by
  have hq0 : 0 < q := by omega
  have hA : 1 ≤ vfMidSameTagDyadicStart q := by
    unfold vfMidSameTagDyadicStart
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 4096)).2
    omega
  have hnum :
      (vfMidSameTagDyadicStart q) ^ 2 ≤
        (2 * vfMidSameTagDyadicStart q) ^ 2 - 1 := by
    have ha := hA
    have haSq : 1 ≤ (vfMidSameTagDyadicStart q) ^ 2 := by nlinarith
    have hsquares :
        (vfMidSameTagDyadicStart q) ^ 2 + 1 ≤
          (2 * vfMidSameTagDyadicStart q) ^ 2 := by nlinarith
    omega
  exact ⟨hq0, hA, Nat.div_le_div_right hnum⟩

/-- Exact strict-wall equivalence at arbitrary q>=4096:
no square endpoint is included and no prime-site multiplicity is changed. -/
theorem mem_vfMidSameTagDyadicFibre_iff
    {q p : ℕ} (hq : 4096 ≤ q) :
    p ∈ vfMidSameTagDyadicFibre q ↔
      p.Prime ∧ 3 ≤ p ∧
      (vfMidSameTagDyadicStart q) ^ 2 < p * q ∧
        p * q < (2 * vfMidSameTagDyadicStart q) ^ 2 := by
  have hq0 : 0 < q := (vfMidSameTagDyadic_domain hq).1
  have hA : 1 ≤ vfMidSameTagDyadicStart q :=
    (vfMidSameTagDyadic_domain hq).2.1
  have hUpperPos : 0 < (2 * vfMidSameTagDyadicStart q) ^ 2 := by
    have hA0 : 0 < vfMidSameTagDyadicStart q := by omega
    positivity
  simp only [vfMidSameTagDyadicFibre, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hlo, hhi⟩, hpPrime, hp3⟩
    have hlow : (vfMidSameTagDyadicStart q) ^ 2 < p * q := by
      exact (Nat.div_lt_iff_lt_mul hq0).mp hlo
    have hhigh : p * q ≤ (2 * vfMidSameTagDyadicStart q) ^ 2 - 1 :=
      (Nat.le_div_iff_mul_le hq0).mp hhi
    exact ⟨hpPrime, hp3, hlow, by omega⟩
  · rintro ⟨hpPrime, hp3, hlow, hhigh⟩
    have hlo : vfMidSameTagDyadicLower q < p := by
      exact (Nat.div_lt_iff_lt_mul hq0).mpr hlow
    have hhi : p ≤ vfMidSameTagDyadicUpper q := by
      apply (Nat.le_div_iff_mul_le hq0).mpr
      omega
    exact ⟨⟨hlo, hhi⟩, hpPrime, hp3⟩

/-- Native primeCounting is the cardinality of genuine prime integers
at or below its upper endpoint. -/
private theorem vfMidSameTag_primeCounting_range (N : ℕ) :
    ((Finset.range (N + 1)).filter Nat.Prime).card =
      Nat.primeCounting N := by
  unfold Nat.primeCounting Nat.primeCounting'
  rw [Nat.count_eq_card_filter_range]

/-- Actual prime counts split exactly across any two ordered integer walls. -/
private theorem vfMidSameTag_primeCount_split
    (L U : ℕ) (hLU : L ≤ U) :
    ((Finset.Ioc L U).filter Nat.Prime).card +
        Nat.primeCounting L = Nat.primeCounting U := by
  let E : Finset ℕ := (Finset.range (L + 1)).filter Nat.Prime
  let F : Finset ℕ := (Finset.Ioc L U).filter Nat.Prime
  let G : Finset ℕ := (Finset.range (U + 1)).filter Nat.Prime
  have hdisj : Disjoint E F := by
    apply Finset.disjoint_left.mpr
    intro p hpE hpF
    have he : p ≤ L := by
      have he := (Finset.mem_filter.mp hpE).1
      simpa only [Finset.mem_range, Nat.lt_succ_iff] using! he
    have hf : L < p := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hpF).1).1
    omega
  have hunion : E ∪ F = G := by
    ext p
    simp only [E, F, G, Finset.mem_union, Finset.mem_filter,
      Finset.mem_range, Finset.mem_Ioc, Nat.lt_succ_iff]
    constructor
    · rintro (⟨hpL, hpPrime⟩ | ⟨⟨hpL, hpU⟩, hpPrime⟩)
      · exact ⟨hpL.trans hLU, hpPrime⟩
      · exact ⟨hpU, hpPrime⟩
    · rintro ⟨hpU, hpPrime⟩
      by_cases hpL : p ≤ L
      · exact Or.inl ⟨hpL, hpPrime⟩
      · exact Or.inr ⟨⟨by omega, hpU⟩, hpPrime⟩
  have hcard := congrArg Finset.card hunion
  rw [Finset.card_union_of_disjoint hdisj] at hcard
  rw [vfMidSameTag_primeCounting_range L,
      vfMidSameTag_primeCounting_range U] at hcard
  simpa [E, F, G, add_comm] using! hcard

/-- Excluding the even prime is an exact one-unit correction, not an
asymptotic approximation. -/
private theorem vfMidSameTag_oddPrimeCount_split
    (L U : ℕ) (hLU : L ≤ U) :
    ((Finset.Ioc L U).filter (fun p => p.Prime ∧ 3 ≤ p)).card +
        Nat.primeCounting L +
        (if L < 2 ∧ 2 ≤ U then 1 else 0) =
      Nat.primeCounting U := by
  let F : Finset ℕ := (Finset.Ioc L U).filter Nat.Prime
  let O : Finset ℕ := (Finset.Ioc L U).filter
    (fun p => p.Prime ∧ 3 ≤ p)
  have hO : O = F.erase 2 := by
    ext p
    simp only [O, F, Finset.mem_filter, Finset.mem_Ioc,
      Finset.mem_erase]
    constructor
    · rintro ⟨⟨hpL, hpU⟩, hpPrime, hp3⟩
      exact ⟨by omega, ⟨⟨hpL, hpU⟩, hpPrime⟩⟩
    · rintro ⟨hpNe, ⟨⟨hpL, hpU⟩, hpPrime⟩⟩
      have hp2 := hpPrime.two_le
      exact ⟨⟨hpL, hpU⟩, hpPrime, by omega⟩
  have hCount := vfMidSameTag_primeCount_split L U hLU
  change F.card + Nat.primeCounting L = Nat.primeCounting U at hCount
  have hTwo : 2 ∈ F ↔ L < 2 ∧ 2 ≤ U := by
    simp [F, Nat.prime_two]
  change O.card + Nat.primeCounting L +
      (if L < 2 ∧ 2 ≤ U then 1 else 0) = Nat.primeCounting U
  by_cases heven : 2 ∈ F
  · have hCond : L < 2 ∧ 2 ≤ U := hTwo.mp heven
    have hErase := Finset.card_erase_of_mem heven
    have hFpos : 0 < F.card := Finset.card_pos.mpr ⟨2, heven⟩
    rw [hO, hErase]
    simp only [ite_eq_left hCond]
    omega
  · have hCond : ¬(L < 2 ∧ 2 ≤ U) := by
      intro h
      exact heven (hTwo.mpr h)
    have hErase : F.erase 2 = F := Finset.erase_eq_of_notMem heven
    rw [hO, hErase]
    simp only [ite_eq_right hCond]
    omega

/-- Exact Analytic Type II prime-fibre formula, corrected for q>=4096.
The small even-prime indicator is included for all finite q in the domain. -/
theorem vfMidSameTagDyadicFibre_card_plus_counts
    {q : ℕ} (hq : 4096 ≤ q) :
    (vfMidSameTagDyadicFibre q).card +
        Nat.primeCounting (vfMidSameTagDyadicLower q) +
        (if vfMidSameTagDyadicLower q < 2 ∧
            2 ≤ vfMidSameTagDyadicUpper q then 1 else 0) =
      Nat.primeCounting (vfMidSameTagDyadicUpper q) := by
  exact vfMidSameTag_oddPrimeCount_split
    (vfMidSameTagDyadicLower q)
    (vfMidSameTagDyadicUpper q)
    (vfMidSameTagDyadic_domain hq).2.2

/-- Actual raw VF weights on this exact finite prime owner fibre. These
are the physical current charges, not copied historical charges. -/
def vfMidSameTagDyadicCurrentMass (q : ℕ) : ℝ :=
  ∑ p ∈ vfMidSameTagDyadicFibre q,
    vfMidOddFractionalPrimeSeatWeight (Nat.sqrt (p * q))

#print axioms mem_vfMidSameTagDyadicFibre_iff
#print axioms vfMidSameTagDyadicFibre_card_plus_counts

end RHLean.Analysis
