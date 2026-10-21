import Mathlib
import «research.VF_MID_HISTORICAL_PRIME_MULTIPLICITY»
import «research.VF_MID_OWNER_SIGNED_PAIR_BOUNDS»

/-!
# Repeated historical-prime tags: sharp local geometry and payment limits

The literal historical prime q is ONE physical occurrence, regardless of
how many current owner products p*q are selected. These results are
restricted to genuine odd-prime small owners with the original VF
odd-seat coefficients.

Accepted 2026-10-14 Referee claims wheel-8, census-11, census-12.
No first-bad source admission, historical tag cloning, mask invariance,
or global NNS covariance payment is inferred.
-/

noncomputable section
namespace RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Translate the exact 2^20 cofactor threshold into an integer root
spacing of 1024. The owner gap is at least two (distinct odd primes). -/
private theorem vfMidSameTag_root_gap_two
    {p₁ p₂ q : ℕ}
    (hpGap : p₁ + 2 ≤ p₂)
    (hq : 1048576 * p₂ ≤ q) :
    Nat.sqrt (p₁ * q) + 1024 ≤ Nat.sqrt (p₂ * q) := by
  let r := Nat.sqrt (p₁ * q)
  let s := Nat.sqrt (p₂ * q)
  have hrSquare : r ^ 2 ≤ p₁ * q := Nat.sqrt_le' _
  have hsUpper : p₂ * q < (s + 1) ^ 2 := Nat.lt_succ_sqrt' _
  have hqLarge : 1048576 * (p₁ + 2) ≤ q := by
    nlinarith
  have hprodReal :
      0 ≤ (q : ℝ) * ((q : ℝ) - 1048576 * ((p₁ : ℝ) + 1)) := by
    apply mul_nonneg (by positivity)
    have hqR : (1048576 : ℝ) * ((p₁ : ℝ) + 2) ≤ (q : ℝ) := by
      exact_mod_cast hqLarge
    nlinarith
  have hrReal : (r : ℝ) ^ 2 ≤ (p₁ : ℝ) * (q : ℝ) := by
    exact_mod_cast hrSquare
  have hrootCeiling : 1024 * r + 524288 ≤ q := by
    by_contra h
    have hbad : q < 1024 * r + 524288 := by omega
    have hbadR : (q : ℝ) < 1024 * (r : ℝ) + 524288 := by
      exact_mod_cast hbad
    have hleft : 0 < (q : ℝ) - 524288 := by
      have hqR : (1048576 : ℝ) * ((p₁ : ℝ) + 2) ≤ (q : ℝ) := by
        exact_mod_cast hqLarge
      nlinarith
    have hright : 0 < 1024 * (r : ℝ) - ((q : ℝ) - 524288) := by
      linarith
    have hsquareDiff :=
      mul_pos hright
        (show 0 < 1024 * (r : ℝ) + ((q : ℝ) - 524288) by
          have hr0 : 0 ≤ (r : ℝ) := by positivity
          linarith)
    nlinarith [hprodReal, hrReal, hsquareDiff]
  by_contra h
  have hsmall : s < r + 1024 := by omega
  have hlt : p₂ * q < (r + 1024) ^ 2 := by
    calc
      p₂ * q < (s + 1) ^ 2 := hsUpper
      _ ≤ (r + 1024) ^ 2 :=
        Nat.pow_le_pow_left (by omega : s + 1 ≤ r + 1024) 2
  have hmul : (p₁ + 2) * q ≤ p₂ * q :=
    Nat.mul_le_mul_right q hpGap
  nlinarith [hrSquare, hrootCeiling, hmul, hlt]

/-- 1024 is a UNIFORM genuine-tag gap; it is not an assertion of
same-owner uniqueness across arbitrarily long runs. -/
theorem vfMidSameTag_root_spacing_1024
    {p₁ p₂ q : ℕ}
    (hp₁ : p₁.Prime) (hp₂ : p₂.Prime)
    (h₃ : 3 ≤ p₁) (h₁₂ : p₁ < p₂)
    (hscale : 1024 * p₂ ≤ Nat.sqrt (p₂ * q)) :
    Nat.sqrt (p₁ * q) + 1024 ≤ Nat.sqrt (p₂ * q) := by
  have hodd₁ : Odd p₁ := hp₁.odd_of_ne_two (by omega)
  have hodd₂ : Odd p₂ := hp₂.odd_of_ne_two (by omega)
  obtain ⟨k₁, hk₁⟩ := hodd₁
  obtain ⟨k₂, hk₂⟩ := hodd₂
  have hgap : p₁ + 2 ≤ p₂ := by omega
  have hq : 1048576 * p₂ ≤ q :=
    (vfMidHistoricalOwner_sqrt_iff hp₂.pos).mp hscale
  exact vfMidSameTag_root_gap_two hgap hq

/-- A larger owner diameter of twelve produces a root span of
at least six 1024-units. This is an arithmetic inequality, not a
statement about masks or historical admission. -/
private theorem vfMidSameTag_root_gap_twelve
    {p₁ p₂ q : ℕ}
    (hpGap : p₁ + 12 ≤ p₂)
    (hq : 1048576 * p₂ ≤ q) :
    Nat.sqrt (p₁ * q) + 6144 ≤ Nat.sqrt (p₂ * q) := by
  let r := Nat.sqrt (p₁ * q)
  let s := Nat.sqrt (p₂ * q)
  have hrSquare : r ^ 2 ≤ p₁ * q := Nat.sqrt_le' _
  have hsUpper : p₂ * q < (s + 1) ^ 2 := Nat.lt_succ_sqrt' _
  have hqLarge : 1048576 * (p₁ + 12) ≤ q := by
    nlinarith
  have hprodReal :
      0 ≤ (q : ℝ) * ((q : ℝ) - 1048576 * ((p₁ : ℝ) + 6)) := by
    apply mul_nonneg (by positivity)
    have hqR : (1048576 : ℝ) * ((p₁ : ℝ) + 12) ≤ (q : ℝ) := by
      exact_mod_cast hqLarge
    nlinarith
  have hrReal : (r : ℝ) ^ 2 ≤ (p₁ : ℝ) * (q : ℝ) := by
    exact_mod_cast hrSquare
  have hrootCeiling : 1024 * r + 3145728 ≤ q := by
    by_contra h
    have hbad : q < 1024 * r + 3145728 := by omega
    have hbadR : (q : ℝ) < 1024 * (r : ℝ) + 3145728 := by
      exact_mod_cast hbad
    have hleft : 0 < (q : ℝ) - 3145728 := by
      have hqR : (1048576 : ℝ) * ((p₁ : ℝ) + 12) ≤ (q : ℝ) := by
        exact_mod_cast hqLarge
      nlinarith
    have hright : 0 < 1024 * (r : ℝ) - ((q : ℝ) - 3145728) := by
      linarith
    have hsquareDiff :=
      mul_pos hright
        (show 0 < 1024 * (r : ℝ) + ((q : ℝ) - 3145728) by
          have hr0 : 0 ≤ (r : ℝ) := by positivity
          linarith)
    nlinarith [hprodReal, hrReal, hsquareDiff]
  by_contra h
  have hsmall : s < r + 6144 := by omega
  have hlt : p₂ * q < (r + 6144) ^ 2 := by
    calc
      p₂ * q < (s + 1) ^ 2 := hsUpper
      _ ≤ (r + 6144) ^ 2 :=
        Nat.pow_le_pow_left (by omega : s + 1 ≤ r + 6144) 2
  have hmul : (p₁ + 12) * q ≤ p₂ * q :=
    Nat.mul_le_mul_right q hpGap
  nlinarith [hrSquare, hrootCeiling, hmul, hlt]

/-- Exceptional first owner 3: a fifth prime owner must be at least
13. The true root span is already greater than the 6144 window. -/
private theorem vfMidSameTag_root_gap_three_to_thirteen
    {p₂ q : ℕ}
    (hp₂ : 13 ≤ p₂)
    (hq : 1048576 * p₂ ≤ q) :
    Nat.sqrt (3 * q) + 6144 ≤ Nat.sqrt (p₂ * q) := by
  let r := Nat.sqrt (3 * q)
  let s := Nat.sqrt (p₂ * q)
  have hrSquare : r ^ 2 ≤ 3 * q := Nat.sqrt_le' _
  have hsUpper : p₂ * q < (s + 1) ^ 2 := Nat.lt_succ_sqrt' _
  have hqLarge : 13 * 1048576 ≤ q := by nlinarith
  have hrReal : (r : ℝ) ^ 2 ≤ 3 * (q : ℝ) := by
    exact_mod_cast hrSquare
  have hprodReal : 0 ≤ (q : ℝ) * ((q : ℝ) - 12 * 1048576) := by
    apply mul_nonneg (by positivity)
    have hqR : (13 * 1048576 : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast hqLarge
    norm_num at hqR ⊢
    linarith
  have hrootCeiling : 2048 * r ≤ q := by
    by_contra h
    have hbad : q < 2048 * r := by omega
    have hbadR : (q : ℝ) < 2048 * (r : ℝ) := by exact_mod_cast hbad
    have hprod := mul_pos
      (show 0 < 2048 * (r : ℝ) - (q : ℝ) by linarith)
      (show 0 < 2048 * (r : ℝ) + (q : ℝ) by
        have hqR : (0 : ℝ) < (q : ℝ) := by
          have hq0 : 0 < q := by omega
          exact_mod_cast hq0
        have hr0 : 0 ≤ (r : ℝ) := by positivity
        linarith)
    nlinarith [hprodReal, hrReal, hprod]
  by_contra h
  have hsmall : s < r + 6144 := by omega
  have hlt : p₂ * q < (r + 6144) ^ 2 := by
    calc
      p₂ * q < (s + 1) ^ 2 := hsUpper
      _ ≤ (r + 6144) ^ 2 :=
        Nat.pow_le_pow_left (by omega : s + 1 ≤ r + 6144) 2
  have hmul : 13 * q ≤ p₂ * q :=
    Nat.mul_le_mul_right q hp₂
  nlinarith [hrSquare, hrootCeiling, hmul, hlt, hqLarge]


/-- A genuine prime at least five is a unit modulo six. -/
private theorem vfMidSameTag_prime_mod_six
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    p % 6 = 1 ∨ p % 6 = 5 := by
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  obtain ⟨k, hk⟩ := hodd
  have hnot3 : p % 3 ≠ 0 := by
    intro hz
    have hdiv : 3 ∣ p := Nat.dvd_of_mod_eq_zero hz
    rcases (Nat.dvd_prime hp).mp hdiv with heq | heq
    · omega
    · omega
  omega

/-- Every twelve consecutive integers contain exactly four residue positions
coprime to six. The calculation is independent of the starting integer. -/
private theorem vfMidSameTag_twelve_residue_capacity (a : ℕ) :
    ((Finset.range 12).filter
       (fun k => (a + k) % 6 = 1 ∨ (a + k) % 6 = 5)).card = 4 := by
  have hset :
      ((Finset.range 12).filter
        (fun k => (a + k) % 6 = 1 ∨ (a + k) % 6 = 5)) =
      ((Finset.range 12).filter
        (fun k => (a % 6 + k) % 6 = 1 ∨ (a % 6 + k) % 6 = 5)) := by
    ext k
    simp only [Finset.mem_filter]
    have hmod : (a + k) % 6 = (a % 6 + k) % 6 := by omega
    rw [hmod]
  rw [hset]
  have hcalc : ∀ r : ℕ, r < 6 →
      ((Finset.range 12).filter
        (fun k => (r + k) % 6 = 1 ∨ (r + k) % 6 = 5)).card = 4 := by
    intro r hr
    interval_cases r <;> decide
  exact hcalc (a % 6) (Nat.mod_lt _ (by norm_num))

/-- Pure elementary finite-prime restriction. More than four primes >=5
cannot lie in twelve consecutive integers. -/
private theorem vfMidSameTag_prime_interval_twelve_card_le_four
    {a : ℕ} (ha : 5 ≤ a) :
    ((Finset.Icc a (a + 11)).filter Nat.Prime).card ≤ 4 := by
  let S : Finset ℕ := (Finset.Icc a (a + 11)).filter Nat.Prime
  let T : Finset ℕ :=
    (Finset.range 12).filter
      (fun k => (a + k) % 6 = 1 ∨ (a + k) % 6 = 5)
  have hmap : Set.MapsTo (fun p : ℕ => p - a) (S : Set ℕ) (T : Set ℕ) := by
    intro p hp
    have hmember := (Finset.mem_filter.mp hp).1
    have hpPrime := (Finset.mem_filter.mp hp).2
    have hlo : a ≤ p := (Finset.mem_Icc.mp hmember).1
    have hhi : p ≤ a + 11 := (Finset.mem_Icc.mp hmember).2
    have hres : p % 6 = 1 ∨ p % 6 = 5 :=
      vfMidSameTag_prime_mod_six hpPrime (by omega)
    have heq : a + (p - a) = p := Nat.add_sub_of_le hlo
    change p - a ∈ T
    simp only [T, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, by simpa [heq] using! hres⟩
  have hinj : Set.InjOn (fun p : ℕ => p - a) (S : Set ℕ) := by
    intro p hp p' hp' heq
    have hpLo : a ≤ p :=
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
    have hp'Lo : a ≤ p' :=
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hp').1).1
    change p - a = p' - a at heq
    omega
  calc
    S.card ≤ T.card := Finset.card_le_card_of_injOn _ hmap hinj
    _ = 4 := vfMidSameTag_twelve_residue_capacity a

/-- The physical carrier for an individual historical prime in a
half-open window of square ROOTS. Membership retains the genuine
least-owner threshold, rather than replacing it with a wheel or density. -/
def vfMidSameTagWindow (q A B : ℕ) : Finset ℕ :=
  (vfMidHistoricalPrimeOwnerFibre q).filter
    (fun p => A ≤ Nat.sqrt (p * q) ∧ Nat.sqrt (p * q) < B)

@[simp] theorem mem_vfMidSameTagWindow {q A B p : ℕ} :
    p ∈ vfMidSameTagWindow q A B ↔
      p.Prime ∧ 3 ≤ p ∧
        1024 * p ≤ Nat.sqrt (p * q) ∧
        A ≤ Nat.sqrt (p * q) ∧ Nat.sqrt (p * q) < B := by
  simp only [vfMidSameTagWindow, Finset.mem_filter]
  rw [mem_vfMidHistoricalPrimeOwnerFibre_iff]
  constructor
  · rintro ⟨⟨hp, hp3, hpDiv⟩, hA, hB⟩
    have hqBound : vfMidHistoricalOwnerThreshold * p ≤ q := by
      have h := (Nat.le_div_iff_mul_le
        (by norm_num [vfMidHistoricalOwnerThreshold])).1 hpDiv
      simpa [Nat.mul_comm] using! h
    exact ⟨hp, hp3,
      (vfMidHistoricalOwner_sqrt_iff (by omega : 0 < p)).mpr hqBound,
      hA, hB⟩
  · rintro ⟨hp, hp3, hroot, hA, hB⟩
    have hqBound := (vfMidHistoricalOwner_sqrt_iff
      (by omega : 0 < p)).mp hroot
    have hpDiv : p ≤ q / vfMidHistoricalOwnerThreshold := by
      apply (Nat.le_div_iff_mul_le
        (by norm_num [vfMidHistoricalOwnerThreshold])).2
      simpa [Nat.mul_comm] using! hqBound
    exact ⟨⟨hp, hp3, hpDiv⟩, hA, hB⟩

/-- The optimal four-owner capacity in an arbitrary 6144-root window.
The historical prime q can have unbounded total descendants in a longer run. -/
theorem vfMidSameTagWindow_card_le_four
    (q A B : ℕ) (hAB : B ≤ A + 6144) :
    (vfMidSameTagWindow q A B).card ≤ 4 := by
  let S : Finset ℕ := vfMidSameTagWindow q A B
  by_cases hS : S.Nonempty
  · let m := S.min' hS
    have hm : m ∈ S := Finset.min'_mem S hS
    have hmData := (mem_vfMidSameTagWindow.mp hm)
    have hmPrime : m.Prime := hmData.1
    have hm3 : 3 ≤ m := hmData.2.1
    have hmA : A ≤ Nat.sqrt (m * q) := hmData.2.2.2.1
    have hmin : ∀ p ∈ S, m ≤ p := by
      intro p hp
      exact Finset.min'_le S p hp
    have hnear : ∀ p ∈ S, p < m + 12 := by
      intro p hp
      by_contra hnot
      have hgap : m + 12 ≤ p := by omega
      have hpData := mem_vfMidSameTagWindow.mp hp
      have hscale : 1048576 * p ≤ q :=
        (vfMidHistoricalOwner_sqrt_iff hpData.1.pos).mp hpData.2.2.1
      have hfar : Nat.sqrt (m * q) + 6144 ≤ Nat.sqrt (p * q) :=
        vfMidSameTag_root_gap_twelve hgap hscale
      omega
    by_cases hm3eq : m = 3
    · have hsub : S ⊆ ({3, 5, 7, 11} : Finset ℕ) := by
        intro p hp
        have hpData := mem_vfMidSameTagWindow.mp hp
        have hle : m ≤ p := hmin p hp
        have hlt : p < m + 12 := hnear p hp
        have hlt13 : p < 13 := by
          by_contra hn
          have h13 : 13 ≤ p := by omega
          have hscale : 1048576 * p ≤ q :=
            (vfMidHistoricalOwner_sqrt_iff hpData.1.pos).mp hpData.2.2.1
          have hfar : Nat.sqrt (3 * q) + 6144 ≤ Nat.sqrt (p * q) :=
            vfMidSameTag_root_gap_three_to_thirteen h13 hscale
          have hpB := hpData.2.2.2.2
          rw [hm3eq] at hmA
          omega
        by_cases hpEq : p = 3
        · simp [hpEq]
        · have hpOdd := hpData.1.odd_of_ne_two (by omega)
          obtain ⟨k, hk⟩ := hpOdd
          have hp5 : 5 ≤ p := by omega
          have hres := vfMidSameTag_prime_mod_six hpData.1 hp5
          simp only [Finset.mem_insert, Finset.mem_singleton]
          omega
      exact (Finset.card_le_card hsub).trans (by norm_num)
    · have hm5 : 5 ≤ m := by
        have hodd := hmPrime.odd_of_ne_two (by omega)
        obtain ⟨k, hk⟩ := hodd
        omega
      have hsub :
          S ⊆ (Finset.Icc m (m + 11)).filter Nat.Prime := by
        intro p hp
        have hpData := mem_vfMidSameTagWindow.mp hp
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_Icc.mpr ⟨hmin p hp, by have := hnear p hp; omega⟩,
            hpData.1⟩
      exact (Finset.card_le_card hsub).trans
        (vfMidSameTag_prime_interval_twelve_card_le_four hm5)
  · have hEmpty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    change S.card ≤ 4
    rw [hEmpty]
    simp

/-- A historical q supporting at least one selected eligible owner must
itself lie past the actual 1024-th historical square root. -/
private theorem vfMidSameTag_historical_root_ge
    {q A B : ℕ} (hS : (vfMidSameTagWindow q A B).Nonempty) :
    1024 ≤ Nat.sqrt q := by
  obtain ⟨p, hp⟩ := hS
  have hpData := mem_vfMidSameTagWindow.mp hp
  have hqBound : 1048576 * p ≤ q :=
    (vfMidHistoricalOwner_sqrt_iff hpData.1.pos).mp hpData.2.2.1
  apply (Nat.le_sqrt).2
  have hp3 : 3 ≤ p := hpData.2.1
  nlinarith

/-- Current products are composite, hence carry the *literal* positive
VF odd-seat weight, not an independently invented owner proxy. -/
private theorem vfMidSameTag_current_charge_eq
    {q A B p : ℕ} (hq : q.Prime)
    (hp : p ∈ vfMidSameTagWindow q A B) :
    vfMidOddSignedSeatCharge (Nat.sqrt (p * q)) (p * q) =
      vfMidOddFractionalPrimeSeatWeight (Nat.sqrt (p * q)) := by
  have hpPrime := (mem_vfMidSameTagWindow.mp hp).1
  have hnNotPrime : ¬(p * q).Prime := by
    intro h
    have hdiv : p ∣ p * q := dvd_mul_right p q
    rcases (Nat.dvd_prime h).mp hdiv with h1 | heq
    · exact hpPrime.ne_one h1
    · have hm : 2 * p ≤ p * q := by
        simpa [Nat.mul_comm] using! Nat.mul_le_mul_left p hq.two_le
      have hp2 := hpPrime.two_le
      nlinarith
  exact vfMidOddSignedSeatCharge_of_not_prime
    (Nat.sqrt (p * q)) (p * q) hnNotPrime

/-- A single historical q is spent ONCE and at most four current
descendants are included. The sharp rational original-coefficient margin
is -181/640. It is a local LINEAR packet, not a global NNS bound. -/
theorem vfMidSameTagWindow_one_history_signed_packet
    {q A B : ℕ} (hq : q.Prime)
    (hAB : B ≤ A + 6144)
    (hS : (vfMidSameTagWindow q A B).Nonempty) :
    (∑ p ∈ vfMidSameTagWindow q A B,
      vfMidOddSignedSeatCharge (Nat.sqrt (p * q)) (p * q)) +
        vfMidOddSignedSeatCharge (Nat.sqrt q) q <
      -(181 / 640 : ℝ) := by
  let S : Finset ℕ := vfMidSameTagWindow q A B
  have hcard : S.card ≤ 4 := vfMidSameTagWindow_card_le_four q A B hAB
  have hcardR : (S.card : ℝ) ≤ 4 := by exact_mod_cast hcard
  have hsum : (∑ p ∈ S,
       vfMidOddSignedSeatCharge (Nat.sqrt (p * q)) (p * q)) ≤
        (S.card : ℝ) * (9 / 64 : ℝ) := by
    calc
      _ ≤ ∑ p ∈ S, (9 / 64 : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpData := mem_vfMidSameTagWindow.mp hp
        have hR : 2048 ≤ Nat.sqrt (p * q) := by
          have hr := hpData.2.2.1
          omega
        rw [vfMidSameTag_current_charge_eq hq hp]
        exact (vfMidOddWeight_lt_9_div_64 hR).le
      _ = (S.card : ℝ) * (9 / 64 : ℝ) := by
        simp [nsmul_eq_mul]
  have hr : 1024 ≤ Nat.sqrt q :=
    vfMidSameTag_historical_root_ge hS
  have hweight := vfMidOddWeight_lt_99_div_640 hr
  rw [vfMidOddSignedSeatCharge_of_prime (Nat.sqrt q) q hq]
  linarith

#print axioms vfMidSameTag_root_spacing_1024
#print axioms vfMidSameTagWindow_card_le_four
#print axioms vfMidSameTagWindow_one_history_signed_packet

end RHLean.Analysis
