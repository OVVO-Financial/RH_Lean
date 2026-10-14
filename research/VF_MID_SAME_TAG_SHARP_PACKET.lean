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
      positivity
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

#print axioms vfMidSameTag_root_spacing_1024

end RHLean.Analysis
