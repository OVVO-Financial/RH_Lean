import Mathlib
import RHLean.Proof.CanonicalHighSectorBridge

/-!
# Canonical low-height occupancy

This file proves the elementary bounded-occupancy theorem for canonical
low-height sources in square blocks and constructs an unconditional
`CanonicalLowIncrementControl`.

For a canonical factor pair, write the sorted factors as `r <= r + d`.
Inside the block `[j^2,(j+1)^2)`, consecutive products with fixed positive
factor gap `d` differ by at least `2j+1`, so at most one source realizes each
positive gap. The height cutoff forces the gap into a finite range independent
of `j`. The isolated initial source is absorbed into the final uniform bound.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

theorem canonicalLargestPrimeFactor_mem_primeFactors {m : ℕ} (h : 1 < m) :
    canonicalLargestPrimeFactor m ∈ m.primeFactors := by
  unfold canonicalLargestPrimeFactor
  rw [dif_pos h]
  exact Finset.max'_mem m.primeFactors (Nat.nonempty_primeFactors.mpr h)

theorem canonicalLargestPrimeFactor_dvd {m : ℕ} (h : 1 < m) :
    canonicalLargestPrimeFactor m ∣ m :=
  (Nat.mem_primeFactors.mp (canonicalLargestPrimeFactor_mem_primeFactors h)).2.1

theorem canonicalCofactor_mul {m : ℕ} (h : 1 < m) :
    canonicalCofactor m * canonicalLargestPrimeFactor m = m := by
  unfold canonicalCofactor
  exact Nat.div_mul_cancel (canonicalLargestPrimeFactor_dvd h)

/-- Smaller member of the canonical factor pair. -/
def canonicalPairLo (m : ℕ) : ℕ :=
  min (canonicalCofactor m) (canonicalLargestPrimeFactor m)

/-- Larger member of the canonical factor pair. -/
def canonicalPairHi (m : ℕ) : ℕ :=
  max (canonicalCofactor m) (canonicalLargestPrimeFactor m)

theorem canonicalPairLo_le_Hi (m : ℕ) :
    canonicalPairLo m ≤ canonicalPairHi m :=
  min_le_max

theorem canonicalPair_mul {m : ℕ} (h : 1 < m) :
    canonicalPairLo m * canonicalPairHi m = m := by
  unfold canonicalPairLo canonicalPairHi
  rcases le_total (canonicalCofactor m) (canonicalLargestPrimeFactor m) with hle | hle
  · rw [min_eq_left hle, max_eq_right hle]
    exact canonicalCofactor_mul h
  · rw [min_eq_right hle, max_eq_left hle, mul_comm]
    exact canonicalCofactor_mul h

/-- Absolute gap of the sorted canonical factor pair. -/
def canonicalGap (m : ℕ) : ℕ :=
  canonicalPairHi m - canonicalPairLo m

theorem canonicalPairLo_add_gap (m : ℕ) :
    canonicalPairLo m + canonicalGap m = canonicalPairHi m := by
  unfold canonicalGap
  omega

/-- AM-GM in the exact natural-number form needed by the occupancy proof. -/
theorem two_mul_le_of_sq_le_mul (r d j : ℕ)
    (h : j ^ 2 ≤ r * (r + d)) :
    2 * j ≤ 2 * r + d := by
  by_contra hc
  push_neg at hc
  have hc' : 2 * r + d + 1 ≤ 2 * j := by omega
  have hsq : (2 * r + d + 1) ^ 2 ≤ (2 * j) ^ 2 :=
    Nat.pow_le_pow_left hc' 2
  have hexpand :
      (2 * r + d + 1) ^ 2 =
        4 * (r * (r + d)) + (d + 1) ^ 2 + 4 * r := by
    ring
  have hexpand2 : (2 * j) ^ 2 = 4 * j ^ 2 := by ring
  have hpos : 1 ≤ (d + 1) ^ 2 := by positivity
  nlinarith

/-- At most one canonical source in a square block realizes a fixed factor gap. -/
theorem eq_of_canonicalGap_eq_in_block
    {j d m m' : ℕ}
    (hm : m ∈ canonicalSquareBlock j)
    (hm' : m' ∈ canonicalSquareBlock j)
    (hm1 : 1 < m) (hm'1 : 1 < m')
    (hgap : canonicalGap m = d)
    (hgap' : canonicalGap m' = d) :
    m = m' := by
  have hprod := canonicalPair_mul hm1
  have hprod' := canonicalPair_mul hm'1
  have hHiLo : canonicalPairLo m + d = canonicalPairHi m := by
    simpa [hgap] using canonicalPairLo_add_gap m
  have hHiLo' : canonicalPairLo m' + d = canonicalPairHi m' := by
    simpa [hgap'] using canonicalPairLo_add_gap m'
  have hjm : j ^ 2 ≤ m ∧ m < (j + 1) ^ 2 := by
    simpa [canonicalSquareBlock, Finset.mem_Ico] using hm
  have hjm' : j ^ 2 ≤ m' ∧ m' < (j + 1) ^ 2 := by
    simpa [canonicalSquareBlock, Finset.mem_Ico] using hm'
  rcases lt_trichotomy (canonicalPairLo m) (canonicalPairLo m') with hlt | heq | hgt
  · have hmeq : m = canonicalPairLo m * (canonicalPairLo m + d) := by
      rw [hHiLo]
      exact hprod.symm
    have hm'eq : m' = canonicalPairLo m' * (canonicalPairLo m' + d) := by
      rw [hHiLo']
      exact hprod'.symm
    have hjr : j ^ 2 ≤ canonicalPairLo m * (canonicalPairLo m + d) := by
      simpa [hmeq] using hjm.1
    have hkey := two_mul_le_of_sq_le_mul (canonicalPairLo m) d j hjr
    have hstep :
        canonicalPairLo m * (canonicalPairLo m + d) + (2 * j + 1) ≤
          canonicalPairLo m' * (canonicalPairLo m' + d) := by
      have hmono :
          (canonicalPairLo m + 1) * (canonicalPairLo m + 1 + d) ≤
            canonicalPairLo m' * (canonicalPairLo m' + d) := by
        apply Nat.mul_le_mul
        · omega
        · omega
      have hexp :
          (canonicalPairLo m + 1) * (canonicalPairLo m + 1 + d) =
            canonicalPairLo m * (canonicalPairLo m + d) +
              (2 * canonicalPairLo m + d + 1) := by
        ring
      omega
    have hsq : j ^ 2 + (2 * j + 1) = (j + 1) ^ 2 := by ring
    omega
  · have hhi : canonicalPairHi m = canonicalPairHi m' := by omega
    rw [← hprod, ← hprod', heq, hhi]
  · have hmeq : m = canonicalPairLo m * (canonicalPairLo m + d) := by
      rw [hHiLo]
      exact hprod.symm
    have hm'eq : m' = canonicalPairLo m' * (canonicalPairLo m' + d) := by
      rw [hHiLo']
      exact hprod'.symm
    have hjr : j ^ 2 ≤ canonicalPairLo m' * (canonicalPairLo m' + d) := by
      simpa [hm'eq] using hjm'.1
    have hkey := two_mul_le_of_sq_le_mul (canonicalPairLo m') d j hjr
    have hstep :
        canonicalPairLo m' * (canonicalPairLo m' + d) + (2 * j + 1) ≤
          canonicalPairLo m * (canonicalPairLo m + d) := by
      have hmono :
          (canonicalPairLo m' + 1) * (canonicalPairLo m' + 1 + d) ≤
            canonicalPairLo m * (canonicalPairLo m + d) := by
        apply Nat.mul_le_mul
        · omega
        · omega
      have hexp :
          (canonicalPairLo m' + 1) * (canonicalPairLo m' + 1 + d) =
            canonicalPairLo m' * (canonicalPairLo m' + d) +
              (2 * canonicalPairLo m' + d + 1) := by
        ring
      omega
    have hsq : j ^ 2 + (2 * j + 1) = (j + 1) ^ 2 := by ring
    omega

/-- Absolute doubled height equals gap times factor sum. -/
theorem abs_canonicalHeightTwice_eq {m : ℕ} (h : 1 < m) :
    |canonicalHeightTwice m| =
      (canonicalGap m : ℝ) *
        ((canonicalPairLo m : ℝ) + (canonicalPairHi m : ℝ)) := by
  unfold canonicalHeightTwice canonicalGap canonicalPairLo canonicalPairHi
  rcases le_total (canonicalCofactor m) (canonicalLargestPrimeFactor m) with hle | hle
  · rw [min_eq_left hle, max_eq_right hle]
    have hcast :
        ((canonicalLargestPrimeFactor m - canonicalCofactor m : ℕ) : ℝ) =
          (canonicalLargestPrimeFactor m : ℝ) - (canonicalCofactor m : ℝ) := by
      exact_mod_cast Nat.cast_sub hle
    rw [hcast, abs_of_nonneg]
    · ring
    · exact sub_nonneg.mpr (by exact_mod_cast hle)
  · rw [min_eq_right hle, max_eq_left hle]
    have hcast :
        ((canonicalCofactor m - canonicalLargestPrimeFactor m : ℕ) : ℝ) =
          (canonicalCofactor m : ℝ) - (canonicalLargestPrimeFactor m : ℝ) := by
      exact_mod_cast Nat.cast_sub hle
    rw [hcast, abs_of_nonpos]
    · ring
    · exact sub_nonpos.mpr (by exact_mod_cast hle)

/-- Low height forces the canonical factor gap to be at most the cutoff. -/
theorem canonicalGap_le_of_lowHeight
    {Λ : ℝ} {j m : ℕ}
    (hj : 1 ≤ j)
    (hm : m ∈ canonicalSquareBlock j)
    (hm1 : 1 < m)
    (hlow : IsCanonicalLowHeight Λ j m) :
    (canonicalGap m : ℝ) ≤ Λ := by
  have hjm : j ^ 2 ≤ m := by
    simpa [canonicalSquareBlock, Finset.mem_Ico] using hm.1
  have hprod := canonicalPair_mul hm1
  have hgapform := canonicalPairLo_add_gap m
  have hjr :
      j ^ 2 ≤ canonicalPairLo m * (canonicalPairLo m + canonicalGap m) := by
    rw [hgapform, hprod]
    exact hjm
  have hkey := two_mul_le_of_sq_le_mul
    (canonicalPairLo m) (canonicalGap m) j hjr
  have hsum :
      (2 : ℝ) * (j : ℝ) ≤
        (canonicalPairLo m : ℝ) + (canonicalPairHi m : ℝ) := by
    exact_mod_cast (show 2 * j ≤ canonicalPairLo m + canonicalPairHi m by
      rw [← hgapform]
      omega)
  have habs := abs_canonicalHeightTwice_eq hm1
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj
  have hgap_nonneg : 0 ≤ (canonicalGap m : ℝ) := by positivity
  nlinarith [hlow, habs]

/-- Low-height nontrivial sources inject into their canonical gap. -/
theorem canonicalGap_injOn_lowHeight {Λ : ℝ} {j : ℕ} :
    Set.InjOn canonicalGap
      {m | m ∈ canonicalSquareBlock j ∧ 1 < m ∧ IsCanonicalLowHeight Λ j m} := by
  intro m hm m' hm' hgap
  exact eq_of_canonicalGap_eq_in_block
    hm.1 hm'.1 hm.2.1 hm'.2.1 hgap rfl

/-- Uniform finite occupancy of nontrivial low-height sources. -/
theorem card_canonicalLowHeight_nontrivial_le
    {Λ : ℝ} (hΛ : 0 ≤ Λ) {j : ℕ} (hj : 1 ≤ j) :
    ((canonicalSquareBlock j).filter
      (fun m => 1 < m ∧ IsCanonicalLowHeight Λ j m)).card ≤
        Nat.floor Λ + 1 := by
  classical
  let s := (canonicalSquareBlock j).filter
    (fun m => 1 < m ∧ IsCanonicalLowHeight Λ j m)
  have hinj : Set.InjOn canonicalGap (s : Set ℕ) := by
    intro m hm m' hm' hgap
    simp only [s, Finset.mem_filter] at hm hm'
    exact eq_of_canonicalGap_eq_in_block
      hm.1 hm'.1 hm.2.1 hm'.2.1 hgap rfl
  have hsub : s.image canonicalGap ⊆ Finset.Icc 0 (Nat.floor Λ) := by
    intro d hd
    rcases Finset.mem_image.mp hd with ⟨m, hm, rfl⟩
    simp only [s, Finset.mem_filter] at hm
    have hbound := canonicalGap_le_of_lowHeight hj hm.1 hm.2.1 hm.2.2
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.le_floor hbound⟩
  calc
    s.card = (s.image canonicalGap).card := by
      rw [Finset.card_image_of_injOn hinj]
    _ ≤ (Finset.Icc 0 (Nat.floor Λ)).card := Finset.card_le_card hsub
    _ = Nat.floor Λ + 1 := by simp

/-- Unconditional uniform control of the canonical low increment. -/
noncomputable def canonicalLowIncrementControl
    (Λ : ℝ) (hΛ : 0 ≤ Λ) : CanonicalLowIncrementControl Λ where
  bound := (Nat.floor Λ : ℝ) + 2
  bound_nonneg := by positivity
  norm_increment_le := by
    intro j
    unfold canonicalLowIncrement
    classical
    by_cases hj : 1 ≤ j
    · have hcard := card_canonicalLowHeight_nontrivial_le hΛ hj
      calc
        ‖∑ m ∈ canonicalSquareBlock j,
            if IsCanonicalLowHeight Λ j m then canonicalMoebiusWeight m else 0‖ ≤
            ∑ m ∈ canonicalSquareBlock j,
              ‖if IsCanonicalLowHeight Λ j m then canonicalMoebiusWeight m else 0‖ :=
          norm_sum_le _ _
        _ ≤ ∑ _m ∈ canonicalSquareBlock j, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro m hm
          split_ifs
          · unfold canonicalMoebiusWeight
            rcases ArithmeticFunction.moebius_eq_or m with h | h | h <;> simp [h]
          · simp
        _ = (canonicalSquareBlock j).card := by simp
        _ ≤ ((canonicalSquareBlock j).filter
              (fun m => 1 < m ∧ IsCanonicalLowHeight Λ j m)).card + 1 := by
          have hsupport :
              (canonicalSquareBlock j).filter
                (fun m => IsCanonicalLowHeight Λ j m ∧ canonicalMoebiusWeight m ≠ 0) ⊆
              ((canonicalSquareBlock j).filter
                (fun m => 1 < m ∧ IsCanonicalLowHeight Λ j m)) ∪ {1} := by
            intro m hm
            simp only [Finset.mem_filter] at hm
            by_cases hm1 : 1 < m
            · simp [Finset.mem_union, Finset.mem_filter, hm.1, hm1]
            · have hmle : m ≤ 1 := by omega
              have hmge : j ^ 2 ≤ m := by
                simpa [canonicalSquareBlock, Finset.mem_Ico] using hm.1.1
              have hj2 : 1 ≤ j ^ 2 := by positivity
              have hmpos : 0 < m := by
                by_contra hz
                have : m = 0 := Nat.eq_zero_of_not_pos hz
                subst m
                simp [canonicalMoebiusWeight] at hm
              have hm_eq : m = 1 := by omega
              simp [hm_eq]
          have hnormSupport :
              ∑ m ∈ canonicalSquareBlock j,
                ‖if IsCanonicalLowHeight Λ j m then canonicalMoebiusWeight m else 0‖ =
              ∑ _m ∈ (canonicalSquareBlock j).filter
                (fun m => IsCanonicalLowHeight Λ j m ∧ canonicalMoebiusWeight m ≠ 0),
                (1 : ℝ) := by
            rw [Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro m hm
            by_cases hlow : IsCanonicalLowHeight Λ j m
            · by_cases hmu : canonicalMoebiusWeight m = 0
              · simp [hlow, hmu]
              · unfold canonicalMoebiusWeight at hmu ⊢
                rcases ArithmeticFunction.moebius_eq_or m with h | h | h <;> simp [hlow, hmu, h]
            · simp [hlow]
          rw [hnormSupport]
          simpa using Finset.card_le_card hsupport
        _ ≤ (Nat.floor Λ + 1) + 1 := Nat.add_le_add_right hcard 1
        _ = (Nat.floor Λ : ℝ) + 2 := by norm_num
    · have hj0 : j = 0 := by omega
      subst j
      simp [canonicalSquareBlock, canonicalMoebiusWeight]

/-- The canonical low-height hypothesis used by the high-sector bridge is inhabited
for every nonnegative cutoff. -/
theorem canonicalLowIncrementControl_exists
    (Λ : ℝ) (hΛ : 0 ≤ Λ) :
    Nonempty (CanonicalLowIncrementControl Λ) :=
  ⟨canonicalLowIncrementControl Λ hΛ⟩

/-- Native high-sector equivalence with the elementary low control discharged. -/
theorem canonicalHighUniformLocalBounded_iff_squarePrefixUniformLocalBounded_realized
    (Λ : ℝ) (hΛ : 0 ≤ Λ) :
    CanonicalHighUniformLocalBoundedStatement Λ ↔
      RHLean.Analysis.SquarePrefixUniformLocalBoundedStatement :=
  canonicalHighUniformLocalBounded_iff_squarePrefixUniformLocalBounded
    Λ (canonicalLowIncrementControl Λ hΛ)

/-- Native high-sector RH equivalence with the only remaining external input being
an ordinary classical Mertens/RH theorem argument. -/
theorem canonicalHighUniformLocalBounded_iff_riemannHypothesis_realized
    (Λ : ℝ) (hΛ : 0 ≤ Λ)
    (criterion : RHLean.Analysis.ClassicalMertensRHCriterion) :
    CanonicalHighUniformLocalBoundedStatement Λ ↔
      RHLean.Analysis.RiemannHypothesisStatement :=
  canonicalHighUniformLocalBounded_iff_riemannHypothesis
    Λ (canonicalLowIncrementControl Λ hΛ) criterion

end RHLean.Proof
