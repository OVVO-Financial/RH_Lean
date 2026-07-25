import Mathlib
import RHLean.Proof.CanonicalHighSectorBridge

/-!
# Canonical low-height occupancy

This file proves the elementary low-height clustering estimate for the native
largest-prime-factor canonical square-block decomposition and constructs the
previously abstract `CanonicalLowIncrementControl` input.

The sharp occupancy statement is made on the nonzero Möbius support and excludes
the isolated source `m = 1`. The resulting uniform increment estimate adds that
single endpoint back, giving the bound `Nat.floor Λ + 1`.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

/-! ## Largest-prime-factor pair -/

theorem canonicalLargestPrimeFactor_mem_primeFactors {m : ℕ} (h : 1 < m) :
    canonicalLargestPrimeFactor m ∈ m.primeFactors := by
  unfold canonicalLargestPrimeFactor
  rw [dif_pos h]
  exact Finset.max'_mem m.primeFactors (Nat.nonempty_primeFactors.mpr h)

theorem canonicalLargestPrimeFactor_prime {m : ℕ} (h : 1 < m) :
    (canonicalLargestPrimeFactor m).Prime :=
  (Nat.mem_primeFactors.mp (canonicalLargestPrimeFactor_mem_primeFactors h)).1

theorem canonicalLargestPrimeFactor_dvd {m : ℕ} (h : 1 < m) :
    canonicalLargestPrimeFactor m ∣ m :=
  (Nat.mem_primeFactors.mp (canonicalLargestPrimeFactor_mem_primeFactors h)).2.1

theorem canonicalCofactor_mul_largestPrimeFactor {m : ℕ} (h : 1 < m) :
    canonicalCofactor m * canonicalLargestPrimeFactor m = m := by
  unfold canonicalCofactor
  exact Nat.div_mul_cancel (canonicalLargestPrimeFactor_dvd h)

/-- The smaller canonical factor. -/
def canonicalPairLo (m : ℕ) : ℕ :=
  min (canonicalCofactor m) (canonicalLargestPrimeFactor m)

/-- The larger canonical factor. -/
def canonicalPairHi (m : ℕ) : ℕ :=
  max (canonicalCofactor m) (canonicalLargestPrimeFactor m)

theorem canonicalPairLo_le_pairHi (m : ℕ) :
    canonicalPairLo m ≤ canonicalPairHi m :=
  min_le_max

theorem canonicalPairLo_mul_pairHi {m : ℕ} (h : 1 < m) :
    canonicalPairLo m * canonicalPairHi m = m := by
  unfold canonicalPairLo canonicalPairHi
  rcases le_total (canonicalCofactor m) (canonicalLargestPrimeFactor m) with hle | hle
  · rw [min_eq_left hle, max_eq_right hle]
    exact canonicalCofactor_mul_largestPrimeFactor h
  · rw [min_eq_right hle, max_eq_left hle, mul_comm]
    exact canonicalCofactor_mul_largestPrimeFactor h

/-- The absolute gap between the two canonical factors. -/
def canonicalAbsoluteGap (m : ℕ) : ℕ :=
  canonicalPairHi m - canonicalPairLo m

theorem canonicalPairLo_add_absoluteGap (m : ℕ) :
    canonicalPairLo m + canonicalAbsoluteGap m = canonicalPairHi m := by
  unfold canonicalAbsoluteGap
  omega

/-! ## Product spacing at fixed positive gap -/

/-- If `j^2 ≤ r(r+d)`, then the factor sum `2r+d` is at least `2j`. -/
theorem two_mul_le_of_sq_le_gapProduct
    (r d j : ℕ) (h : j ^ 2 ≤ r * (r + d)) :
    2 * j ≤ 2 * r + d := by
  by_contra hcontra
  have hstrict : 2 * r + d < 2 * j := by omega
  have hsquare : (2 * r + d) ^ 2 < (2 * j) ^ 2 :=
    Nat.pow_lt_pow_left hstrict (by omega)
  have hidentity : (2 * r + d) ^ 2 = 4 * (r * (r + d)) + d ^ 2 := by
    ring
  have hjsquare : (2 * j) ^ 2 = 4 * j ^ 2 := by
    ring
  nlinarith

/-- In one square block, a fixed canonical absolute gap determines at most one
source greater than one. -/
theorem eq_of_canonicalAbsoluteGap_eq_in_block
    {j d m m' : ℕ}
    (hm : m ∈ canonicalSquareBlock j)
    (hm' : m' ∈ canonicalSquareBlock j)
    (hm1 : 1 < m)
    (hm'1 : 1 < m')
    (hgap : canonicalAbsoluteGap m = d)
    (hgap' : canonicalAbsoluteGap m' = d) :
    m = m' := by
  have hprod := canonicalPairLo_mul_pairHi hm1
  have hprod' := canonicalPairLo_mul_pairHi hm'1
  have hHiLo : canonicalPairLo m + d = canonicalPairHi m := by
    simpa [hgap] using canonicalPairLo_add_absoluteGap m
  have hHiLo' : canonicalPairLo m' + d = canonicalPairHi m' := by
    simpa [hgap'] using canonicalPairLo_add_absoluteGap m'
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
    have hfactorSum :=
      two_mul_le_of_sq_le_gapProduct (canonicalPairLo m) d j hjr
    have hstep :
        canonicalPairLo m * (canonicalPairLo m + d) + (2 * j + 1) ≤
          canonicalPairLo m' * (canonicalPairLo m' + d) := by
      have hloSucc : canonicalPairLo m + 1 ≤ canonicalPairLo m' := by omega
      have hmono :
          (canonicalPairLo m + 1) * (canonicalPairLo m + 1 + d) ≤
            canonicalPairLo m' * (canonicalPairLo m' + d) := by
        exact Nat.mul_le_mul hloSucc (by omega)
      have hexpand :
          (canonicalPairLo m + 1) * (canonicalPairLo m + 1 + d) =
            canonicalPairLo m * (canonicalPairLo m + d) +
              (2 * canonicalPairLo m + d + 1) := by
        ring
      rw [hexpand] at hmono
      omega
    have hblockWidth : j ^ 2 + (2 * j + 1) = (j + 1) ^ 2 := by
      ring
    rw [← hm'eq] at hstep
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
    have hfactorSum :=
      two_mul_le_of_sq_le_gapProduct (canonicalPairLo m') d j hjr
    have hstep :
        canonicalPairLo m' * (canonicalPairLo m' + d) + (2 * j + 1) ≤
          canonicalPairLo m * (canonicalPairLo m + d) := by
      have hloSucc : canonicalPairLo m' + 1 ≤ canonicalPairLo m := by omega
      have hmono :
          (canonicalPairLo m' + 1) * (canonicalPairLo m' + 1 + d) ≤
            canonicalPairLo m * (canonicalPairLo m + d) := by
        exact Nat.mul_le_mul hloSucc (by omega)
      have hexpand :
          (canonicalPairLo m' + 1) * (canonicalPairLo m' + 1 + d) =
            canonicalPairLo m' * (canonicalPairLo m' + d) +
              (2 * canonicalPairLo m' + d + 1) := by
        ring
      rw [hexpand] at hmono
      omega
    have hblockWidth : j ^ 2 + (2 * j + 1) = (j + 1) ^ 2 := by
      ring
    rw [← hmeq] at hstep
    omega

/-! ## Height versus factor gap -/

theorem abs_canonicalHeightTwice_eq_gap_mul_factorSum {m : ℕ} (h : 1 < m) :
    |canonicalHeightTwice m| =
      (canonicalAbsoluteGap m : ℝ) *
        ((canonicalPairLo m : ℝ) + (canonicalPairHi m : ℝ)) := by
  unfold canonicalHeightTwice canonicalAbsoluteGap canonicalPairLo canonicalPairHi
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

/-- Nonzero Möbius weight excludes zero canonical gap away from `m = 1`. -/
theorem canonicalAbsoluteGap_pos_of_moebius_ne_zero
    {m : ℕ} (hm1 : 1 < m) (hμ : μ m ≠ 0) :
    0 < canonicalAbsoluteGap m := by
  have hsquarefree : Squarefree m :=
    ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hμ
  have hprime := canonicalLargestPrimeFactor_prime hm1
  by_contra hgap
  have hgap0 : canonicalAbsoluteGap m = 0 := by omega
  have hpairEq : canonicalPairHi m = canonicalPairLo m := by
    have hle := canonicalPairLo_le_pairHi m
    unfold canonicalAbsoluteGap at hgap0
    omega
  have hcofactorEq : canonicalCofactor m = canonicalLargestPrimeFactor m := by
    unfold canonicalPairLo canonicalPairHi at hpairEq
    rcases le_total (canonicalCofactor m) (canonicalLargestPrimeFactor m) with hle | hle
    · rw [min_eq_left hle, max_eq_right hle] at hpairEq
      exact hpairEq.symm
    · rw [min_eq_right hle, max_eq_left hle] at hpairEq
      exact hpairEq
  have hnotSquareDvd :
      ¬ canonicalLargestPrimeFactor m * canonicalLargestPrimeFactor m ∣ m :=
    (Nat.squarefree_iff_prime_squarefree.mp hsquarefree)
      (canonicalLargestPrimeFactor m) hprime
  apply hnotSquareDvd
  rw [← canonicalCofactor_mul_largestPrimeFactor hm1, hcofactorEq]

/-- Low height in block `j` forces the absolute canonical gap to be at most
`Λ`. -/
theorem canonicalAbsoluteGap_le_of_lowHeight
    {Λ : ℝ} {j m : ℕ}
    (hj : 1 ≤ j)
    (hm : m ∈ canonicalSquareBlock j)
    (hm1 : 1 < m)
    (hlow : IsCanonicalLowHeight Λ j m) :
    (canonicalAbsoluteGap m : ℝ) ≤ Λ := by
  have hjm : j ^ 2 ≤ m := by
    simpa [canonicalSquareBlock, Finset.mem_Ico] using hm.1
  have hprod := canonicalPairLo_mul_pairHi hm1
  have hHiLo := canonicalPairLo_add_absoluteGap m
  have hjgapProduct :
      j ^ 2 ≤ canonicalPairLo m * (canonicalPairLo m + canonicalAbsoluteGap m) := by
    rw [hHiLo, hprod]
    exact hjm
  have hfactorSumNat :=
    two_mul_le_of_sq_le_gapProduct
      (canonicalPairLo m) (canonicalAbsoluteGap m) j hjgapProduct
  have hfactorSum :
      2 * (j : ℝ) ≤ (canonicalPairLo m : ℝ) + (canonicalPairHi m : ℝ) := by
    exact_mod_cast hfactorSumNat
  have hheight := abs_canonicalHeightTwice_eq_gap_mul_factorSum hm1
  have hcutoff : |canonicalHeightTwice m| ≤ 2 * Λ * (j : ℝ) := hlow
  have hjpos : 0 < (j : ℝ) := by exact_mod_cast hj
  have hgapNonneg : 0 ≤ (canonicalAbsoluteGap m : ℝ) := by positivity
  nlinarith

/-! ## Sharp nontrivial occupancy -/

/-- Nontrivial, nonzero-Möbius canonical low-height support in block `j`. -/
def canonicalNontrivialLowSupport (Λ : ℝ) (j : ℕ) : Finset ℕ :=
  (canonicalSquareBlock j).filter fun m =>
    1 < m ∧ μ m ≠ 0 ∧ IsCanonicalLowHeight Λ j m

/-- On the nonzero Möbius support and away from `m = 1`, the number of low-height
sources in a square block is at most `floor Λ`. -/
theorem card_canonicalNontrivialLowSupport_le_floor
    {Λ : ℝ} (hΛ : 0 ≤ Λ) {j : ℕ} (hj : 1 ≤ j) :
    (canonicalNontrivialLowSupport Λ j).card ≤ Nat.floor Λ := by
  classical
  have hinj : Set.InjOn canonicalAbsoluteGap ↑(canonicalNontrivialLowSupport Λ j) := by
    intro m hm m' hm' hgap
    simp only [canonicalNontrivialLowSupport, Finset.mem_filter] at hm hm'
    exact eq_of_canonicalAbsoluteGap_eq_in_block
      hm.1 hm'.1 hm.2.1 hm'.2.1 hgap rfl
  have hrange :
      (canonicalNontrivialLowSupport Λ j).image canonicalAbsoluteGap ⊆
        Finset.Icc 1 (Nat.floor Λ) := by
    intro d hd
    simp only [Finset.mem_image] at hd
    rcases hd with ⟨m, hm, rfl⟩
    simp only [canonicalNontrivialLowSupport, Finset.mem_filter] at hm
    have hgapPos := canonicalAbsoluteGap_pos_of_moebius_ne_zero hm.2.1 hm.2.2.1
    have hgapLeReal :=
      canonicalAbsoluteGap_le_of_lowHeight hj hm.1 hm.2.1 hm.2.2.2
    have hgapLeFloor : canonicalAbsoluteGap m ≤ Nat.floor Λ :=
      Nat.le_floor hgapLeReal
    exact Finset.mem_Icc.mpr ⟨hgapPos, hgapLeFloor⟩
  calc
    (canonicalNontrivialLowSupport Λ j).card =
        ((canonicalNontrivialLowSupport Λ j).image canonicalAbsoluteGap).card := by
      exact (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.Icc 1 (Nat.floor Λ)).card := Finset.card_le_card hrange
    _ ≤ Nat.floor Λ := by simp

/-! ## Uniform low-increment control -/

/-- All low-height terms with nonzero Möbius weight. -/
def canonicalLowSupport (Λ : ℝ) (j : ℕ) : Finset ℕ :=
  (canonicalSquareBlock j).filter fun m =>
    μ m ≠ 0 ∧ IsCanonicalLowHeight Λ j m

theorem card_canonicalLowSupport_le_floor_add_one
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (j : ℕ) :
    (canonicalLowSupport Λ j).card ≤ Nat.floor Λ + 1 := by
  classical
  by_cases hj : 1 ≤ j
  · have hsubset :
        canonicalLowSupport Λ j ⊆ canonicalNontrivialLowSupport Λ j ∪ {1} := by
      intro m hm
      simp only [canonicalLowSupport, Finset.mem_filter] at hm
      by_cases hm1 : 1 < m
      · apply Finset.mem_union_left
        exact Finset.mem_filter.mpr ⟨hm.1, hm1, hm.2.1, hm.2.2⟩
      · apply Finset.mem_union_right
        have hmLower : j ^ 2 ≤ m := by
          simpa [canonicalSquareBlock, Finset.mem_Ico] using hm.1.1
        have hjSquare : 1 ≤ j ^ 2 := by positivity
        have hmEq : m = 1 := by omega
        simp [hmEq]
    calc
      (canonicalLowSupport Λ j).card ≤
          (canonicalNontrivialLowSupport Λ j ∪ {1}).card :=
        Finset.card_le_card hsubset
      _ ≤ (canonicalNontrivialLowSupport Λ j).card + 1 := by
        simpa using Finset.card_union_le (canonicalNontrivialLowSupport Λ j) {1}
      _ ≤ Nat.floor Λ + 1 := by
        exact Nat.add_le_add_right
          (card_canonicalNontrivialLowSupport_le_floor hΛ hj) 1
  · have hj0 : j = 0 := by omega
    subst j
    have hsupportEmpty : canonicalLowSupport Λ 0 = ∅ := by
      ext m
      simp [canonicalLowSupport, canonicalSquareBlock, canonicalMoebiusWeight]
    simp [hsupportEmpty]

/-- Every canonical Möbius weight has complex norm at most one. -/
theorem norm_canonicalMoebiusWeight_le_one (m : ℕ) :
    ‖canonicalMoebiusWeight m‖ ≤ 1 := by
  rcases ArithmeticFunction.moebius_eq_or m with h | h | h <;>
    simp [canonicalMoebiusWeight, h]

/-- The canonical low increment is bounded uniformly by `floor Λ + 1`. -/
theorem norm_canonicalLowIncrement_le_floor_add_one
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (j : ℕ) :
    ‖canonicalLowIncrement Λ j‖ ≤ (Nat.floor Λ : ℝ) + 1 := by
  classical
  unfold canonicalLowIncrement
  calc
    ‖∑ m ∈ canonicalSquareBlock j,
        if IsCanonicalLowHeight Λ j m then canonicalMoebiusWeight m else 0‖ ≤
        ∑ m ∈ canonicalSquareBlock j,
          ‖if IsCanonicalLowHeight Λ j m then canonicalMoebiusWeight m else 0‖ :=
      norm_sum_le _ _
    _ ≤ ∑ m ∈ canonicalSquareBlock j,
        if μ m ≠ 0 ∧ IsCanonicalLowHeight Λ j m then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro m hm
      by_cases hμ : μ m = 0
      · simp [hμ, canonicalMoebiusWeight]
      · by_cases hlow : IsCanonicalLowHeight Λ j m
        · simpa [hμ, hlow] using norm_canonicalMoebiusWeight_le_one m
        · simp [hlow]
    _ = (canonicalLowSupport Λ j).card := by
      simp [canonicalLowSupport]
    _ ≤ Nat.floor Λ + 1 := by
      exact_mod_cast card_canonicalLowSupport_le_floor_add_one hΛ j
    _ = (Nat.floor Λ : ℝ) + 1 := by norm_num

/-- Unconditional realization of the canonical low-increment control for every
nonnegative cutoff. -/
noncomputable def canonicalLowIncrementControl
    (Λ : ℝ) (hΛ : 0 ≤ Λ) : CanonicalLowIncrementControl Λ where
  bound := (Nat.floor Λ : ℝ) + 1
  bound_nonneg := by positivity
  norm_increment_le := norm_canonicalLowIncrement_le_floor_add_one hΛ

/-- The native canonical high-sector criterion is equivalent to the protected
square-prefix uniform-local criterion without any remaining low-sector
hypothesis. -/
theorem canonicalHighUniformLocalBounded_iff_squarePrefixUniformLocalBounded_realized
    (Λ : ℝ) (hΛ : 0 ≤ Λ) :
    CanonicalHighUniformLocalBoundedStatement Λ ↔
      RHLean.Analysis.SquarePrefixUniformLocalBoundedStatement :=
  canonicalHighUniformLocalBounded_iff_squarePrefixUniformLocalBounded
    Λ (canonicalLowIncrementControl Λ hΛ)

/-- With the ordinary classical Mertens criterion supplied as a theorem
argument, the canonical high-sector statement is equivalent to RH, with the
low-sector obligation now discharged internally. -/
theorem canonicalHighUniformLocalBounded_iff_riemannHypothesis_realized
    (Λ : ℝ) (hΛ : 0 ≤ Λ)
    (criterion : RHLean.Analysis.ClassicalMertensRHCriterion) :
    CanonicalHighUniformLocalBoundedStatement Λ ↔
      RHLean.Analysis.RiemannHypothesisStatement :=
  canonicalHighUniformLocalBounded_iff_riemannHypothesis
    Λ (canonicalLowIncrementControl Λ hΛ) criterion

end RHLean.Proof
