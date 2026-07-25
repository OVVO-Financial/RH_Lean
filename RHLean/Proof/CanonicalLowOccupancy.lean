import Mathlib
import RHLean.Proof.CanonicalHighSectorBridge

/-!
# The elementary canonical low-height occupancy bound

This file gives an unconditional construction of
`RHLean.Proof.CanonicalLowIncrementControl Λ` (previously an unproved
hypothesis everywhere it was used), matching the manuscript's
"Low-height clustering in square blocks" section.

STATUS: this file has not been compiled against mathlib in the
environment that produced it (no local Lean/mathlib toolchain was
available). It follows the tactic patterns already verified elsewhere
in this repository (`nlinarith` with explicit `ring`-expanded hints,
`omega` for linear Nat facts, `exact_mod_cast`), but it has not been
checked by `lake build` and should be treated as a draft pending that
check. The highest-risk step is `two_mul_le_of_sq_le_mul`, the one
place a genuine AM-GM-style nonlinear inequality is used.

Mathematical content: for canonical source `m > 1` write its two
canonical factors in sorted order `(canonicalPairLo m, canonicalPairHi
m)`. Within a fixed square block `j`, at most one `m` can realize any
fixed positive factor gap `d = canonicalPairHi m - canonicalPairLo m`,
because consecutive values of `r ↦ r*(r+d)` grow faster than the block
diameter once `r*(r+d)` is already at least `j^2`. Combined with the
AM-GM bound `canonicalPairLo m + canonicalPairHi m ≥ 2j`, this forces
`d` (hence the occupancy) into a range of length `⌊Λ⌋` at height cutoff
`Λ * j`. Two small correction terms (the source `m = 1`, and the single
possible perfect-square source with gap `0`) are added by hand,
avoiding the need to filter by squarefreeness.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

/-! ### Basic facts about the canonical largest-prime-factor pair -/

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

theorem canonicalCofactor_mul {m : ℕ} (h : 1 < m) :
    canonicalCofactor m * canonicalLargestPrimeFactor m = m := by
  unfold canonicalCofactor
  exact Nat.div_mul_cancel (canonicalLargestPrimeFactor_dvd h)

theorem canonicalCofactor_pos {m : ℕ} (h : 1 < m) : 0 < canonicalCofactor m := by
  rcases Nat.eq_zero_or_pos (canonicalCofactor m) with h0 | h0
  · exfalso
    have hmul := canonicalCofactor_mul h
    rw [h0, zero_mul] at hmul
    omega
  · exact h0

/-! ### The sorted factor pair and its gap -/

/-- The smaller of the two canonical factors. -/
def canonicalPairLo (m : ℕ) : ℕ := min (canonicalCofactor m) (canonicalLargestPrimeFactor m)

/-- The larger of the two canonical factors. -/
def canonicalPairHi (m : ℕ) : ℕ := max (canonicalCofactor m) (canonicalLargestPrimeFactor m)

theorem canonicalPairLo_le_Hi (m : ℕ) : canonicalPairLo m ≤ canonicalPairHi m :=
  min_le_max

theorem canonicalPair_mul {m : ℕ} (h : 1 < m) :
    canonicalPairLo m * canonicalPairHi m = m := by
  unfold canonicalPairLo canonicalPairHi
  rcases le_total (canonicalCofactor m) (canonicalLargestPrimeFactor m) with hle | hle
  · rw [min_eq_left hle, max_eq_right hle]
    exact canonicalCofactor_mul h
  · rw [min_eq_right hle, max_eq_left hle, mul_comm]
    exact canonicalCofactor_mul h

/-- The absolute canonical factor gap. -/
def canonicalGap (m : ℕ) : ℕ := canonicalPairHi m - canonicalPairLo m

theorem canonicalPairLo_add_gap (m : ℕ) :
    canonicalPairLo m + canonicalGap m = canonicalPairHi m := by
  have h := canonicalPairLo_le_Hi m
  unfold canonicalGap
  omega

/-! ### Growth lemma: the AM-GM-style step -/

/-- If `r*(r+d) ≥ j^2` then `2r+d ≥ 2j`. This is the only genuinely
nonlinear step in the whole occupancy argument. -/
theorem two_mul_le_of_sq_le_mul (r d j : ℕ) (h : j ^ 2 ≤ r * (r + d)) :
    2 * j ≤ 2 * r + d := by
  by_contra hc
  push_neg at hc
  have hc' : 2 * r + d + 1 ≤ 2 * j := hc
  have hsq : (2 * r + d + 1) ^ 2 ≤ (2 * j) ^ 2 := Nat.pow_le_pow_left hc' 2
  have hexpand : (2 * r + d + 1) ^ 2 = 4 * (r * (r + d)) + (d + 1) ^ 2 + 4 * r := by ring
  have hexpand2 : (2 * j) ^ 2 = 4 * j ^ 2 := by ring
  have hpos : 1 ≤ (d + 1) ^ 2 := Nat.one_le_pow 2 (d + 1) (by omega)
  nlinarith [h, hsq, hexpand, hexpand2, hpos]

/-! ### At most one source per positive gap, per block -/

/-- Within a fixed square block, at most one canonical source `m > 1`
realizes any fixed positive factor gap `d`. -/
theorem eq_of_canonicalGap_eq_in_block
    {j d : ℕ} {m m' : ℕ}
    (hm : m ∈ canonicalSquareBlock j) (hm' : m' ∈ canonicalSquareBlock j)
    (hm1 : 1 < m) (hm'1 : 1 < m')
    (hgap : canonicalGap m = d) (hgap' : canonicalGap m' = d) :
    m = m' := by
  have hprod := canonicalPair_mul hm1
  have hprod' := canonicalPair_mul hm'1
  have hHiLo : canonicalPairLo m + d = canonicalPairHi m := by
    have h0 := canonicalPairLo_add_gap m; rwa [hgap] at h0
  have hHiLo' : canonicalPairLo m' + d = canonicalPairHi m' := by
    have h0 := canonicalPairLo_add_gap m'; rwa [hgap'] at h0
  have hjm : j ^ 2 ≤ m ∧ m < (j + 1) ^ 2 := by
    simpa [canonicalSquareBlock, Finset.mem_Ico] using hm
  have hjm' : j ^ 2 ≤ m' ∧ m' < (j + 1) ^ 2 := by
    simpa [canonicalSquareBlock, Finset.mem_Ico] using hm'
  rcases lt_trichotomy (canonicalPairLo m) (canonicalPairLo m') with hlt | heq | hlt
  · exfalso
    have hmeq : m = canonicalPairLo m * (canonicalPairLo m + d) := by
      rw [hHiLo]; exact hprod.symm
    have hm'eq : m' = canonicalPairLo m' * (canonicalPairLo m' + d) := by
      rw [hHiLo']; exact hprod'.symm
    have hjr : j ^ 2 ≤ canonicalPairLo m * (canonicalPairLo m + d) := by
      rw [← hmeq]; exact hjm.1
    have hkey := two_mul_le_of_sq_le_mul (canonicalPairLo m) d j hjr
    have hrr' : canonicalPairLo m + 1 ≤ canonicalPairLo m' := hlt
    have hgrow : canonicalPairLo m' * (canonicalPairLo m' + d) ≥
        canonicalPairLo m * (canonicalPairLo m + d) + (2 * canonicalPairLo m + d + 1) := by
      have hmono : (canonicalPairLo m + 1) * (canonicalPairLo m + 1 + d) ≤
          canonicalPairLo m' * (canonicalPairLo m' + d) := by
        apply Nat.mul_le_mul hrr'
        omega
      have hexp : (canonicalPairLo m + 1) * (canonicalPairLo m + 1 + d) =
          canonicalPairLo m * (canonicalPairLo m + d) +
            (2 * canonicalPairLo m + d + 1) := by ring
      omega
    have hfinal : m' ≥ j ^ 2 + (2 * j + 1) := by
      rw [hm'eq]
      omega
    have hsq : j ^ 2 + (2 * j + 1) = (j + 1) ^ 2 := by ring
    omega
  · have hhi : canonicalPairHi m = canonicalPairHi m' := by omega
    rw [← hprod, ← hprod', heq, hhi]
  · exfalso
    have hmeq : m = canonicalPairLo m * (canonicalPairLo m + d) := by
      rw [hHiLo]; exact hprod.symm
    have hm'eq : m' = canonicalPairLo m' * (canonicalPairLo m' + d) := by
      rw [hHiLo']; exact hprod'.symm
    have hjr : j ^ 2 ≤ canonicalPairLo m' * (canonicalPairLo m' + d) := by
      rw [← hm'eq]; exact hjm'.1
    have hkey := two_mul_le_of_sq_le_mul (canonicalPairLo m') d j hjr
    have hrr' : canonicalPairLo m' + 1 ≤ canonicalPairLo m := hlt
    have hgrow : canonicalPairLo m * (canonicalPairLo m + d) ≥
        canonicalPairLo m' * (canonicalPairLo m' + d) + (2 * canonicalPairLo m' + d + 1) := by
      have hmono : (canonicalPairLo m' + 1) * (canonicalPairLo m' + 1 + d) ≤
          canonicalPairLo m * (canonicalPairLo m + d) := by
        apply Nat.mul_le_mul hrr'
        omega
      have hexp : (canonicalPairLo m' + 1) * (canonicalPairLo m' + 1 + d) =
          canonicalPairLo m' * (canonicalPairLo m' + d) +
            (2 * canonicalPairLo m' + d + 1) := by ring
      omega
    have hfinal : m ≥ j ^ 2 + (2 * j + 1) := by
      rw [hmeq]
      omega
    have hsq : j ^ 2 + (2 * j + 1) = (j + 1) ^ 2 := by ring
    omega

/-! ### Relating the gap to the height -/

/-- `|2Y_m|` equals `2 * gap * (Lo+Hi)`, matching the manuscript's
`|Y| = d(c+q)/2`. -/
theorem abs_canonicalHeightTwice_eq {m : ℕ} (h : 1 < m) :
    |canonicalHeightTwice m| =
      (canonicalGap m : ℝ) * ((canonicalPairLo m : ℝ) + (canonicalPairHi m : ℝ)) := by
  unfold canonicalHeightTwice
  have hle := canonicalPairLo_le_Hi m
  have hcast : ((canonicalGap m : ℕ) : ℝ) =
      (canonicalPairHi m : ℝ) - (canonicalPairLo m : ℝ) := by
    unfold canonicalGap
    exact_mod_cast Nat.cast_sub hle
  rw [hcast]
  rcases le_total (canonicalCofactor m) (canonicalLargestPrimeFactor m) with hle2 | hle2
  · have hlo : canonicalPairLo m = canonicalCofactor m := min_eq_left hle2
    have hhi : canonicalPairHi m = canonicalLargestPrimeFactor m := max_eq_right hle2
    rw [hlo, hhi]
    have hnn : (canonicalCofactor m : ℝ) ≤ (canonicalLargestPrimeFactor m : ℝ) := by
      exact_mod_cast hle2
    rw [abs_of_nonpos (by linarith)]
    ring
  · have hlo : canonicalPairLo m = canonicalLargestPrimeFactor m := min_eq_right hle2
    have hhi : canonicalPairHi m = canonicalCofactor m := max_eq_left hle2
    rw [hlo, hhi]
    have hnn : (canonicalLargestPrimeFactor m : ℝ) ≤ (canonicalCofactor m : ℝ) := by
      exact_mod_cast hle2
    rw [abs_of_nonneg (by linarith)]
    ring

/-- Low height with `m > 1` forces a real gap bound `canonicalGap m ≤ Λ`
(as reals), via the AM-GM bound `Lo+Hi ≥ 2j` for `j ≥ 1`. -/
theorem canonicalGap_le_of_lowHeight {Λ : ℝ} {j m : ℕ} (hj : 1 ≤ j)
    (hm : m ∈ canonicalSquareBlock j) (h1 : 1 < m)
    (hlow : IsCanonicalLowHeight Λ j m) :
    (canonicalGap m : ℝ) ≤ Λ := by
  have hjm : j ^ 2 ≤ m := by
    have := hm; simpa [canonicalSquareBlock, Finset.mem_Ico] using this.1
  have hprod : canonicalPairLo m * canonicalPairHi m = m := canonicalPair_mul h1
  have hHiLo : canonicalPairLo m + canonicalGap m = canonicalPairHi m :=
    canonicalPairLo_add_gap m
  have hjr : j ^ 2 ≤ canonicalPairLo m * (canonicalPairLo m + canonicalGap m) := by
    rw [hHiLo]; rw [hprod] at hjm ⊢; exact hjm
  have hkey := two_mul_le_of_sq_le_mul (canonicalPairLo m) (canonicalGap m) j hjr
  have hsumR : (2 : ℝ) * j ≤ (canonicalPairLo m : ℝ) + (canonicalPairHi m : ℝ) := by
    have : 2 * j ≤ canonicalPairLo m + canonicalPairHi m := by
      rw [← hHiLo]; omega
    exact_mod_cast this
  have habs : |canonicalHeightTwice m| =
      (canonicalGap m : ℝ) * ((canonicalPairLo m : ℝ) + (canonicalPairHi m : ℝ)) :=
    abs_canonicalHeightTwice_eq h1
  have hle : |canonicalHeightTwice m| ≤ 2 * Λ * (j : ℝ) := hlow
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj
  have hprodpos : (0:ℝ) < (canonicalPairLo m : ℝ) + (canonicalPairHi m : ℝ) := by linarith
  nlinarith [habs, hle, hsumR, hjpos, hprodpos]

/-! ### Occupancy bound -/

/-- The `m > 1` low-height sources in block `j` inject into
`Finset.Icc 0 ⌊Λ⌋₊`, via `m ↦ canonicalGap m`. -/
theorem canonicalGap_injOn_lowHeight {Λ : ℝ} {j : ℕ} (hj : 1 ≤ j) :
    Set.InjOn canonicalGap
      {m ∈ canonicalSquareBlock j | 1 < m ∧ IsCanonicalLowHeight Λ j m} := by
  intro m hm m' hm' hgapeq
  simp only [Set.mem_setOf_eq] at hm hm'
  exact eq_of_canonicalGap_eq_in_block hm.1 hm'.1 hm.2.1 hm'.2.1 hgapeq rfl

/-- Occupancy bound: the number of `m > 1` low-height sources in block
`j` (for `j ≥ 1`) is at most `⌊Λ⌋₊ + 1`. -/
theorem card_lowHeight_le {Λ : ℝ} {j : ℕ} (hj : 1 ≤ j) :
    (canonicalSquareBlock j |>.filter
        (fun m => 1 < m ∧ IsCanonicalLowHeight Λ j m)).card ≤ Nat.floor Λ + 1 := by
  classical
  have hsub :
      (canonicalSquareBlock j |>.filter
          (fun m => 1 < m ∧ IsCanonicalLowHeight Λ j m)).image canonicalGap ⊆
        Finset.Icc 0 (Nat.floor Λ) := by
    intro d hd
    simp only [Finset.mem_image, Finset.mem_filter] at hd
    obtain ⟨m, ⟨hmem, h1, hlow⟩, hd⟩ := hd
    have hbound := canonicalGap_le_of_lowHeight (Λ := Λ) hj hmem h1 hlow
    rw [← hd] at hbound
    simp only [Finset.mem_Icc]
    exact ⟨Nat.zero_le _, Nat.le_floor hbound⟩
  have hinj : Set.InjOn canonicalGap
      ↑(canonicalSquareBlock j |>.filter
          (fun m => 1 < m ∧ IsCanonicalLowHeight Λ j m)) := by
    intro m hm m' hm' hgapeq
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hm hm'
    exact eq_of_canonicalGap_eq_in_block hm.1 hm'.1 hm.2.1 hm'.2.1 hgapeq rfl
  calc
    (canonicalSquareBlock j |>.filter
        (fun m => 1 < m ∧ IsCanonicalLowHeight Λ j m)).card =
        ((canonicalSquareBlock j |>.filter
            (fun m => 1 < m ∧ IsCanonicalLowHeight Λ j m)).image canonicalGap).card := by
      rw [Finset.card_image_of_injOn hinj]
    _ ≤ (Finset.Icc 0 (Nat.floor Λ)).card := Finset.card_le_card hsub
    _ = Nat.floor Λ + 1 := by simp

/-! ### Assembling the uniform control -/

/-- Unconditional construction of `CanonicalLowIncrementControl`. -/
noncomputable def canonicalLowIncrementControl (Λ : ℝ) : CanonicalLowIncrementControl Λ where
  bound := (Nat.floor Λ : ℝ) + 2
  bound_nonneg := by positivity
  norm_increment_le := by
    intro j
    unfold canonicalLowIncrement
    classical
    by_cases hj : 1 ≤ j
    · have hcard := card_lowHeight_le (Λ := Λ) hj
      calc
        ‖∑ m ∈ canonicalSquareBlock j,
            if IsCanonicalLowHeight Λ j m then canonicalMoebiusWeight m else 0‖
            ≤ ∑ m ∈ canonicalSquareBlock j,
                ‖if IsCanonicalLowHeight Λ j m then canonicalMoebiusWeight m else 0‖ :=
          norm_sum_le _ _
        _ = ∑ m ∈ (canonicalSquareBlock j).filter (fun m => IsCanonicalLowHeight Λ j m),
              ‖canonicalMoebiusWeight m‖ := by
          rw [Finset.sum_filter]
          congr 1
          funext m
          split_ifs <;> simp
        _ ≤ ∑ _m ∈ (canonicalSquareBlock j).filter (fun m => IsCanonicalLowHeight Λ j m), (1:ℝ) := by
          apply Finset.sum_le_sum
          intro m _
          unfold canonicalMoebiusWeight
          rcases ArithmeticFunction.moebius_eq_or m with h | h | h <;> simp [h]
        _ = ((canonicalSquareBlock j).filter (fun m => IsCanonicalLowHeight Λ j m)).card := by
          simp
        _ ≤ ((canonicalSquareBlock j).filter
              (fun m => 1 < m ∧ IsCanonicalLowHeight Λ j m)).card + 1 := by
          have hsplit :
              (canonicalSquareBlock j).filter (fun m => IsCanonicalLowHeight Λ j m) ⊆
                ((canonicalSquareBlock j).filter
                    (fun m => 1 < m ∧ IsCanonicalLowHeight Λ j m)) ∪ {1} := by
            intro m hm
            simp only [Finset.mem_filter] at hm
            by_cases hm1 : 1 < m
            · left; simp [Finset.mem_filter, hm.1, hm1, hm.2]
            · right
              have hm_le1 : m ≤ 1 := by omega
              have hm_ge : j ^ 2 ≤ m := by
                have hblk := hm.1
                simpa [canonicalSquareBlock, Finset.mem_Ico] using hblk
              have hjpos : 1 ≤ j ^ 2 := Nat.one_le_pow 2 j (by omega)
              have hm0 : 0 < m := by omega
              simp only [Finset.mem_singleton]
              omega
          calc
            ((canonicalSquareBlock j).filter (fun m => IsCanonicalLowHeight Λ j m)).card ≤
                (((canonicalSquareBlock j).filter
                    (fun m => 1 < m ∧ IsCanonicalLowHeight Λ j m)) ∪ {1}).card :=
              Finset.card_le_card hsplit
            _ ≤ ((canonicalSquareBlock j).filter
                    (fun m => 1 < m ∧ IsCanonicalLowHeight Λ j m)).card + 1 :=
              (Finset.card_union_le _ _).trans (by simp)
        _ ≤ (Nat.floor Λ + 1) + 1 := by exact_mod_cast Nat.add_le_add_right hcard 1
        _ = (Nat.floor Λ : ℝ) + 2 := by push_cast; ring
    · have hj0 : j = 0 := by omega
      subst hj0
      have hblock : canonicalSquareBlock 0 = {0} := by
        unfold canonicalSquareBlock
        ext x
        simp only [Finset.mem_Ico, Finset.mem_singleton]
        omega
      rw [hblock, Finset.sum_singleton]
      have hmu0 : canonicalMoebiusWeight 0 = 0 := by
        unfold canonicalMoebiusWeight; simp
      by_cases h0 : IsCanonicalLowHeight Λ 0 0
      · simp [h0, hmu0]
      · simp [h0]

end RHLean.Proof
