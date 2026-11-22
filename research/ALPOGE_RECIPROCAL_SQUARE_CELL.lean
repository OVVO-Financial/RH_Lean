import RHLean.Analysis.AlpogeGzNNSFutureTail
import RHLean.Analysis.NativePNTErdosContraction

/-! Finite reciprocal quadrature on the original signed Chebyshev future tail.
The sample uses both endpoints, but the jump sites are left-open, right-closed.
No prime-distribution or geometric estimate is used. -/

noncomputable section
open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace RHLean.Analysis

/-- Discrete summation by parts with the endpoint average retained. -/
theorem alpogeCell_midpoint_jump (E u : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b) :
    (∑ n ∈ Finset.Ico a b, E n * (u n - u (n + 1))) -
        (u a - u b) * (E a + E b) / 2 =
      ∑ n ∈ Finset.Ico a b, (E (n + 1) - E n) *
        (u (n + 1) - (u a + u b) / 2) := by
  let m := (u a + u b) / 2
  have ht : (∑ n ∈ Finset.Ico a b, (E n * (u n - u (n + 1)) -
      (E (n + 1) - E n) * (u (n + 1) - m))) =
      E b * (m - u b) - E a * (m - u a) := by
    calc
      _ = ∑ n ∈ Finset.Ico a b, (E (n + 1) * (m - u (n + 1)) -
          E n * (m - u n)) := Finset.sum_congr rfl (fun n _ => by ring)
      _ = _ := Finset.sum_Ico_sub (fun n => E n * (m - u n)) hab
  rw [Finset.sum_sub_distrib] at ht
  dsimp only [m] at ht
  linear_combination ht

def alpogeReciprocalCellKernel (a b k : ℕ) : ℝ :=
  1 / (k : ℝ) - (1 / (a : ℝ) + 1 / (b : ℝ)) / 2

def alpogeReciprocalCellSample (a b : ℕ) : ℝ :=
  (1 / (a : ℝ) - 1 / (b : ℝ)) * (nativePNTError a + nativePNTError b) / 2

def alpogeReciprocalCellJumps (a b : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico a b, (Λ (n + 1) - 1) * alpogeReciprocalCellKernel a b (n + 1)

private theorem tail_eq_cell_sum (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    alpogeGzNativeNNSTail a b =
      ∑ n ∈ Finset.Ico a b, nativePNTError n / ((n : ℝ) * (n + 1 : ℝ)) := by
  have hi (v : ℕ) (hv : 1 ≤ v) : Finset.Icc 1 (v - 1) = Finset.Ico 1 v := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [alpogeGzNativeNNSTail_eq_prefix_diff]
  unfold nativePNTWeightedErrorMass
  rw [hi b (ha.trans hab), hi a ha]
  have e := Finset.sum_Ico_consecutive
    (fun n : ℕ => nativePNTError n / ((n : ℝ) * (n + 1 : ℝ))) ha hab
  linarith only [e]

/-- The last atom at b has weight minus one half of the reciprocal width. -/
theorem alpogeNativeTail_cell_quadrature (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    alpogeGzNativeNNSTail a b - alpogeReciprocalCellSample a b =
      alpogeReciprocalCellJumps a b := by
  have he : (∑ n ∈ Finset.Ico a b, nativePNTError n *
      (1 / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ))) = alpogeGzNativeNNSTail a b := by
    rw [tail_eq_cell_sum a b ha hab]
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : 0 < n := ha.trans (Finset.mem_Ico.mp hn).1
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    push_cast
    field_simp
    ring
  have e := alpogeCell_midpoint_jump nativePNTError (fun n => 1 / (n : ℝ)) a b hab
  change (∑ n ∈ Finset.Ico a b, nativePNTError n *
    (1 / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ))) - _ = _ at e
  rw [he] at e
  simpa only [alpogeReciprocalCellSample, alpogeReciprocalCellJumps,
    alpogeReciprocalCellKernel, nativePNTError_succ_eq] using e

/-- SHELL1 on any finite block of the native square clock, including the empty block. -/
theorem alpogeNativeTail_square_quadrature (h l : ℕ) (hh : 2 ≤ h) (hl : h ≤ l) :
    alpogeGzNativeNNSTail (h ^ 2 - 1) (l ^ 2 - 1) -
        (∑ r ∈ Finset.Ico h l, alpogeReciprocalCellSample (r ^ 2 - 1) ((r + 1) ^ 2 - 1)) =
      ∑ r ∈ Finset.Ico h l, alpogeReciprocalCellJumps (r ^ 2 - 1) ((r + 1) ^ 2 - 1) := by
  have e : (∑ r ∈ Finset.Ico h l,
      (nativePNTWeightedErrorMass (((r + 1) ^ 2 - 1) - 1) -
        nativePNTWeightedErrorMass ((r ^ 2 - 1) - 1))) =
      nativePNTWeightedErrorMass ((l ^ 2 - 1) - 1) -
        nativePNTWeightedErrorMass ((h ^ 2 - 1) - 1) :=
    Finset.sum_Ico_sub (fun r : ℕ => nativePNTWeightedErrorMass ((r ^ 2 - 1) - 1)) hl
  rw [alpogeGzNativeNNSTail_eq_prefix_diff, ← e, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  have hr2 := hh.trans (Finset.mem_Ico.mp hr).1
  have hs : 4 ≤ r ^ 2 := Nat.pow_le_pow_left hr2 2
  have hm := Nat.sub_le_sub_right (Nat.pow_le_pow_left (Nat.le_succ r) 2) 1
  simpa only [alpogeGzNativeNNSTail_eq_prefix_diff] using
    alpogeNativeTail_cell_quadrature (r ^ 2 - 1) ((r + 1) ^ 2 - 1) (by omega) hm

/-- The signed kernel never vanishes at a positive integer: the exact dividing
sites straddle the harmonic mean, not the arithmetic midpoint of the cell. -/
theorem alpogeSquareCell_kernel_sign (r k : ℕ) (hr : 2 ≤ r) (hk : 0 < k) :
    (0 < alpogeReciprocalCellKernel (r ^ 2 - 1) ((r + 1) ^ 2 - 1) k ↔
      k + 2 ≤ r ^ 2 + r) ∧
    (alpogeReciprocalCellKernel (r ^ 2 - 1) ((r + 1) ^ 2 - 1) k < 0 ↔
      r ^ 2 + r ≤ k + 1) := by
  let a : ℝ := (r : ℝ) ^ 2 - 1
  let b : ℝ := (r : ℝ) ^ 2 + 2 * r
  let t : ℝ := (r : ℝ) ^ 2 + r
  let K := alpogeReciprocalCellKernel (r ^ 2 - 1) ((r + 1) ^ 2 - 1) k
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have ha : 0 < a := by dsimp [a]; nlinarith [sq_nonneg ((r : ℝ) - 1)]
  have hb : 0 < b := by dsimp [b]; nlinarith [sq_nonneg (r : ℝ)]
  have hd : 0 < 2 * a * b * (k : ℝ) := by positivity
  have hca : ((r ^ 2 - 1 : ℕ) : ℝ) = a := by
    rw [Nat.cast_sub (Nat.one_le_pow 2 r (by omega))]
    simp [a]
  have hcb : (((r + 1) ^ 2 - 1 : ℕ) : ℝ) = b := by
    rw [Nat.cast_sub (Nat.one_le_pow 2 (r + 1) (by omega))]
    simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_one, b]
    ring
  have he : 2 * a * b * (k : ℝ) * K = 2 * a * b - (a + b) * k := by
    dsimp only [K, alpogeReciprocalCellKernel]
    rw [hca, hcb]
    field_simp
    ring
  have hp : 0 < 2 * a * b - (a + b) * (t - 2) := by
    dsimp [a, b, t]
    nlinarith [sq_nonneg (r : ℝ)]
  have hn : 2 * a * b - (a + b) * (t - 1) < 0 := by
    dsimp [a, b, t]
    nlinarith [sq_nonneg (r : ℝ)]
  by_cases h : k + 2 ≤ r ^ 2 + r
  · have h' : (k : ℝ) + 2 ≤ t := by dsimp only [t]; exact_mod_cast h
    have hbnd := mul_le_mul_of_nonneg_left (show (k : ℝ) ≤ t - 2 by linarith) (add_pos ha hb).le
    have hK : 0 < K := by
      by_contra! bad
      linarith only [he, hp, hbnd, mul_nonpos_of_nonneg_of_nonpos hd.le bad]
    exact ⟨iff_of_true hK h, iff_of_false (not_lt_of_ge hK.le) (by omega)⟩
  · have h' : r ^ 2 + r ≤ k + 1 := by omega
    have hR : t ≤ (k : ℝ) + 1 := by dsimp only [t]; exact_mod_cast h'
    have hbnd := mul_le_mul_of_nonneg_left (show t - 1 ≤ (k : ℝ) by linarith) (add_pos ha hb).le
    have hK : K < 0 := by
      by_contra! bad
      linarith only [he, hn, hbnd, mul_nonneg hd.le bad]
    exact ⟨iff_of_false (not_lt_of_ge hK.le) h, iff_of_true hK h'⟩

end RHLean.Analysis

/-- info: 'RHLean.Analysis.alpogeCell_midpoint_jump' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RHLean.Analysis.alpogeCell_midpoint_jump
/-- info: 'RHLean.Analysis.alpogeNativeTail_cell_quadrature' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RHLean.Analysis.alpogeNativeTail_cell_quadrature
/-- info: 'RHLean.Analysis.alpogeNativeTail_square_quadrature' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RHLean.Analysis.alpogeNativeTail_square_quadrature
/-- info: 'RHLean.Analysis.alpogeSquareCell_kernel_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RHLean.Analysis.alpogeSquareCell_kernel_sign
