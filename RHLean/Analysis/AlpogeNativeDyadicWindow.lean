import RHLean.Analysis.AlpogeSquareClockSignedHistorySampling

/-!
# An exact dyadic window for the native signed source

This module derives a finite prime-power identity directly from `nativeAlpogeGz`.
The combination `-G(4N) + 3G(2N) - 2G(N)` cancels every coefficient at or below `N`
and the affine centering term. Its remaining arithmetic source is the genuine
von Mangoldt sum on the open interval `(N, 4N)`, with a piecewise rational weight.
The weight is zero at the exterior endpoints and one at `2N` for positive `N`.

This is an exact change of source coordinates. It provides no bound for the
remaining signed deficit and does not replace the native square-clock target.
The proof uses finite sums and elementary logarithmic identities only.
-/

noncomputable section

open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

/-- The compact dyadic weight, including its exact integer endpoints. -/
def nativeAlpogeDyadicWindowWeight (N n : ℕ) : ℝ :=
  if n ≤ N then 0
  else if n ≤ 2 * N then 2 * (1 - (N : ℝ) / (n : ℝ))
  else if n < 4 * N then 4 * (N : ℝ) / (n : ℝ) - 1
  else 0

/-- Every von Mangoldt prime power in the open dyadic window is retained. -/
def nativeAlpogeDyadicPrimePowerWindow (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioo N (4 * N), Λ n * nativeAlpogeDyadicWindowWeight N n

/-- The three-scale difference of the complete original signed source. -/
def nativeAlpogeDyadicDifference (N : ℕ) : ℝ :=
  -nativeAlpogeGz (4 * N) + 3 * nativeAlpogeGz (2 * N) -
    2 * nativeAlpogeGz N

theorem nativeAlpogeDyadicWindowWeight_of_le
    (N n : ℕ) (hn : n ≤ N) : nativeAlpogeDyadicWindowWeight N n = 0 := by
  simp [nativeAlpogeDyadicWindowWeight, hn]

theorem nativeAlpogeDyadicWindowWeight_of_ge
    (N n : ℕ) (hn : 4 * N ≤ n) : nativeAlpogeDyadicWindowWeight N n = 0 := by
  by_cases hlo : n ≤ N
  · exact nativeAlpogeDyadicWindowWeight_of_le N n hlo
  · have hmid : ¬n ≤ 2 * N := by omega
    simp [nativeAlpogeDyadicWindowWeight, hlo, hmid, not_lt.mpr hn]

theorem nativeAlpogeDyadicWindowWeight_lower
    (N n : ℕ) (hlo : N < n) (hhi : n ≤ 2 * N) :
    nativeAlpogeDyadicWindowWeight N n = 2 * (1 - (N : ℝ) / (n : ℝ)) := by
  simp [nativeAlpogeDyadicWindowWeight, not_le.mpr hlo, hhi]

theorem nativeAlpogeDyadicWindowWeight_upper
    (N n : ℕ) (hlo : 2 * N < n) (hhi : n < 4 * N) :
    nativeAlpogeDyadicWindowWeight N n = 4 * (N : ℝ) / (n : ℝ) - 1 := by
  have hN : ¬n ≤ N := by omega
  simp [nativeAlpogeDyadicWindowWeight, hN, not_le.mpr hlo, hhi]

/-- The prime power at the middle endpoint has full weight. -/
theorem nativeAlpogeDyadicWindowWeight_middle (N : ℕ) (hN : 1 ≤ N) :
    nativeAlpogeDyadicWindowWeight N (2 * N) = 1 := by
  rw [nativeAlpogeDyadicWindowWeight_lower N (2 * N) (by omega) le_rfl]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  push_cast
  field_simp [hn]
  ring

/-- Both exterior endpoints have zero weight; the final sum is open at both. -/
theorem nativeAlpogeDyadicWindowWeight_endpoints (N : ℕ) :
    nativeAlpogeDyadicWindowWeight N N = 0 ∧
      nativeAlpogeDyadicWindowWeight N (4 * N) = 0 :=
  ⟨nativeAlpogeDyadicWindowWeight_of_le N N le_rfl,
    nativeAlpogeDyadicWindowWeight_of_ge N (4 * N) le_rfl⟩

private theorem nativeDyadicSum_extend
    (f : ℕ → ℝ) (M B : ℕ) (hMB : M ≤ B) :
    (∑ n ∈ Finset.Icc 1 M, f n) =
      ∑ n ∈ Finset.Icc 1 B, if n ≤ M then f n else 0 := by
  calc
    (∑ n ∈ Finset.Icc 1 M, f n) =
        ∑ n ∈ Finset.Icc 1 M, if n ≤ M then f n else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [ite_eq_left (Finset.mem_Icc.mp hn).2]
    _ = ∑ n ∈ Finset.Icc 1 B, if n ≤ M then f n else 0 := by
      apply Finset.sum_subset (Finset.Icc_subset_Icc le_rfl hMB)
      intro n hn hnot
      have hcut : ¬n ≤ M := by
        intro hle
        exact hnot (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1, hle⟩)
      rw [ite_eq_right hcut]

private theorem nativeDyadicRamp_eq_sum (M : ℕ) :
    (M : ℝ) * nativeLambdaRecip M - nativePsi M =
      ∑ n ∈ Finset.Icc 1 M, Λ n * ((M : ℝ) / (n : ℝ) - 1) := by
  unfold nativeLambdaRecip nativePsi
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  ring

private theorem nativeDyadicRamp_eq_sum_cut (M B : ℕ) (hMB : M ≤ B) :
    (M : ℝ) * nativeLambdaRecip M - nativePsi M =
      ∑ n ∈ Finset.Icc 1 B,
        if n ≤ M then Λ n * ((M : ℝ) / (n : ℝ) - 1) else 0 := by
  rw [nativeDyadicRamp_eq_sum]
  exact nativeDyadicSum_extend _ M B hMB

private theorem nativeDyadicRamp_coefficient
    (N n : ℕ) (hn : 1 ≤ n) (hn4 : n ≤ 4 * N) :
    Λ n * (((4 * N : ℕ) : ℝ) / (n : ℝ) - 1) -
        3 * (if n ≤ 2 * N then
          Λ n * (((2 * N : ℕ) : ℝ) / (n : ℝ) - 1) else 0) +
        2 * (if n ≤ N then Λ n * ((N : ℝ) / (n : ℝ) - 1) else 0) =
      Λ n * nativeAlpogeDyadicWindowWeight N n := by
  by_cases hlo : n ≤ N
  · have hmid : n ≤ 2 * N := by omega
    simp only [nativeAlpogeDyadicWindowWeight, ite_eq_left hlo, ite_eq_left hmid, mul_zero]
    push_cast
    ring
  · by_cases hmid : n ≤ 2 * N
    · simp only [nativeAlpogeDyadicWindowWeight, ite_eq_right hlo, ite_eq_left hmid,
        mul_zero, add_zero]
      push_cast
      ring
    · by_cases hhi : n < 4 * N
      · simp only [nativeAlpogeDyadicWindowWeight, ite_eq_right hlo, ite_eq_right hmid,
          ite_eq_left hhi, mul_zero, sub_zero, add_zero, Nat.cast_mul, Nat.cast_ofNat]
      · have heq : n = 4 * N := by omega
        have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
        have hratioNat : (((4 * N : ℕ) : ℝ) / (n : ℝ)) = 1 := by
          rw [← heq, div_self hn0]
        have hratio : 4 * (N : ℝ) / (n : ℝ) = 1 := by
          simpa only [Nat.cast_mul, Nat.cast_ofNat] using hratioNat
        simp [nativeAlpogeDyadicWindowWeight, hlo, hmid, hhi, hratio]

private theorem nativeDyadicWindow_sum_extend (N : ℕ) :
    nativeAlpogeDyadicPrimePowerWindow N =
      ∑ n ∈ Finset.Icc 1 (4 * N), Λ n * nativeAlpogeDyadicWindowWeight N n := by
  unfold nativeAlpogeDyadicPrimePowerWindow
  apply Finset.sum_subset
  · intro n hn
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ioo.mp hn
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro n _hn hnot
    by_cases hlo : n ≤ N
    · rw [nativeAlpogeDyadicWindowWeight_of_le N n hlo, mul_zero]
    · have hhi : 4 * N ≤ n := by
        by_contra h
        exact hnot (Finset.mem_Ioo.mpr ⟨by omega, by omega⟩)
      rw [nativeAlpogeDyadicWindowWeight_of_ge N n hhi, mul_zero]

/-- The exact arithmetic part of the three-scale cancellation. No coefficient
is estimated or omitted: the old prefix cancels term by term. -/
theorem nativeAlpogeDyadicPrimePowerWindow_eq (N : ℕ) :
    nativeAlpogeDyadicPrimePowerWindow N =
      (((4 * N : ℕ) : ℝ) * nativeLambdaRecip (4 * N) - nativePsi (4 * N)) -
        3 * (((2 * N : ℕ) : ℝ) * nativeLambdaRecip (2 * N) - nativePsi (2 * N)) +
        2 * ((N : ℝ) * nativeLambdaRecip N - nativePsi N) := by
  rw [nativeDyadicWindow_sum_extend, nativeDyadicRamp_eq_sum (4 * N),
    nativeDyadicRamp_eq_sum_cut (2 * N) (4 * N) (by omega),
    nativeDyadicRamp_eq_sum_cut N (4 * N) (by omega),
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  exact (nativeDyadicRamp_coefficient N n
    (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2).symm

/-- Exact dyadic localization of `nativeAlpogeGz`, on the original prime powers.
The remaining signed deficit is not asserted to satisfy a critical bound. -/
theorem nativeAlpogeDyadicDifference_eq_primePowerWindow (N : ℕ) (hN : 1 ≤ N) :
    nativeAlpogeDyadicDifference N =
      2 * (N : ℝ) * Real.log 2 - nativeAlpogeDyadicPrimePowerWindow N := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    have h := Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (by norm_num : (2 : ℝ) ≠ 0)
    norm_num at h
    linarith
  have hlog2N : Real.log (((2 * N : ℕ) : ℝ)) =
      Real.log 2 + Real.log (N : ℝ) := by
    push_cast
    exact Real.log_mul (by norm_num) hN0
  have hlog4N : Real.log (((4 * N : ℕ) : ℝ)) =
      2 * Real.log 2 + Real.log (N : ℝ) := by
    push_cast
    rw [Real.log_mul (by norm_num) hN0, hlog4]
  have hsource := nativeAlpogeDyadicPrimePowerWindow_eq N
  unfold nativeAlpogeDyadicDifference nativeAlpogeGz
  rw [hlog2N, hlog4N]
  push_cast at hsource ⊢
  linear_combination hsource

/-- Algebraic multiplier when the forward dilation factor is `q`. -/
theorem nativeAlpogeDyadicForwardPolynomial (q : ℂ) :
    -(q ^ 2) + 3 * q - 2 = (q - 1) * (2 - q) := by
  ring

/-- Algebraic multiplier when the backward dilation factor is `q`. -/
theorem nativeAlpogeDyadicBackwardPolynomial (q : ℂ) :
    -1 + 3 * q - 2 * q ^ 2 = (1 - q) * (2 * q - 1) := by
  ring

end RHLean.Analysis
