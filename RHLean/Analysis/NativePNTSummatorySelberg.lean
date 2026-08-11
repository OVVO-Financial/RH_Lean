import Mathlib
import RHLean.Analysis.NativePNTSelberg

/-!
# Summatory Selberg interface

The pointwise Dirichlet-ring identity

`Lambda_2 = D Lambda + Lambda * Lambda`

is not yet Selberg's summatory formula.  This module performs that missing
finite reindexing in the same reciprocal-fibre coordinates used throughout
`RH_Lean`.

No asymptotic prime-distribution theorem is used here.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

/-- Summatory second von Mangoldt mass. -/
def nativeLambdaTwoSummatory (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, nativeLambdaTwo n

/-- Log-weighted von Mangoldt mass. -/
def nativeLambdaLogMass (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, Λ n * Real.log n

/-- Summatory Dirichlet self-convolution of von Mangoldt. -/
def nativeLambdaConvolutionMass (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, (Λ * Λ) n

/-- Summing the pointwise Selberg kernel gives the exact decomposition into
its log-weighted and convolution pieces. -/
theorem nativeLambdaTwoSummatory_eq_log_add_convolution (N : ℕ) :
    nativeLambdaTwoSummatory N =
      nativeLambdaLogMass N + nativeLambdaConvolutionMass N := by
  unfold nativeLambdaTwoSummatory nativeLambdaLogMass nativeLambdaConvolutionMass
  rw [nativeLambdaTwo_eq_logWeight_vonMangoldt_add_convolution]
  simp only [ArithmeticFunction.add_apply, arithmeticLogWeight_apply]
  exact Finset.sum_add_distrib

/-- Exact reciprocal-fibre form of the von Mangoldt self-convolution:

`sum_{m <= N} (Lambda * Lambda)(m)
   = sum_{d <= N} Lambda(d) * psi(floor(N/d))`.

This is the finite cofactor-first/endpoint-first Fubini step needed by
Selberg's symmetry formula. -/
theorem nativeLambdaConvolutionMass_eq_reciprocalPsi (N : ℕ) :
    nativeLambdaConvolutionMass N =
      ∑ d ∈ Finset.Icc 1 N, Λ d * nativePsi (N / d) := by
  unfold nativeLambdaConvolutionMass nativePsi
  have hmem : ∀ (n d : ℕ),
      n ∈ Finset.Icc 1 N ∧ d ∈ n.divisors ↔
        n ∈ (Finset.Icc 1 N).filter (fun x => d ∣ x) ∧ d ∈ Finset.Icc 1 N := by
    intro n d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hn1, hnN⟩, hdvd, hn0⟩
      have hd0 : d ≠ 0 := by
        rintro rfl
        exact hn0 (Nat.eq_zero_of_zero_dvd hdvd)
      exact ⟨⟨⟨hn1, hnN⟩, hdvd⟩,
        Nat.one_le_iff_ne_zero.mpr hd0,
        (Nat.le_of_dvd (by omega) hdvd).trans hnN⟩
    · rintro ⟨⟨⟨hn1, hnN⟩, hdvd⟩, hd1, _hdN⟩
      exact ⟨⟨hn1, hnN⟩, hdvd, by omega⟩
  calc
    (∑ n ∈ Finset.Icc 1 N, (Λ * Λ) n) =
        ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, Λ d * Λ (n / d) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hn0 : n ≠ 0 := by omega
      rw [ArithmeticFunction.mul_apply]
      apply Finset.sum_congr
      · ext ab
        simp only [Nat.mem_divisorsAntidiagonal, Nat.mem_divisors]
        constructor
        · rintro ⟨hab, _ha0, _hb0⟩
          refine ⟨hab ▸ dvd_mul_right ab.1 ab.2, ?_⟩
          omega
        · rintro ⟨hdvd, hn0'⟩
          exact ⟨Nat.mul_div_cancel' hdvd, by omega,
            Nat.div_ne_of_lt (Nat.lt_of_lt_of_le (by omega) (Nat.le_of_dvd (by omega) hdvd))⟩
      · intro ab hab
        have habprod : ab.1 * ab.2 = n := (Nat.mem_divisorsAntidiagonal.mp hab).1
        have hdvd : ab.1 ∣ n := habprod ▸ dvd_mul_right ab.1 ab.2
        have hdiv : n / ab.1 = ab.2 := by
          rw [← habprod]
          exact Nat.mul_div_left ab.2 ab.1
        simp [hdvd, hdiv]
    _ = ∑ d ∈ Finset.Icc 1 N,
          ∑ n ∈ (Finset.Icc 1 N).filter (fun x => d ∣ x),
            Λ d * Λ (n / d) :=
      Finset.sum_comm' hmem
    _ = ∑ d ∈ Finset.Icc 1 N,
          Λ d * ∑ m ∈ Finset.Icc 1 (N / d), Λ m := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mul_sum]
      have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
      have hmap :
          (Finset.Icc 1 N).filter (fun x => d ∣ x) =
            (Finset.Icc 1 (N / d)).image (fun m => d * m) := by
        ext n
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
        constructor
        · rintro ⟨⟨hn1, hnN⟩, hdvd⟩
          refine ⟨n / d, ?_, Nat.mul_div_cancel' hdvd |>.symm⟩
          have hq1 : 1 ≤ n / d := by
            exact Nat.one_le_div_iff hdpos |>.2 (Nat.le_of_dvd (by omega) hdvd)
          have hqN : n / d ≤ N / d := Nat.div_le_div_right hnN
          exact ⟨hq1, hqN⟩
        · rintro ⟨m, ⟨hm1, hmN⟩, rfl⟩
          have hmulN : d * m ≤ N := (Nat.le_div_iff_mul_le hdpos).1 hmN
          exact ⟨⟨by positivity, hmulN⟩, dvd_mul_right d m⟩
      rw [hmap, Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro m hm
        have hdne : d ≠ 0 := Nat.ne_of_gt hdpos
        rw [Nat.mul_div_left]
      · intro a _ha b _hb hab
        exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (Nat.ne_of_gt hdpos)) hab
    _ = ∑ d ∈ Finset.Icc 1 N, Λ d * nativePsi (N / d) := by rfl

/-- One-step increment of `nativePsi`, placed here so the summatory Selberg
modules do not depend on the later error-mass module. -/
theorem nativePsi_succ_eq (N : ℕ) :
    nativePsi (N + 1) = nativePsi N + Λ (N + 1) := by
  unfold nativePsi
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]

/-- Finite Abel summation for the log-weighted von Mangoldt mass. -/
theorem nativeLambdaLogMass_abel (N : ℕ) :
    nativeLambdaLogMass N =
      nativePsi N * Real.log N -
        ∑ n ∈ Finset.Ico 1 N,
          nativePsi n * (Real.log (n + 1) - Real.log n) := by
  induction N with
  | zero =>
      simp [nativeLambdaLogMass, nativePsi]
  | succ N ih =>
      by_cases hN0 : N = 0
      · subst N
        simp [nativeLambdaLogMass, nativePsi]
      · have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
        unfold nativeLambdaLogMass at ih ⊢
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
        fold nativeLambdaLogMass
        rw [ih, nativePsi_succ_eq]
        rw [Finset.sum_Ico_succ_top hN1]
        ring

/-- Elementary logarithmic increment bound used in the Abel correction. -/
theorem nativeLog_succ_sub_log_le_inv
    (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n + 1) - Real.log n ≤ 1 / (n : ℝ) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hsuccpos : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hratio :
      Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) =
        Real.log (n + 1) - Real.log n := by
    rw [Real.log_div (ne_of_gt hsuccpos) (ne_of_gt hnpos)]
  have h := Real.log_le_sub_one_of_pos
    (show 0 < (((n + 1 : ℕ) : ℝ) / (n : ℝ)) by positivity)
  rw [hratio] at h
  have hsub : (((n + 1 : ℕ) : ℝ) / (n : ℝ)) - 1 = 1 / (n : ℝ) := by
    push_cast
    field_simp [ne_of_gt hnpos]
    ring
  simpa [hsub] using h

/-- The Abel correction is nonnegative. -/
theorem nativeLambdaLogAbelCorrection_nonneg (N : ℕ) :
    0 ≤ ∑ n ∈ Finset.Ico 1 N,
      nativePsi n * (Real.log (n + 1) - Real.log n) := by
  apply Finset.sum_nonneg
  intro n hn
  have hn1 : 1 ≤ n := (Finset.mem_Ico.mp hn).1
  have hlog : Real.log (n : ℝ) ≤ Real.log ((n + 1 : ℕ) : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast hn1
    · exact_mod_cast (show n ≤ n + 1 by omega)
  exact mul_nonneg (nativePsi_nonneg n) (sub_nonneg.mpr hlog)

/-- The Abel correction is at most the elementary Chebyshev constant times
`N`.  This is the precise `O(N)` bridge from the pointwise Selberg kernel to
its summatory `psi log` form. -/
theorem nativeLambdaLogAbelCorrection_le (N : ℕ) :
    (∑ n ∈ Finset.Ico 1 N,
      nativePsi n * (Real.log (n + 1) - Real.log n)) ≤
      (Real.log 4 + 2) * (N : ℝ) := by
  have hpoint : ∀ n ∈ Finset.Ico 1 N,
      nativePsi n * (Real.log (n + 1) - Real.log n) ≤ Real.log 4 + 2 := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Ico.mp hn).1
    have hpsi := nativePsi_le_const_mul n
    have hinc := nativeLog_succ_sub_log_le_inv n hn1
    have hpsi0 := nativePsi_nonneg n
    have hinc0 : 0 ≤ Real.log (n + 1) - Real.log n := by
      apply sub_nonneg.mpr
      apply Real.log_le_log
      · exact_mod_cast hn1
      · exact_mod_cast (show n ≤ n + 1 by omega)
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hconst0 : 0 ≤ Real.log 4 + 2 := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
      linarith
    calc
      nativePsi n * (Real.log (n + 1) - Real.log n) ≤
          ((Real.log 4 + 2) * (n : ℝ)) *
            (Real.log (n + 1) - Real.log n) :=
        mul_le_mul_of_nonneg_right hpsi hinc0
      _ ≤ ((Real.log 4 + 2) * (n : ℝ)) * (1 / (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hinc (mul_nonneg hconst0 (by positivity))
      _ = Real.log 4 + 2 := by
        field_simp [ne_of_gt hnpos]
  calc
    (∑ n ∈ Finset.Ico 1 N,
        nativePsi n * (Real.log (n + 1) - Real.log n)) ≤
        ∑ _n ∈ Finset.Ico 1 N, (Real.log 4 + 2) :=
      Finset.sum_le_sum hpoint
    _ = ((Finset.Ico 1 N).card : ℝ) * (Real.log 4 + 2) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) * (Real.log 4 + 2) := by
      have hcard : (Finset.Ico 1 N).card ≤ N := by
        rw [Nat.card_Ico]
        omega
      have hcast : ((Finset.Ico 1 N).card : ℝ) ≤ (N : ℝ) := by exact_mod_cast hcard
      have hconst0 : 0 ≤ Real.log 4 + 2 := by
        have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
        linarith
      exact mul_le_mul_of_nonneg_right hcast hconst0
    _ = (Real.log 4 + 2) * (N : ℝ) := by ring

/-- Explicit absolute `O(N)` form of the Abel bridge. -/
theorem nativeLambdaLogMass_sub_psiLog_abs_le (N : ℕ) :
    |nativeLambdaLogMass N - nativePsi N * Real.log N| ≤
      (Real.log 4 + 2) * (N : ℝ) := by
  rw [nativeLambdaLogMass_abel]
  have h0 := nativeLambdaLogAbelCorrection_nonneg N
  have h1 := nativeLambdaLogAbelCorrection_le N
  rw [sub_sub_cancel_left, abs_neg, abs_of_nonneg h0]
  exact h1

/-- The exact Selberg summatory pair before its main-term estimate. -/
def nativeSelbergPair (N : ℕ) : ℝ :=
  nativePsi N * Real.log N +
    ∑ d ∈ Finset.Icc 1 N, Λ d * nativePsi (N / d)

/-- `nativeSelbergPair` differs from the summatory `Lambda_2` mass by only the
explicit Abel correction. -/
theorem nativeSelbergPair_sub_lambdaTwoSummatory_abs_le (N : ℕ) :
    |nativeSelbergPair N - nativeLambdaTwoSummatory N| ≤
      (Real.log 4 + 2) * (N : ℝ) := by
  rw [nativeLambdaTwoSummatory_eq_log_add_convolution,
    nativeLambdaConvolutionMass_eq_reciprocalPsi]
  unfold nativeSelbergPair
  have h := nativeLambdaLogMass_sub_psiLog_abs_le N
  simpa [abs_sub_comm, add_sub_add_right_eq_sub] using h

end RHLean.Analysis
