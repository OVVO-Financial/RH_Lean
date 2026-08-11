import Mathlib
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import RHLean.Analysis.NativePNTMertens

/-!
# Möbius logarithmic moments for the native Selberg route

The summatory identity

`sum_{n <= N} Lambda_2(n) = sum_{d <= N} mu(d) * S₂(floor(N/d))`

reduces Selberg's main term to reciprocal Möbius moments.  This module develops
those moments directly from finite convolution identities.  No PNT input or
zero-free argument is used.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

/-- Harmonic numbers as a positive-prefix real sum. -/
theorem nativeHarmonicReal_eq_sum_Icc (N : ℕ) :
    (harmonic N : ℝ) = ∑ m ∈ Finset.Icc 1 N, 1 / (m : ℝ) := by
  induction N with
  | zero => simp [harmonic_zero]
  | succ N ih =>
      rw [harmonic_succ, Rat.cast_add, ih,
        Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
      push_cast
      simp [one_div]

/-- Exact reciprocal convolution `mu * 1 = epsilon`, after dividing by the
endpoint.  This is the harmonic identity behind the first logarithmic Möbius
moment. -/
theorem nativeMobiusRecipHarmonic_eq_one
    (N : ℕ) (hN : 1 ≤ N) :
    (∑ d ∈ Finset.Icc 1 N,
      (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) *
        (harmonic (N / d) : ℝ)) = 1 := by
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
    · rintro ⟨⟨⟨hn1, hnN⟩, hdvd⟩, _hd1, _hdN⟩
      exact ⟨⟨hn1, hnN⟩, hdvd, Nat.ne_of_gt (by omega : 0 < n)⟩
  calc
    (∑ d ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) *
          (harmonic (N / d) : ℝ)) =
        ∑ d ∈ Finset.Icc 1 N,
          ∑ n ∈ (Finset.Icc 1 N).filter (fun x => d ∣ x),
            (ArithmeticFunction.moebius d : ℝ) / (n : ℝ) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [nativeHarmonicReal_eq_sum_Icc, Finset.mul_sum]
      have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
      have hmap :
          (Finset.Icc 1 N).filter (fun x => d ∣ x) =
            (Finset.Icc 1 (N / d)).image (fun m => d * m) := by
        ext n
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
        constructor
        · rintro ⟨⟨hn1, hnN⟩, hdvd⟩
          refine ⟨n / d, ?_, Nat.mul_div_cancel' hdvd⟩
          have hq1 : 1 ≤ n / d :=
            (Nat.one_le_div_iff hdpos).2 (Nat.le_of_dvd (by omega) hdvd)
          exact ⟨hq1, Nat.div_le_div_right hnN⟩
        · rintro ⟨m, ⟨hm1, hmN⟩, rfl⟩
          have hmulN' : m * d ≤ N := (Nat.le_div_iff_mul_le hdpos).1 hmN
          have hmulN : d * m ≤ N := by simpa [Nat.mul_comm] using hmulN'
          exact ⟨⟨by positivity, hmulN⟩, dvd_mul_right d m⟩
      rw [hmap, Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro m hm
        have hmpos : 0 < m := (Finset.mem_Icc.mp hm).1
        have hdmpos : (0 : ℝ) < (d : ℝ) * (m : ℝ) := by positivity
        push_cast
        field_simp [show (d : ℝ) ≠ 0 by positivity,
          show (m : ℝ) ≠ 0 by positivity]
        ring
      · intro a _ha b _hb hab
        exact Nat.eq_of_mul_eq_mul_left hdpos hab
    _ = ∑ n ∈ Finset.Icc 1 N,
          ∑ d ∈ n.divisors,
            (ArithmeticFunction.moebius d : ℝ) / (n : ℝ) :=
      (Finset.sum_comm' hmem).symm
    _ = ∑ n ∈ Finset.Icc 1 N,
          (if n = 1 then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
      calc
        (∑ d ∈ n.divisors,
            (ArithmeticFunction.moebius d : ℝ) / (n : ℝ)) =
            (∑ d ∈ n.divisors,
              (ArithmeticFunction.moebius d : ℝ)) / (n : ℝ) := by
          rw [Finset.sum_div]
        _ = ((if n = 1 then (1 : ℤ) else 0 : ℤ) : ℝ) / (n : ℝ) := by
          rw [← Int.cast_sum, nativeSumMoebiusDivisors n hn1]
        _ = if n = 1 then (1 : ℝ) else 0 := by
          split_ifs with h
          · subst n
            norm_num
          · simp
    _ = 1 := by
      simp [Finset.sum_ite_eq', Finset.mem_Icc, hN]

/-- First logarithmic reciprocal Möbius moment. -/
def nativeMobiusLogMomentOne (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N,
    (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) *
      Real.log (N / d : ℝ)

/-- Euler--Mascheroni remainder at an integer endpoint. -/
def nativeHarmonicLogError (q : ℕ) : ℝ :=
  (harmonic q : ℝ) - Real.log q - Real.eulerMascheroniConstant

private theorem nativeLogSucc_sub_log_le_inv
    (q : ℕ) (hq : 1 ≤ q) :
    Real.log ((q + 1 : ℕ) : ℝ) - Real.log (q : ℝ) ≤ 1 / (q : ℝ) := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hsuccpos : (0 : ℝ) < ((q + 1 : ℕ) : ℝ) := by positivity
  have hratio :
      Real.log (((q + 1 : ℕ) : ℝ) / (q : ℝ)) =
        Real.log ((q + 1 : ℕ) : ℝ) - Real.log (q : ℝ) := by
    rw [Real.log_div (ne_of_gt hsuccpos) (ne_of_gt hqpos)]
  have h := Real.log_le_sub_one_of_pos
    (show 0 < (((q + 1 : ℕ) : ℝ) / (q : ℝ)) by positivity)
  rw [hratio] at h
  have hsub : (((q + 1 : ℕ) : ℝ) / (q : ℝ)) - 1 = 1 / (q : ℝ) := by
    push_cast
    field_simp [ne_of_gt hqpos]
    ring
  rw [hsub] at h
  exact h

/-- Explicit Euler--Mascheroni remainder bound
`0 <= H_q - log q - gamma <= 1/q`. -/
theorem nativeHarmonicLogError_bounds
    (q : ℕ) (hq : 1 ≤ q) :
    0 ≤ nativeHarmonicLogError q ∧
      nativeHarmonicLogError q ≤ 1 / (q : ℝ) := by
  have hupperGamma := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' q
  have hlowerGamma := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant q
  have hq0 : q ≠ 0 := by omega
  simp only [Real.eulerMascheroniSeq', hq0, if_false] at hupperGamma
  simp only [Real.eulerMascheroniSeq] at hlowerGamma
  have hinc := nativeLogSucc_sub_log_le_inv q hq
  unfold nativeHarmonicLogError
  constructor
  · linarith
  · have hstrict :
        (harmonic q : ℝ) - Real.log q - Real.eulerMascheroniConstant <
          Real.log ((q + 1 : ℕ) : ℝ) - Real.log (q : ℝ) := by
      linarith
    exact hstrict.le.trans hinc

/-- Weighted Euler--Mascheroni remainder in the reciprocal Möbius identity. -/
def nativeMobiusHarmonicErrorMass (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N,
    (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) *
      nativeHarmonicLogError (N / d)

private theorem nativeReciprocalDivisorProduct_le_two_over
    (N d : ℕ) (hN : 1 ≤ N) (hd : d ∈ Finset.Icc 1 N) :
    (1 / (d : ℝ)) * (1 / (N / d : ℝ)) ≤ 2 / (N : ℝ) := by
  have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
  have hdN : d ≤ N := (Finset.mem_Icc.mp hd).2
  have hdpos : 0 < d := by omega
  have hq1 : 1 ≤ N / d := (Nat.one_le_div_iff hdpos).2 hdN
  have hmod : N % d < d := Nat.mod_lt N hdpos
  have hdecomp := Nat.mod_add_div N d
  have hlt : N < d * (N / d + 1) := by
    omega
  have hqdouble : N / d + 1 ≤ 2 * (N / d) := by omega
  have hmul : d * (N / d + 1) ≤ d * (2 * (N / d)) :=
    Nat.mul_le_mul_left d hqdouble
  have hNat : N ≤ 2 * (d * (N / d)) := by
    calc
      N ≤ d * (N / d + 1) := hlt.le
      _ ≤ d * (2 * (N / d)) := hmul
      _ = 2 * (d * (N / d)) := by omega
  have hReal : (N : ℝ) ≤ 2 * ((d : ℝ) * (N / d : ℝ)) := by
    exact_mod_cast hNat
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
  have hqR : (0 : ℝ) < (N / d : ℝ) := by exact_mod_cast (by omega : 0 < N / d)
  rw [← one_div_mul_one_div_rev, div_le_div_iff₀ (mul_pos hdR hqR) hNpos]
  simpa [mul_assoc, mul_comm, mul_left_comm] using hReal

/-- The accumulated harmonic remainder remains uniformly bounded despite the
hyperbolic reciprocal fibres. -/
theorem nativeMobiusHarmonicErrorMass_abs_le_two
    (N : ℕ) (hN : 1 ≤ N) :
    |nativeMobiusHarmonicErrorMass N| ≤ 2 := by
  unfold nativeMobiusHarmonicErrorMass
  calc
    |∑ d ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) *
          nativeHarmonicLogError (N / d)| ≤
        ∑ d ∈ Finset.Icc 1 N,
          |(ArithmeticFunction.moebius d : ℝ) / (d : ℝ) *
            nativeHarmonicLogError (N / d)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ Finset.Icc 1 N, 2 / (N : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
      have hdN : d ≤ N := (Finset.mem_Icc.mp hd).2
      have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
      have hq1 : 1 ≤ N / d :=
        (Nat.one_le_div_iff (by omega : 0 < d)).2 hdN
      have herr := nativeHarmonicLogError_bounds (N / d) hq1
      have hmu0 : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
        have h := ArithmeticFunction.abs_moebius_le_one (n := d)
        calc
          |(ArithmeticFunction.moebius d : ℝ)| =
              ((|ArithmeticFunction.moebius d| : ℤ) : ℝ) := by rw [Int.cast_abs]
          _ ≤ ((1 : ℤ) : ℝ) := by exact_mod_cast h
          _ = 1 := by norm_num
      have hterm :
          |(ArithmeticFunction.moebius d : ℝ) / (d : ℝ) *
              nativeHarmonicLogError (N / d)| ≤
            (1 / (d : ℝ)) * (1 / (N / d : ℝ)) := by
        rw [abs_mul, abs_div, abs_of_nonneg herr.1,
          abs_of_pos hdpos]
        have hdiv : |(ArithmeticFunction.moebius d : ℝ)| / (d : ℝ) ≤
            1 / (d : ℝ) := div_le_div_of_nonneg_right hmu0 hdpos.le
        exact mul_le_mul hdiv herr.2 (by positivity) (by positivity)
      exact hterm.trans (nativeReciprocalDivisorProduct_le_two_over N d hN hd)
    _ = ((Finset.Icc 1 N).card : ℝ) * (2 / (N : ℝ)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ = 2 := by
      rw [Nat.card_Icc]
      have hcard : N + 1 - 1 = N := by omega
      rw [hcard]
      have hN0 : (N : ℝ) ≠ 0 := by positivity
      field_simp

/-- Exact decomposition of the first logarithmic Möbius moment. -/
theorem nativeMobiusLogMomentOne_eq
    (N : ℕ) (hN : 1 ≤ N) :
    nativeMobiusLogMomentOne N =
      1 - Real.eulerMascheroniConstant * nativeMertensRecip N -
        nativeMobiusHarmonicErrorMass N := by
  have hexact := nativeMobiusRecipHarmonic_eq_one N hN
  unfold nativeMobiusLogMomentOne nativeMertensRecip
  unfold nativeMobiusHarmonicErrorMass nativeHarmonicLogError
  have hsplit :
      (∑ d ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) *
          (harmonic (N / d) : ℝ)) =
      (∑ d ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) *
          Real.log (N / d : ℝ)) +
      Real.eulerMascheroniConstant *
        (∑ d ∈ Finset.Icc 1 N,
          (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)) +
      (∑ d ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) *
          ((harmonic (N / d) : ℝ) - Real.log (N / d : ℝ) -
            Real.eulerMascheroniConstant)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d _hd
    ring
  rw [hsplit] at hexact
  linarith

/-- Uniform first logarithmic Möbius moment. -/
theorem nativeMobiusLogMomentOne_abs_le_four
    (N : ℕ) (hN : 1 ≤ N) :
    |nativeMobiusLogMomentOne N| ≤ 4 := by
  rw [nativeMobiusLogMomentOne_eq N hN]
  have hM := nativeMertensRecip_abs_le_one N
  have hE := nativeMobiusHarmonicErrorMass_abs_le_two N hN
  have hgammaPos : 0 ≤ Real.eulerMascheroniConstant :=
    (Real.one_half_lt_eulerMascheroniConstant).le.trans' (by norm_num)
  have hgamma : Real.eulerMascheroniConstant ≤ 1 := by
    linarith [Real.eulerMascheroniConstant_lt_two_thirds]
  calc
    |1 - Real.eulerMascheroniConstant * nativeMertensRecip N -
        nativeMobiusHarmonicErrorMass N| ≤
      |(1 : ℝ)| +
        |Real.eulerMascheroniConstant * nativeMertensRecip N| +
        |nativeMobiusHarmonicErrorMass N| := by
      calc
        |1 - Real.eulerMascheroniConstant * nativeMertensRecip N -
            nativeMobiusHarmonicErrorMass N| ≤
          |1 - Real.eulerMascheroniConstant * nativeMertensRecip N| +
            |nativeMobiusHarmonicErrorMass N| := abs_sub _ _
        _ ≤ (|(1 : ℝ)| +
            |Real.eulerMascheroniConstant * nativeMertensRecip N|) +
            |nativeMobiusHarmonicErrorMass N| := by
          gcongr
          exact abs_sub _ _
    _ ≤ 1 + 1 + 2 := by
      rw [abs_one, abs_mul, abs_of_nonneg hgammaPos]
      nlinarith [abs_nonneg (nativeMertensRecip N)]
    _ = 4 := by norm_num

end RHLean.Analysis
