import Mathlib
import Mathlib.NumberTheory.Harmonic.Bounds
import RHLean.Analysis.NativePNTSelberg

/-!
# Bounded reciprocal mass of the Chebyshev error

Let `R(N) = psi(N) - N`.  The elementary Erdos step needs the signed reciprocal
mass

`sum_{1 <= n <= N} R(n) / (n(n+1))`

to stay uniformly bounded.  This module proves that fact from the already
formalized Mertens-first-theorem estimate by an exact finite Abel identity.
No prime-distribution asymptotic is used.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

/-- Discrete Chebyshev error. -/
def nativePNTError (N : ℕ) : ℝ := nativePsi N - (N : ℝ)

/-- Signed reciprocal mass used in Erdos's good-interval argument. -/
def nativePNTWeightedErrorMass (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N,
    nativePNTError n / ((n : ℝ) * (n + 1 : ℝ))

/-- One-step increment of the finite Chebyshev mass. -/
theorem nativePsi_succ (N : ℕ) :
    nativePsi (N + 1) = nativePsi N + Λ (N + 1) := by
  unfold nativePsi
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]

/-- One-step increment of the reciprocal von Mangoldt mass. -/
theorem nativeLambdaRecip_succ (N : ℕ) :
    nativeLambdaRecip (N + 1) =
      nativeLambdaRecip N + Λ (N + 1) / (N + 1 : ℝ) := by
  unfold nativeLambdaRecip
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
  norm_num [Nat.cast_add, Nat.cast_one]

/-- Exact finite Abel identity for the Chebyshev mass. -/
theorem nativePsi_weighted_abel (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N,
      nativePsi n / ((n : ℝ) * (n + 1 : ℝ))) =
      nativeLambdaRecip N - nativePsi N / (N + 1 : ℝ) := by
  induction N with
  | zero =>
      simp [nativePsi, nativeLambdaRecip]
  | succ N ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1), ih,
        nativeLambdaRecip_succ, nativePsi_succ]
      push_cast
      have h1 : (N : ℝ) + 1 ≠ 0 := by positivity
      have h2 : (N : ℝ) + 2 ≠ 0 := by positivity
      field_simp [h1, h2]
      ring_nf

/-- The corresponding linear kernel telescopes to a harmonic number. -/
theorem nativeLinear_weighted_abel (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N,
      (n : ℝ) / ((n : ℝ) * (n + 1 : ℝ))) =
      (harmonic (N + 1) : ℝ) - 1 := by
  induction N with
  | zero => norm_num [harmonic_succ]
  | succ N ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1), ih]
      rw [harmonic_succ (N + 1)]
      push_cast
      have h1 : (N : ℝ) + 1 ≠ 0 := by positivity
      have h2 : (N : ℝ) + 2 ≠ 0 := by positivity
      field_simp [h1, h2]
      ring_nf

/-- Exact expression of the signed reciprocal error mass in terms of Mertens'
first theorem, the endpoint Chebyshev mass, and one harmonic number. -/
theorem nativePNTWeightedErrorMass_eq (N : ℕ) :
    nativePNTWeightedErrorMass N =
      nativeLambdaRecip N - nativePsi N / (N + 1 : ℝ) -
        ((harmonic (N + 1) : ℝ) - 1) := by
  unfold nativePNTWeightedErrorMass nativePNTError
  have hsplit :
      (∑ n ∈ Finset.Icc 1 N,
        (nativePsi n - (n : ℝ)) / ((n : ℝ) * (n + 1 : ℝ))) =
        (∑ n ∈ Finset.Icc 1 N,
          nativePsi n / ((n : ℝ) * (n + 1 : ℝ))) -
        ∑ n ∈ Finset.Icc 1 N,
          (n : ℝ) / ((n : ℝ) * (n + 1 : ℝ)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _hn
    ring
  rw [hsplit, nativePsi_weighted_abel, nativeLinear_weighted_abel]

/-- Harmonic excess over `log N` is uniformly bounded by `1 + log 2`. -/
theorem nativeHarmonic_succ_sub_log_bounds
    (N : ℕ) (hN : 1 ≤ N) :
    0 ≤ (harmonic (N + 1) : ℝ) - Real.log N ∧
      (harmonic (N + 1) : ℝ) - Real.log N ≤ 1 + Real.log 2 := by
  have hlower : Real.log (N : ℝ) ≤ (harmonic (N + 1) : ℝ) := by
    calc
      Real.log (N : ℝ) ≤ Real.log ((N + 2 : ℕ) : ℝ) := by
        apply Real.log_le_log
        · exact_mod_cast hN
        · exact_mod_cast (show N ≤ N + 2 by omega)
      _ ≤ (harmonic (N + 1) : ℝ) := by
        simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_assoc] using
          (log_add_one_le_harmonic (N + 1))
  have hupper0 :
      (harmonic (N + 1) : ℝ) ≤ 1 + Real.log (N + 1 : ℝ) := by
    simpa using harmonic_le_one_add_log (N + 1)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNone : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hratio : (N : ℝ) + 1 ≤ 2 * (N : ℝ) := by
    linarith
  have hlogratio : Real.log (N + 1 : ℝ) ≤ Real.log 2 + Real.log N := by
    change Real.log ((N : ℝ) + 1) ≤ Real.log 2 + Real.log (N : ℝ)
    calc
      Real.log ((N : ℝ) + 1) ≤ Real.log (2 * (N : ℝ)) := by
        apply Real.log_le_log
        · positivity
        · exact hratio
      _ = Real.log 2 + Real.log N := by
        rw [Real.log_mul (by norm_num) (ne_of_gt hNpos)]
  constructor
  · linarith
  · have hupper0' :
        (harmonic (N + 1) : ℝ) ≤ 1 + Real.log (N : ℝ) + Real.log 2 := by
      calc
        (harmonic (N + 1) : ℝ) ≤ 1 + Real.log (N + 1 : ℝ) := hupper0
        _ ≤ 1 + (Real.log 2 + Real.log N) := by linarith
        _ = 1 + Real.log N + Real.log 2 := by ring
    linarith

/-- Uniform bound for the signed reciprocal Chebyshev-error mass. -/
theorem nativePNTWeightedErrorMass_abs_le
    (N : ℕ) :
    |nativePNTWeightedErrorMass N| ≤
      2 * (Real.log 4 + 2) + Real.log 2 + 3 := by
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst N
    simp [nativePNTWeightedErrorMass]
    have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  · have hN : 1 ≤ N := hNpos
    have heq := nativePNTWeightedErrorMass_eq N
    have hLambda := nativeLambdaRecip_sub_log_abs_le N hN
    have hpsi0 := nativePsi_nonneg N
    have hpsi := nativePsi_le_const_mul N
    have hden : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hfrac0 : 0 ≤ nativePsi N / ((N : ℝ) + 1) :=
      div_nonneg hpsi0 hden.le
    have hfrac : nativePsi N / ((N : ℝ) + 1) ≤ Real.log 4 + 2 := by
      have hNlt : (N : ℝ) < (N : ℝ) + 1 := by linarith
      have hconst0 : 0 ≤ Real.log 4 + 2 := by
        have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
        linarith
      calc
        nativePsi N / ((N : ℝ) + 1) ≤
            ((Real.log 4 + 2) * (N : ℝ)) / ((N : ℝ) + 1) :=
          div_le_div_of_nonneg_right hpsi hden.le
        _ ≤ Real.log 4 + 2 := by
          rw [div_le_iff₀ hden]
          nlinarith
    have hharm := nativeHarmonic_succ_sub_log_bounds N hN
    rw [heq]
    rw [abs_le] at hLambda ⊢
    constructor <;> linarith [hLambda.1, hLambda.2, hfrac0, hfrac,
      hharm.1, hharm.2]

end RHLean.Analysis
