import Mathlib
import RHLean.Analysis.NativePNTSelberg

/-!
# Sharp logarithmic sum estimates for the native PNT route

`RHLean.Analysis.NativePNTSelberg` brackets `log(N!)` between
`N log N - N + 1` and `N log N`.  That pair has error `O(N)`, which is already
the size of the main term targeted by Selberg's symmetry formula, so it cannot
feed the summatory `Lambda_2` estimate.

This module sharpens the upper side to

`log(N!) <= N log N - N + 1 + log N`,

which together with the existing lower bound gives the `O(log N)` two-sided
estimate

`|log(N!) - (N log N - N + 1)| <= log N`.

The proof is the elementary induction whose step is exactly
`(n+1) (log(n+1) - log n) >= 1`, itself an instance of `log x <= x - 1` at
`x = n/(n+1)`.  No asymptotic or prime-distribution input is used.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace RHLean.Analysis

/-- Multiplicative form of the elementary logarithmic increment lower bound
`log(n+1) - log n >= 1/(n+1)`.  Stating it without division keeps it linear in
the atoms used by the factorial induction. -/
theorem nativeOne_le_succ_mul_log_succ_sub_log
    (n : ℕ) (hn : 1 ≤ n) :
    (1 : ℝ) ≤ ((n : ℝ) + 1) *
      (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hsuccpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hratio :
      Real.log ((n : ℝ) / ((n : ℝ) + 1)) =
        Real.log (n : ℝ) - Real.log ((n : ℝ) + 1) :=
    Real.log_div (ne_of_gt hnpos) (ne_of_gt hsuccpos)
  have h := Real.log_le_sub_one_of_pos
    (show 0 < ((n : ℝ) / ((n : ℝ) + 1)) by positivity)
  rw [hratio] at h
  have hcancel :
      ((n : ℝ) + 1) * ((n : ℝ) / ((n : ℝ) + 1) - 1) = -1 := by
    field_simp
  have hmul := mul_le_mul_of_nonneg_left h hsuccpos.le
  rw [hcancel] at hmul
  linarith

/-- **Sharp upper bound for `log(N!)`.**  This is the companion of
`nativeLogFactorial_lower`, improving `nativeLogFactorial_upper` from an `O(N)`
error term to an `O(log N)` one. -/
theorem nativeLogFactorial_upper_sharp :
    ∀ N : ℕ, 1 ≤ N →
      Real.log ((Nat.factorial N : ℕ) : ℝ) ≤
        (N : ℝ) * Real.log N - (N : ℝ) + 1 + Real.log N := by
  intro N hN
  induction N with
  | zero => omega
  | succ n ih =>
      by_cases hn0 : n = 0
      · subst n
        norm_num
      · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
        have ih' := ih hn1
        have hnpos : (0 : ℝ) < (n : ℝ) := by
          exact_mod_cast (Nat.pos_of_ne_zero hn0)
        have hkey := nativeOne_le_succ_mul_log_succ_sub_log n hn1
        have hfac :
            Real.log ((Nat.factorial (n + 1) : ℕ) : ℝ) =
              Real.log ((n + 1 : ℕ) : ℝ) +
                Real.log ((Nat.factorial n : ℕ) : ℝ) := by
          rw [Nat.factorial_succ, Nat.cast_mul,
            Real.log_mul (by positivity)
              (by exact_mod_cast (Nat.factorial_ne_zero n))]
        rw [hfac]
        push_cast
        push_cast at ih'
        nlinarith [ih', hkey]

/-- **`log(N!) = N log N - N + 1 + O(log N)`** with an explicit constant. -/
theorem nativeLogFactorial_sub_main_abs_le (N : ℕ) (hN : 1 ≤ N) :
    |Real.log ((Nat.factorial N : ℕ) : ℝ) -
        ((N : ℝ) * Real.log N - (N : ℝ) + 1)| ≤ Real.log N := by
  have hlow := nativeLogFactorial_lower N hN
  have hup := nativeLogFactorial_upper_sharp N hN
  have hlogN : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN)
  rw [abs_le]
  constructor <;> linarith

/-- The same `O(log N)` estimate written for the finite logarithmic mass
`sum_{n <= N} log n`, which is the form consumed by the summatory Selberg
reindexing. -/
theorem nativeLogMass_sub_main_abs_le (N : ℕ) (hN : 1 ≤ N) :
    |nativeLogMass N - ((N : ℝ) * Real.log N - (N : ℝ) + 1)| ≤
      Real.log N := by
  unfold nativeLogMass
  rw [← nativeLogFactorial_eq_sum_log]
  exact nativeLogFactorial_sub_main_abs_le N hN

end RHLean.Analysis
