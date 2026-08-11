from pathlib import Path

p = Path('RHLean/Analysis/NativePNTErrorMass.lean')
s = p.read_text()
assert 'nativeLambdaLogRecip_sub_half_logSq_abs_le' not in s
marker = '\nend RHLean.Analysis\n'
assert marker in s
block = r'''

/-! ## Reciprocal logarithmic von Mangoldt moment -/

/-- Reciprocal log-weighted von Mangoldt mass. -/
def nativeLambdaLogRecip (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, (Λ n / (n : ℝ)) * Real.log (n : ℝ)

private theorem nativePNTTelescopeIco
    (b : ℕ → ℝ) : ∀ M : ℕ, 1 ≤ M →
    (∑ n ∈ Finset.Ico 1 M, (b (n + 1) - b n)) = b M - b 1 := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ M hM ih =>
      rw [Finset.sum_Ico_succ_top hM, ih]
      ring

private theorem nativePNTLogIncrement_nonneg
    (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) := by
  apply sub_nonneg.mpr
  apply Real.log_le_log
  · exact_mod_cast hn
  · exact_mod_cast (show n ≤ n + 1 by omega)

private theorem nativePNTLogIncrement_le_one
    (n : ℕ) (hn : 1 ≤ n) :
    Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) ≤ 1 := by
  have hinc := nativeLog_succ_sub_log_le_inv n hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
  have hrecip : (1 : ℝ) / (n : ℝ) ≤ 1 := by
    rw [div_le_one hnpos]
    exact_mod_cast hn
  exact hinc.trans hrecip

private theorem nativePNTLogIncrement_sum
    (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Ico 1 N,
      (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ))) = Real.log N := by
  have h := nativePNTTelescopeIco (fun n => Real.log (n : ℝ)) N hN
  simpa using h

private theorem nativePNTLogSquareIncrement_sum
    (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Ico 1 N,
      ((Real.log ((n + 1 : ℕ) : ℝ)) ^ 2 -
        (Real.log (n : ℝ)) ^ 2)) = (Real.log N) ^ 2 := by
  have h := nativePNTTelescopeIco
    (fun n => (Real.log (n : ℝ)) ^ 2) N hN
  simpa using h

/-- Abel form of the reciprocal log-weighted von Mangoldt mass. -/
theorem nativeLambdaLogRecip_abel (N : ℕ) :
    nativeLambdaLogRecip N =
      nativeLambdaRecip N * Real.log N +
        ∑ n ∈ Finset.Ico 1 N,
          nativeLambdaRecip n *
            (Real.log (n : ℝ) - Real.log ((n + 1 : ℕ) : ℝ)) := by
  have h := nativeAbelIccOne
    (fun n => Λ n / (n : ℝ))
    (fun n => Real.log (n : ℝ)) N
  simpa [nativeLambdaLogRecip, nativeLambdaRecip] using h

/-- **Reciprocal log von Mangoldt moment.**  Mertens' first theorem and finite
Abel summation give the coefficient `1/2` without any prime-distribution
asymptotic:

`sum_{n<=N} Lambda(n) log(n) / n = (1/2) log^2 N + O(log N)`.
-/
theorem nativeLambdaLogRecip_sub_half_logSq_abs_le
    (N : ℕ) (hN : 1 ≤ N) :
    |nativeLambdaLogRecip N - (1 / 2 : ℝ) * (Real.log N) ^ 2| ≤
      (2 * (Real.log 4 + 2) + 1) * Real.log N := by
  let delta : ℕ → ℝ := fun n =>
    Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)
  have hlog0 : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN)
  have hdelta0 : ∀ n ∈ Finset.Ico 1 N, 0 ≤ delta n := by
    intro n hn
    exact nativePNTLogIncrement_nonneg n (Finset.mem_Ico.mp hn).1
  have hdelta1 : ∀ n ∈ Finset.Ico 1 N, delta n ≤ 1 := by
    intro n hn
    exact nativePNTLogIncrement_le_one n (Finset.mem_Ico.mp hn).1
  have hsumdelta :
      (∑ n ∈ Finset.Ico 1 N, delta n) = Real.log N := by
    simpa [delta] using nativePNTLogIncrement_sum N hN
  have hsquares0 :
      0 ≤ ∑ n ∈ Finset.Ico 1 N, (delta n) ^ 2 := by
    exact Finset.sum_nonneg fun n _hn => sq_nonneg (delta n)
  have hsquares_le :
      (∑ n ∈ Finset.Ico 1 N, (delta n) ^ 2) ≤ Real.log N := by
    calc
      (∑ n ∈ Finset.Ico 1 N, (delta n) ^ 2) ≤
          ∑ n ∈ Finset.Ico 1 N, delta n := by
        apply Finset.sum_le_sum
        intro n hn
        have h0 := hdelta0 n hn
        have h1 := hdelta1 n hn
        have hm := mul_nonneg h0 (sub_nonneg.mpr h1)
        nlinarith
      _ = Real.log N := hsumdelta
  have hsqsplit :
      (∑ n ∈ Finset.Ico 1 N,
        ((Real.log ((n + 1 : ℕ) : ℝ)) ^ 2 -
          (Real.log (n : ℝ)) ^ 2)) =
        2 * (∑ n ∈ Finset.Ico 1 N,
          Real.log (n : ℝ) * delta n) +
          ∑ n ∈ Finset.Ico 1 N, (delta n) ^ 2 := by
    calc
      (∑ n ∈ Finset.Ico 1 N,
        ((Real.log ((n + 1 : ℕ) : ℝ)) ^ 2 -
          (Real.log (n : ℝ)) ^ 2)) =
        ∑ n ∈ Finset.Ico 1 N,
          (2 * (Real.log (n : ℝ) * delta n) + (delta n) ^ 2) := by
        apply Finset.sum_congr rfl
        intro n _hn
        simp only [delta]
        ring
      _ = 2 * (∑ n ∈ Finset.Ico 1 N,
          Real.log (n : ℝ) * delta n) +
          ∑ n ∈ Finset.Ico 1 N, (delta n) ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hsqid :
      (Real.log N) ^ 2 =
        2 * (∑ n ∈ Finset.Ico 1 N,
          Real.log (n : ℝ) * delta n) +
          ∑ n ∈ Finset.Ico 1 N, (delta n) ^ 2 := by
    calc
      (Real.log N) ^ 2 =
          ∑ n ∈ Finset.Ico 1 N,
            ((Real.log ((n + 1 : ℕ) : ℝ)) ^ 2 -
              (Real.log (n : ℝ)) ^ 2) :=
        (nativePNTLogSquareIncrement_sum N hN).symm
      _ = _ := hsqsplit
  have hmain :
      (Real.log N) ^ 2 +
          (∑ n ∈ Finset.Ico 1 N,
            Real.log (n : ℝ) *
              (Real.log (n : ℝ) - Real.log ((n + 1 : ℕ) : ℝ))) =
        (1 / 2 : ℝ) * (Real.log N) ^ 2 +
          (1 / 2 : ℝ) *
            (∑ n ∈ Finset.Ico 1 N, (delta n) ^ 2) := by
    have hneg :
        (∑ n ∈ Finset.Ico 1 N,
          Real.log (n : ℝ) *
            (Real.log (n : ℝ) - Real.log ((n + 1 : ℕ) : ℝ))) =
          -(∑ n ∈ Finset.Ico 1 N,
            Real.log (n : ℝ) * delta n) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro n _hn
      simp only [delta]
      ring
    rw [hneg]
    nlinarith [hsqid]
  have hsumdecomp :
      (∑ n ∈ Finset.Ico 1 N,
        nativeLambdaRecip n *
          (Real.log (n : ℝ) - Real.log ((n + 1 : ℕ) : ℝ))) =
        (∑ n ∈ Finset.Ico 1 N,
          Real.log (n : ℝ) *
            (Real.log (n : ℝ) - Real.log ((n + 1 : ℕ) : ℝ))) +
        ∑ n ∈ Finset.Ico 1 N,
          (nativeLambdaRecip n - Real.log n) *
            (Real.log (n : ℝ) - Real.log ((n + 1 : ℕ) : ℝ)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _hn
    ring
  have hdecomp :
      nativeLambdaLogRecip N - (1 / 2 : ℝ) * (Real.log N) ^ 2 =
        (1 / 2 : ℝ) * (∑ n ∈ Finset.Ico 1 N, (delta n) ^ 2) +
          (nativeLambdaRecip N - Real.log N) * Real.log N +
          ∑ n ∈ Finset.Ico 1 N,
            (nativeLambdaRecip n - Real.log n) *
              (Real.log (n : ℝ) - Real.log ((n + 1 : ℕ) : ℝ)) := by
    rw [nativeLambdaLogRecip_abel, hsumdecomp]
    have hend :
        nativeLambdaRecip N * Real.log N =
          (Real.log N) ^ 2 +
            (nativeLambdaRecip N - Real.log N) * Real.log N := by ring
    rw [hend, hmain]
    ring
  have hhalf :
      |(1 / 2 : ℝ) * (∑ n ∈ Finset.Ico 1 N, (delta n) ^ 2)| ≤
        (1 / 2 : ℝ) * Real.log N := by
    rw [abs_of_nonneg (mul_nonneg (by norm_num) hsquares0)]
    exact mul_le_mul_of_nonneg_left hsquares_le (by norm_num)
  have hendpoint :
      |(nativeLambdaRecip N - Real.log N) * Real.log N| ≤
        (Real.log 4 + 2) * Real.log N := by
    rw [abs_mul, abs_of_nonneg hlog0]
    exact mul_le_mul_of_nonneg_right
      (nativeLambdaRecip_sub_log_abs_le N hN) hlog0
  have hinteriorPoint : ∀ n ∈ Finset.Ico 1 N,
      |(nativeLambdaRecip n - Real.log n) *
        (Real.log (n : ℝ) - Real.log ((n + 1 : ℕ) : ℝ))| ≤
        (Real.log 4 + 2) * delta n := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Ico.mp hn).1
    have hd0 := hdelta0 n hn
    have herr := nativeLambdaRecip_sub_log_abs_le n hn1
    have hneg :
        Real.log (n : ℝ) - Real.log ((n + 1 : ℕ) : ℝ) = -delta n := by
      simp only [delta]
      ring
    rw [hneg, abs_mul, abs_neg, abs_of_nonneg hd0]
    exact mul_le_mul_of_nonneg_right herr hd0
  have hinterior :
      |∑ n ∈ Finset.Ico 1 N,
        (nativeLambdaRecip n - Real.log n) *
          (Real.log (n : ℝ) - Real.log ((n + 1 : ℕ) : ℝ))| ≤
        (Real.log 4 + 2) * Real.log N := by
    calc
      |∑ n ∈ Finset.Ico 1 N,
        (nativeLambdaRecip n - Real.log n) *
          (Real.log (n : ℝ) - Real.log ((n + 1 : ℕ) : ℝ))| ≤
        ∑ n ∈ Finset.Ico 1 N,
          |(nativeLambdaRecip n - Real.log n) *
            (Real.log (n : ℝ) - Real.log ((n + 1 : ℕ) : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Finset.Ico 1 N, (Real.log 4 + 2) * delta n :=
        Finset.sum_le_sum hinteriorPoint
      _ = (Real.log 4 + 2) *
          (∑ n ∈ Finset.Ico 1 N, delta n) := by
        rw [Finset.mul_sum]
      _ = (Real.log 4 + 2) * Real.log N := by rw [hsumdelta]
  rw [hdecomp]
  calc
    |(1 / 2 : ℝ) * (∑ n ∈ Finset.Ico 1 N, (delta n) ^ 2) +
        (nativeLambdaRecip N - Real.log N) * Real.log N +
        ∑ n ∈ Finset.Ico 1 N,
          (nativeLambdaRecip n - Real.log n) *
            (Real.log (n : ℝ) - Real.log ((n + 1 : ℕ) : ℝ))| ≤
      (|(1 / 2 : ℝ) * (∑ n ∈ Finset.Ico 1 N, (delta n) ^ 2)| +
        |(nativeLambdaRecip N - Real.log N) * Real.log N|) +
        |∑ n ∈ Finset.Ico 1 N,
          (nativeLambdaRecip n - Real.log n) *
            (Real.log (n : ℝ) - Real.log ((n + 1 : ℕ) : ℝ))| := by
      exact (abs_add_le _ _).trans
        (add_le_add_right (abs_add_le _ _) _)
    _ ≤ (1 / 2 : ℝ) * Real.log N +
        (Real.log 4 + 2) * Real.log N +
        (Real.log 4 + 2) * Real.log N := by
      gcongr
    _ ≤ (2 * (Real.log 4 + 2) + 1) * Real.log N := by
      nlinarith
'''
s = s.replace(marker, block + marker, 1)
p.write_text(s)