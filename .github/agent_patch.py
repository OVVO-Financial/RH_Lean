from pathlib import Path

p = Path('RHLean/Analysis/NativePNTErdosContraction.lean')
s = p.read_text()


def repl(old: str, new: str) -> None:
    global s
    count = s.count(old)
    assert count == 1, (count, old[:120])
    s = s.replace(old, new, 1)


repl(
'''  have hlo := log_add_one_le_harmonic (B + 1)
  have hup := harmonic_le_one_add_log A
  push_cast at hlo hup ⊢
  norm_num at hlo
  linarith
''',
'''  have hlo : Real.log ((B + 2 : ℕ) : ℝ) ≤ (harmonic (B + 1) : ℝ) := by
    simpa [show B + 2 = (B + 1) + 1 by omega] using
      (log_add_one_le_harmonic (B + 1))
  have hup : (harmonic A : ℝ) ≤ 1 + Real.log (A : ℝ) := by
    simpa using (harmonic_le_one_add_log A)
  linarith
''')

repl(
'''    have hlog3 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
    have hC := nativeSelbergLinearConstant_le_182
    have hrho3 : nativeLambdaTwoSummatory 3 ≤ 600 := by
      norm_num at hlog3
      nlinarith [h3.2]
''',
'''    have hlog3 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
    have hC := nativeSelbergLinearConstant_le_182
    norm_num at hlog3
    have hC3 :
        (2 * (Real.log 4 + 2) + 172) * (3 : ℝ) ≤ 546 := by
      nlinarith
    have hlogpart : 2 * (3 : ℝ) * Real.log 3 ≤ 12 := by
      nlinarith
    have hrho3 : nativeLambdaTwoSummatory 3 ≤ 600 := by
      nlinarith [h3.2, hC3, hlogpart]
''')

repl(
'''  field_simp [hn0, hs0]
  ring

private theorem nativeRecipDiffSum_eq
''',
'''  field_simp [hn0, hs0]
  push_cast
  ring

private theorem nativeRecipDiffSum_eq
''')

repl(
'''        600 * (1 / ((n : ℝ) * (((n + 1 : ℕ) : ℝ)))) := by
      field_simp [ne_of_gt hnpos, ne_of_gt hspos]
      ring
    _ ≤ 2 * Real.log (n : ℝ) / (n : ℝ) + 182 / (n : ℝ) +
''',
'''        600 * (1 / ((n : ℝ) * (((n + 1 : ℕ) : ℝ)))) := by
      field_simp [ne_of_gt hnpos, ne_of_gt hspos]
    _ ≤ 2 * Real.log (n : ℝ) / (n : ℝ) + 182 / (n : ℝ) +
''')

repl(
'''    simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
''',
'''    simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
''')

repl(
'''    have hkernelLe :
        (∑ n ∈ Finset.Ico 1 N,
          (1 / (n : ℝ) - 1 / (((n + 1 : ℕ) : ℝ)))) ≤ 1 := by
      rw [hkernelEq]
      positivity
    calc
''',
'''    have hkernelLe :
        (∑ n ∈ Finset.Ico 1 N,
          (1 / (n : ℝ) - 1 / (((n + 1 : ℕ) : ℝ)))) ≤ 1 := by
      rw [hkernelEq]
      have hrecip0 : 0 ≤ 1 / (N : ℝ) := by positivity
      linarith
    have hlogScale :
        (∑ n ∈ Finset.Ico 1 N, 2 * Real.log (n : ℝ) / (n : ℝ)) =
          2 * (∑ n ∈ Finset.Ico 1 N, Real.log (n : ℝ) / (n : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _hn
      ring
    have hrecipScale :
        (∑ n ∈ Finset.Ico 1 N, 182 / (n : ℝ)) =
          182 * (∑ n ∈ Finset.Ico 1 N, 1 / (n : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _hn
      ring
    have hkernelScale :
        (∑ n ∈ Finset.Ico 1 N,
          600 * (1 / (n : ℝ) - 1 / (((n + 1 : ℕ) : ℝ)))) =
          600 * (∑ n ∈ Finset.Ico 1 N,
            (1 / (n : ℝ) - 1 / (((n + 1 : ℕ) : ℝ)))) := by
      rw [Finset.mul_sum]
    calc
''')

repl(
'''      _ = 2 * (∑ n ∈ Finset.Ico 1 N, Real.log (n : ℝ) / (n : ℝ)) +
          182 * (∑ n ∈ Finset.Ico 1 N, 1 / (n : ℝ)) +
          600 * (∑ n ∈ Finset.Ico 1 N,
            (1 / (n : ℝ) - 1 / (((n + 1 : ℕ) : ℝ)))) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
''',
'''      _ = 2 * (∑ n ∈ Finset.Ico 1 N, Real.log (n : ℝ) / (n : ℝ)) +
          182 * (∑ n ∈ Finset.Ico 1 N, 1 / (n : ℝ)) +
          600 * (∑ n ∈ Finset.Ico 1 N,
            (1 / (n : ℝ) - 1 / (((n + 1 : ℕ) : ℝ)))) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          hlogScale, hrecipScale, hkernelScale]
''')

repl(
'''    calc
      (∑ n ∈ G, nativeLambdaTwo n *
        (beta * ((N : ℝ) / (n : ℝ)) + D)) =
          beta * (∑ n ∈ G,
            nativeLambdaTwo n * ((N : ℝ) / (n : ℝ))) +
          D * (∑ n ∈ G, nativeLambdaTwo n) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro n _hn
        ring
      _ = _ := by rw [hGrec, hGmass]
''',
'''    calc
      (∑ n ∈ G, nativeLambdaTwo n *
        (beta * ((N : ℝ) / (n : ℝ)) + D)) =
          (∑ n ∈ G,
            beta * (nativeLambdaTwo n * ((N : ℝ) / (n : ℝ)))) +
          ∑ n ∈ G, D * nativeLambdaTwo n := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro n _hn
        ring
      _ = beta * (∑ n ∈ G,
            nativeLambdaTwo n * ((N : ℝ) / (n : ℝ))) +
          D * (∑ n ∈ G, nativeLambdaTwo n) := by
        rw [Finset.mul_sum, Finset.mul_sum]
      _ = _ := by rw [hGrec, hGmass]
''')

repl(
'''    calc
      (∑ n ∈ B, nativeLambdaTwo n *
        (alpha * ((N : ℝ) / (n : ℝ)) + D)) =
          alpha * (∑ n ∈ B,
            nativeLambdaTwo n * ((N : ℝ) / (n : ℝ))) +
          D * (∑ n ∈ B, nativeLambdaTwo n) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro n _hn
        ring
      _ = _ := by rw [hBrec, hBmass]
''',
'''    calc
      (∑ n ∈ B, nativeLambdaTwo n *
        (alpha * ((N : ℝ) / (n : ℝ)) + D)) =
          (∑ n ∈ B,
            alpha * (nativeLambdaTwo n * ((N : ℝ) / (n : ℝ)))) +
          ∑ n ∈ B, D * nativeLambdaTwo n := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro n _hn
        ring
      _ = alpha * (∑ n ∈ B,
            nativeLambdaTwo n * ((N : ℝ) / (n : ℝ))) +
          D * (∑ n ∈ B, nativeLambdaTwo n) := by
        rw [Finset.mul_sum, Finset.mul_sum]
      _ = _ := by rw [hBrec, hBmass]
''')

repl(
'''  rw [hGexpand, hBexpand] at hbound
  have hrecSplit := nativeLambdaTwoRecipSplit N beta
  have hmassSplit := nativeLambdaTwoMassSplit N beta
  nlinarith
''',
'''  rw [hGexpand, hBexpand] at hbound
  have hrecSplit := nativeLambdaTwoRecipSplit N beta
  have hmassSplit := nativeLambdaTwoMassSplit N beta
  calc
    nativeLambdaTwoErrorMass N ≤
        beta * ((N : ℝ) * nativeLambdaTwoGoodRecipMass N beta) +
          D * (∑ n ∈ nativePNTGoodFiberSet N beta, nativeLambdaTwo n) +
          (alpha * ((N : ℝ) *
            (∑ n ∈ (Finset.Icc 1 N).filter
              (fun n => ¬ |nativePNTError (N / n)| ≤
                beta * ((N : ℝ) / (n : ℝ))),
              nativeLambdaTwo n / (n : ℝ))) +
            D * (∑ n ∈ (Finset.Icc 1 N).filter
              (fun n => ¬ |nativePNTError (N / n)| ≤
                beta * ((N : ℝ) / (n : ℝ))), nativeLambdaTwo n)) := hbound
    _ = alpha * (N : ℝ) * nativeLambdaTwoRecipMass N -
        (alpha - beta) * (N : ℝ) * nativeLambdaTwoGoodRecipMass N beta +
        D * nativeLambdaTwoSummatory N := by
      rw [← hrecSplit, ← hmassSplit]
      ring
''')

p.write_text(s)
