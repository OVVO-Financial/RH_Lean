from pathlib import Path

p = Path('RHLean/Analysis/NativePNTAxer.lean')
s = p.read_text()

repls = [
('''      _ = 0 := by
        ext n
        simp [arithmeticLogWeight]
''',
 '''      _ = 0 := by
        ext n
        cases n with
        | zero => simp [arithmeticLogWeight]
        | succ n =>
            cases n with
            | zero => simp [arithmeticLogWeight]
            | succ n => simp [arithmeticLogWeight]
'''),
('''    _ = -((μ : ArithmeticFunction ℝ) * Λ) := by
        dsimp [zetaR]
        rw [ArithmeticFunction.coe_zeta_mul_coe_moebius]
        ring
''',
 '''    _ = -(((μ : ArithmeticFunction ℝ) * zetaR) *
          ((μ : ArithmeticFunction ℝ) * Λ)) := by ring
    _ = -((μ : ArithmeticFunction ℝ) * Λ) := by
        dsimp [zetaR]
        rw [ArithmeticFunction.coe_moebius_mul_coe_zeta]
        simp
'''),
('''    _ = -∑ n ∈ Finset.Icc 1 N,
        ((μ : ArithmeticFunction ℝ) * Λ) n := by
      rw [Finset.sum_neg_distrib]
      rfl
''',
 '''    _ = -∑ n ∈ Finset.Icc 1 N,
        ((μ : ArithmeticFunction ℝ) * Λ) n := by
      simp
'''),
('''      rw [hcard]
      push_cast
      ring
''',
 '''      rw [hcard]
      ring
'''),
('''      have h := abs_add (-1 : ℝ)
        (-(∑ d ∈ Finset.Icc 1 N,
          (μ : ArithmeticFunction ℝ) d * nativePNTError (N / d)))
      simpa [abs_neg] using h
''',
 '''      have h := abs_add_le (-1 : ℝ)
        (-(∑ d ∈ Finset.Icc 1 N,
          (μ : ArithmeticFunction ℝ) d * nativePNTError (N / d)))
      simpa [abs_neg] using h
'''),
('''        have hratio : (1 : ℝ) ≤ (N : ℝ) / (n : ℝ) := by
          rw [le_div_iff₀ (by exact_mod_cast hn1 : (0 : ℝ) < (n : ℝ))]
          exact_mod_cast hnN
''',
 '''        have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
        have hnNreal : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
        have hratio : (1 : ℝ) ≤ (N : ℝ) / (n : ℝ) := by
          rw [le_div_iff₀ hnpos]
          simpa using hnNreal
'''),
('''        rw [hcard]
        push_cast
''',
 '''        rw [hcard]
'''),
('''              Real.log ((N : ℝ) / (n : ℝ))| := abs_add _ _
''',
 '''              Real.log ((N : ℝ) / (n : ℝ))| := abs_add_le _ _
'''),
('''  · intro a ha
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hnonneg : 0 ≤ |nativeMertensSummatory N / (N : ℝ)| := abs_nonneg _
    linarith
''',
 '''  · intro a ha
    filter_upwards [] with N
    change a < |nativeMertensSummatory N / (N : ℝ)|
    exact ha.trans_le (abs_nonneg _)
'''),
('''    have hnorm :
        |nativeMertensSummatory N| / (N : ℝ) < b := by
      have hdiv := (div_le_iff₀ hlogpos).2 hraw
      have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
      have hlogne : Real.log (N : ℝ) ≠ 0 := ne_of_gt hlogpos
      have htarget :
          |nativeMertensSummatory N| / (N : ℝ) ≤
            alpha + (alpha + D + 2) / Real.log (N : ℝ) := by
        field_simp [hNne, hlogne] at hdiv ⊢
        nlinarith
      dsimp [alpha] at htarget
      linarith
    rw [abs_div, abs_of_pos hNpos]
    exact hnorm
''',
 '''    have hnorm :
        |nativeMertensSummatory N| / (N : ℝ) < b := by
      have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
      have hlogne : Real.log (N : ℝ) ≠ 0 := ne_of_gt hlogpos
      have htarget :
          |nativeMertensSummatory N| / (N : ℝ) ≤
            alpha + (alpha + D + 2) / Real.log (N : ℝ) := by
        field_simp [hNne, hlogne]
        nlinarith [hraw]
      dsimp [alpha] at htarget
      linarith
    change |nativeMertensSummatory N / (N : ℝ)| < b
    rw [abs_div, abs_of_pos hNpos]
    exact hnorm
'''),
]

for old, new in repls:
    assert old in s, old
    s = s.replace(old, new, 1)

p.write_text(s)
