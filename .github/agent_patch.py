from pathlib import Path

p = Path('RHLean/Analysis/NativePNTErdosContraction.lean')
s = p.read_text()

old = '''  calc
    Λ n ≤ ∑ d ∈ n.divisors, Λ d :=
      Finset.single_le_sum
        (fun d _hd => ArithmeticFunction.vonMangoldt_nonneg) hnmem
    _ = Real.log (n : ℝ) := ArithmeticFunction.vonMangoldt_sum
'''
new = '''  calc
    Λ n ≤ ∑ d ∈ n.divisors, Λ d := by
      exact Finset.single_le_sum
        (s := n.divisors) (f := fun d => Λ d)
        (fun d _hd => ArithmeticFunction.vonMangoldt_nonneg) hnmem
    _ = Real.log (n : ℝ) := ArithmeticFunction.vonMangoldt_sum
'''
assert old in s, 'von Mangoldt single term block not found'
s = s.replace(old, new, 1)

old = '''  | succ B hAB ih =>
      rw [Finset.sum_Icc_succ_top (by omega : A ≤ B + 1), ih, harmonic_succ]
      push_cast
      ring
'''
new = '''  | succ B hAB ih =>
      rw [Finset.sum_Icc_succ_top (by omega : A ≤ B + 1), ih, harmonic_succ]
      push_cast
      ring_nf
'''
assert old in s, 'harmonic succ block not found'
s = s.replace(old, new, 1)

old = '''  have hlo := log_add_one_le_harmonic (B + 1)
  have hup := harmonic_le_one_add_log A
  push_cast at hlo hup ⊢
  linarith
'''
new = '''  have hlo := log_add_one_le_harmonic (B + 1)
  have hup := harmonic_le_one_add_log A
  push_cast at hlo hup ⊢
  have hcast : ((B + 2 : ℕ) : ℝ) = (B : ℝ) + 1 + 1 := by
    push_cast
    ring
  rw [hcast]
  linarith
'''
assert old in s, 'reciprocal log lower block not found'
s = s.replace(old, new, 1)

s = s.replace(
    'one_le_pow₀ (by norm_num : 0 ≤ (2 : ℕ))',
    'one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 2)')

old = '''  have hspos : (0 : ℝ) < (((n + 1 : ℕ) : ℝ)) := by positivity
  have herr := haway n hn
  rw [abs_of_nonneg (hsign n hn)] at herr
  calc
    ε * (1 / (((n + 1 : ℕ) : ℝ))) =
        (ε * (n : ℝ)) / ((n : ℝ) * (((n + 1 : ℕ) : ℝ))) := by
      field_simp [ne_of_gt hnpos, ne_of_gt hspos]
      ring
    _ ≤ nativePNTError n / ((n : ℝ) * (((n + 1 : ℕ) : ℝ))) :=
      div_le_div_of_nonneg_right herr (mul_nonneg hnpos.le hspos.le)
'''
new = '''  have hspos : (0 : ℝ) < (((n + 1 : ℕ) : ℝ)) := by positivity
  have herr := haway n hn
  rw [abs_of_nonneg (hsign n hn)] at herr
  push_cast at hspos ⊢
  calc
    ε * (1 / ((n : ℝ) + 1)) =
        (ε * (n : ℝ)) / ((n : ℝ) * ((n : ℝ) + 1)) := by
      field_simp [ne_of_gt hnpos]
    _ ≤ nativePNTError n / ((n : ℝ) * ((n : ℝ) + 1)) :=
      div_le_div_of_nonneg_right herr (mul_nonneg hnpos.le hspos.le)
'''
assert old in s, 'positive weighted interval block not found'
s = s.replace(old, new, 1)

old = '''  have hspos : (0 : ℝ) < (((n + 1 : ℕ) : ℝ)) := by positivity
  have herr := haway n hn
  rw [abs_of_nonpos (hsign n hn)] at herr
  calc
    ε * (1 / (((n + 1 : ℕ) : ℝ))) =
        (ε * (n : ℝ)) / ((n : ℝ) * (((n + 1 : ℕ) : ℝ))) := by
      field_simp [ne_of_gt hnpos, ne_of_gt hspos]
      ring
    _ ≤ (-nativePNTError n) / ((n : ℝ) * (((n + 1 : ℕ) : ℝ))) :=
      div_le_div_of_nonneg_right herr (mul_nonneg hnpos.le hspos.le)
    _ = -(nativePNTError n / ((n : ℝ) * (((n + 1 : ℕ) : ℝ)))) := by ring
'''
new = '''  have hspos : (0 : ℝ) < (((n + 1 : ℕ) : ℝ)) := by positivity
  have herr := haway n hn
  rw [abs_of_nonpos (hsign n hn)] at herr
  push_cast at hspos ⊢
  calc
    ε * (1 / ((n : ℝ) + 1)) =
        (ε * (n : ℝ)) / ((n : ℝ) * ((n : ℝ) + 1)) := by
      field_simp [ne_of_gt hnpos]
    _ ≤ (-nativePNTError n) / ((n : ℝ) * ((n : ℝ) + 1)) :=
      div_le_div_of_nonneg_right herr (mul_nonneg hnpos.le hspos.le)
    _ = -(nativePNTError n / ((n : ℝ) * ((n : ℝ) + 1))) := by ring
'''
assert old in s, 'negative weighted interval block not found'
s = s.replace(old, new, 1)

old = '''  have heq :
      2 * ((b : ℝ) - (a : ℝ)) + 550 * (a : ℝ) / Real.log (a : ℝ) =
        (2 * ((b : ℝ) - (a : ℝ)) * Real.log (a : ℝ) + 550 * (a : ℝ)) /
          Real.log (a : ℝ) := by
    field_simp [ne_of_gt hlogpos]
    ring
'''
new = '''  have heq :
      2 * ((b : ℝ) - (a : ℝ)) + 550 * (a : ℝ) / Real.log (a : ℝ) =
        (2 * ((b : ℝ) - (a : ℝ)) * Real.log (a : ℝ) + 550 * (a : ℝ)) /
          Real.log (a : ℝ) := by
    field_simp [ne_of_gt hlogpos]
'''
assert old in s, 'gap tail division identity block not found'
s = s.replace(old, new, 1)

old = '''      _ ≤ (A : ℝ) / 8 := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hε1 (by positivity)) (by norm_num)
      _ ≤ (A : ℝ) := by nlinarith
'''
new = '''      _ ≤ (A : ℝ) / 8 := by
        have hmulA : ε * (A : ℝ) ≤ 1 * (A : ℝ) :=
          mul_le_mul_of_nonneg_right hε1 (by positivity)
        nlinarith
      _ ≤ (A : ℝ) := by nlinarith
'''
assert old in s, 'epsilon A comparison block not found'
s = s.replace(old, new, 1)

old = '''  · have : -ε * ((A + h : ℕ) : ℝ) ≤ nativePNTError (A + h) := by
      push_cast
      nlinarith [hlowerStep, hsmall'.1]
    exact this
'''
new = '''  · have hlow : -ε * ((A + h : ℕ) : ℝ) ≤ nativePNTError (A + h) := by
      push_cast
      nlinarith [hlowerStep, hsmall'.1]
    convert hlow using 1 <;> ring
'''
assert old in s, 'good interval lower abs block not found'
s = s.replace(old, new, 1)

old = '''  rw [nativeLambdaTwoSummatory_sub_eq_interval A B hAB]
  unfold nativeLambdaTwoRecipIntervalMass
  rw [← Finset.sum_div]
  apply Finset.sum_le_sum
'''
new = '''  rw [nativeLambdaTwoSummatory_sub_eq_interval A B hAB]
  unfold nativeLambdaTwoRecipIntervalMass
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
'''
assert old in s, 'Lambda2 reciprocal interval sum-div block not found'
s = s.replace(old, new, 1)

p.write_text(s)
