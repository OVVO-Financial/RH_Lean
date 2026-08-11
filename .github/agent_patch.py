from pathlib import Path

p = Path('RHLean/Analysis/NativePNTErdosContraction.lean')
s = p.read_text()

old = '''  | succ B hAB ih =>
      rw [Finset.sum_Icc_succ_top (by omega : A ≤ B + 1), ih,
        harmonic_succ, harmonic_succ]
      push_cast
      ring
'''
new = '''  | succ B hAB ih =>
      rw [Finset.sum_Icc_succ_top (by omega : A ≤ B + 1), ih]
      rw [show B + 2 = (B + 1) + 1 by omega, harmonic_succ (B + 1)]
      push_cast
      ring
'''
assert old in s, 'harmonic successor block not found'
s = s.replace(old, new, 1)

old = '''private theorem nativePNTRecipSuccInterval_log_lower
    (A B : ℕ) (hA : 1 ≤ A) (hAB : A ≤ B) :
'''
new = '''private theorem nativePNTRecipSuccInterval_log_lower
    (A B : ℕ) (_hA : 1 ≤ A) (hAB : A ≤ B) :
'''
assert old in s, 'log lower declaration not found'
s = s.replace(old, new, 1)

old = '''  push_cast at hlo hup ⊢
  have hlo' : Real.log ((B : ℝ) + 2) ≤ (harmonic (B + 1) : ℝ) := by
    convert hlo using 1 <;> ring
  linarith
'''
new = '''  push_cast at hlo hup ⊢
  have hlo' : Real.log ((B : ℝ) + 2) ≤ (harmonic (B + 1) : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_one, add_assoc] using hlo
  linarith
'''
assert old in s, 'log lower proof block not found'
s = s.replace(old, new, 1)

old = '''    rw [Nat.cast_mul, Nat.cast_pow]
    rw [Real.log_mul (ne_of_gt hApos) (by positivity), Real.log_pow]
'''
new = '''    rw [Nat.cast_mul, Nat.cast_pow]
    rw [Real.log_mul (ne_of_gt hApos) (by positivity), Real.log_pow]
    norm_num
'''
assert old in s, 'dyadic log product block not found'
s = s.replace(old, new, 1)

s = s.replace(
'''private theorem nativePNTWeightedErrorIntervalMass_lower_of_nonneg
    (A B : ℕ) (ε : ℝ) (hA : 1 ≤ A) (hAB : A ≤ B)
''',
'''private theorem nativePNTWeightedErrorIntervalMass_lower_of_nonneg
    (A B : ℕ) (ε : ℝ) (hA : 1 ≤ A) (_hAB : A ≤ B)
''', 1)
s = s.replace(
'''private theorem nativePNTWeightedErrorIntervalMass_neg_lower_of_nonpos
    (A B : ℕ) (ε : ℝ) (hA : 1 ≤ A) (hAB : A ≤ B)
''',
'''private theorem nativePNTWeightedErrorIntervalMass_neg_lower_of_nonpos
    (A B : ℕ) (ε : ℝ) (hA : 1 ≤ A) (_hAB : A ≤ B)
''', 1)

old = '''  · have hlow : -ε * ((A + h : ℕ) : ℝ) ≤ nativePNTError (A + h) := by
      push_cast
      nlinarith [hlowerStep, hsmall'.1]
    convert hlow using 1 <;> ring
'''
new = '''  · have hlow : -ε * ((A + h : ℕ) : ℝ) ≤ nativePNTError (A + h) := by
      push_cast
      nlinarith [hlowerStep, hsmall'.1]
    exact hlow
'''
assert old in s, 'forward interval lower block not found'
s = s.replace(old, new, 1)

p.write_text(s)
