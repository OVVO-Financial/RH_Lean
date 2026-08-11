from pathlib import Path

p = Path('RHLean/Analysis/NativePNTErdosContraction.lean')
s = p.read_text()

old = '''  | succ B hAB ih =>
      rw [Finset.sum_Icc_succ_top (by omega : A ≤ B + 1), ih, harmonic_succ]
      push_cast
      ring_nf
'''
new = '''  | succ B hAB ih =>
      rw [Finset.sum_Icc_succ_top (by omega : A ≤ B + 1), ih,
        harmonic_succ, harmonic_succ]
      push_cast
      ring
'''
assert old in s, 'harmonic telescoping block not found'
s = s.replace(old, new, 1)

old = '''  push_cast at hlo hup ⊢
  have hcast : ((B + 2 : ℕ) : ℝ) = (B : ℝ) + 1 + 1 := by
    push_cast
    ring
  rw [hcast]
  linarith
'''
new = '''  push_cast at hlo hup ⊢
  have hlo' : Real.log ((B : ℝ) + 2) ≤ (harmonic (B + 1) : ℝ) := by
    convert hlo using 1 <;> ring
  linarith
'''
assert old in s, 'reciprocal interval log block not found'
s = s.replace(old, new, 1)

old = '''    rw [Nat.cast_mul, Nat.cast_pow]
    rw [Real.log_mul (ne_of_gt hApos) (ne_of_gt hpowpos), Real.log_pow]
'''
new = '''    rw [Nat.cast_mul, Nat.cast_pow]
    rw [Real.log_mul (ne_of_gt hApos) (by positivity), Real.log_pow]
'''
assert old in s, 'dyadic product log block not found'
s = s.replace(old, new, 1)

old = '''    intro n hn
    exact le_of_not_gt (hno n hn)
'''
new = '''    intro n hn
    exact hno n hn
'''
assert old in s, 'haway conversion block not found'
s = s.replace(old, new, 1)

s = s.replace('(mul_nonneg (by exact_mod_cast hn1) (by positivity))',
              '(mul_nonneg (by positivity) (by positivity))')

p.write_text(s)
