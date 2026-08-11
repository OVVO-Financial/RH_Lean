from pathlib import Path

p = Path('RHLean/Analysis/NativePNTErdosContraction.lean')
s = p.read_text()

old = '''  push_cast at hlo hup ⊢
  have hlo' : Real.log ((B : ℝ) + 2) ≤ (harmonic (B + 1) : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_one, add_assoc] using hlo
  linarith
'''
new = '''  push_cast at hlo hup ⊢
  norm_num at hlo
  linarith
'''
assert old in s, 'log lower normalization block not found'
s = s.replace(old, new, 1)

old = '''    exact hlow
'''
new = '''    simpa only [neg_mul] using hlow
'''
assert old in s, 'forward interval negation block not found'
s = s.replace(old, new, 1)

p.write_text(s)
