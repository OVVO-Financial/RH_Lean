from pathlib import Path

p = Path('RHLean/Analysis/NativePNTSquarePrefixGoodMassRate.lean')
s = p.read_text()
old = '''  have hSupper : (S : ℝ) ≤ 200 / eps := by
    have htwo := mul_le_mul_of_nonneg_left hKupper (show (0 : ℝ) ≤ 2 by norm_num)
    dsimp [S, L]
    push_cast
    convert htwo using 1 <;> ring
'''
new = '''  have hSupper : (S : ℝ) ≤ 200 / eps := by
    dsimp [S, L]
    push_cast
    exact hKupper
'''
assert s.count(old) == 1
p.write_text(s.replace(old, new, 1))
