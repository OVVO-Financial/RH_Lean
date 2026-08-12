from pathlib import Path

p = Path('RHLean/Analysis/NativePNTSquarePrefixGoodMassRate.lean')
s = p.read_text()

old = '''  have hSupper : (S : ℝ) ≤ 200 / eps := by
    dsimp [S, L]
    push_cast
    nlinarith [hKupper]
'''
new = '''  have hSupper : (S : ℝ) ≤ 200 / eps := by
    have htwo := mul_le_mul_of_nonneg_left hKupper (show (0 : ℝ) ≤ 2 by norm_num)
    dsimp [S, L]
    push_cast
    convert htwo using 1 <;> ring
'''
count = s.count(old)
assert count == 1, f'expected one hSupper block, found {count}'
s = s.replace(old, new, 1)
p.write_text(s)

for i, line in enumerate(s.splitlines(), start=1):
    if 'norm_num' in line:
        print(f'norm_num:{i}:{line}')
