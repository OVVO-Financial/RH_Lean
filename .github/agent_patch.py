from pathlib import Path

p = Path('RHLean/Analysis/NativePNTErdosContraction.lean')
s = p.read_text()
old = '''  have hKhalf : 96 / eps + 1 < (K : ℝ) / 2 := by
    dsimp [x] at hxK
    nlinarith
'''
new = '''  have hKhalf : 96 / eps + 1 < (K : ℝ) / 2 := by
    dsimp [x] at hxK
    have hhalf := (mul_lt_mul_right (show (0 : ℝ) < 1 / 2 by norm_num)).2 hxK
    convert hhalf using 1 <;> ring
'''
assert old in s
s = s.replace(old, new, 1)
p.write_text(s)
