from pathlib import Path

p = Path('RHLean/Analysis/NativePNTErdosContraction.lean')
s = p.read_text()
old = '''  have hKhalf : 96 / eps + 1 < (K : ℝ) / 2 := by
    dsimp [x] at hxK
    have hhalf := (mul_lt_mul_right (show (0 : ℝ) < 1 / 2 by norm_num)).2 hxK
    convert hhalf using 1 <;> ring
'''
new = '''  have hKhalf : 96 / eps + 1 < (K : ℝ) / 2 := by
    dsimp [x] at hxK
    have hhalf :=
      (mul_lt_mul_iff_left₀ (show (0 : ℝ) < 1 / 2 by norm_num)).2 hxK
    convert hhalf using 1 <;> ring
'''
assert old in s
s = s.replace(old, new, 1)
old2 = '''  have hcancel : (eps / 4) * (96 / eps) = (24 : ℝ) := by
    field_simp [ne_of_gt heps]
    <;> ring
'''
new2 = '''  have hcancel : (eps / 4) * (96 / eps) = (24 : ℝ) := by
    (field_simp [ne_of_gt heps]; ring)
'''
assert old2 in s
s = s.replace(old2, new2, 1)
p.write_text(s)
