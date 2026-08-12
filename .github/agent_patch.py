from pathlib import Path

p = Path('RHLean/Analysis/NativePNTErdosContraction.lean')
s = p.read_text()

repls = [
('''      have hsum : (E + j * L + K + 2) * 4 ≤ q := by
        convert hsum0 using 1 <;> ring
      exact hsum
''',
 '''      have hsum : (E + j * L + K + 2) * 4 ≤ q := by
        have hnorm :
            (E + j * L + K + 2) * 4 = 4 * ((E + K + 2) + j * L) := by
          ring
        rw [hnorm]
        exact hsum0
      exact hsum
'''),
('''  have hJtwo : 2 ≤ J := by
    dsimp [J]
    apply (Nat.le_div_iff_mul_le hdpos).2
    convert hqJL using 1 <;> ring
''',
 '''  have hJtwo : 2 ≤ J := by
    dsimp [J]
    apply (Nat.le_div_iff_mul_le hdpos).2
    have hnorm : 2 * (8 * L) = 16 * L := by ring
    rw [hnorm]
    exact hqJL
'''),
('''  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : 0 ≤ (N : ℝ) := by positivity
  rw [abs_div, abs_of_nonneg hN0]
''',
 '''  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : 0 ≤ (N : ℝ) := by positivity
  change |nativePNTError N| / (N : ℝ) = |nativePNTError N / (N : ℝ)|
  rw [abs_div, abs_of_nonneg hN0]
'''),
]
for old, new in repls:
    assert old in s, old
    s = s.replace(old, new, 1)

p.write_text(s)
