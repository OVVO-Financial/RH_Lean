from pathlib import Path

p = Path('RHLean/Analysis/NativePNTErdosContraction.lean')
s = p.read_text()
old = '''    exact (mul_le_mul_iff_right₀ hLsq).mp
      (show |nativePNTError N| * L ^ 2 ≤
        ((alpha - delta) * (N : ℝ)) * L ^ 2 by
          simpa [mul_assoc] using hsq)
'''
new = '''    have hsq' :
        L ^ 2 * |nativePNTError N| ≤
          L ^ 2 * ((alpha - delta) * (N : ℝ)) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hsq
    exact (mul_le_mul_iff_left₀ hLsq).mp hsq'
'''
assert s.count(old) == 1
s = s.replace(old, new, 1)
p.write_text(s)
