from pathlib import Path

p = Path('RHLean/Analysis/NativePNTErdosContraction.lean')
s = p.read_text()
old = '''        nativeLambdaTwoSummatory 3 ≤
            2 * (3 : ℝ) * Real.log 3 +
              (2 * (Real.log 4 + 2) + 172) * (3 : ℝ) := by
          linarith [h3.2]
'''
new = '''        nativeLambdaTwoSummatory 3 ≤
            2 * (3 : ℝ) * Real.log 3 +
              (2 * (Real.log 4 + 2) + 172) * (3 : ℝ) := by
          have h := (sub_le_iff_le_add.mp h3.2)
          simpa [add_comm] using h
'''
assert s.count(old) == 1
s = s.replace(old, new, 1)
p.write_text(s)
