from pathlib import Path

p = Path('RHLean/Analysis/NativePNTErdosContraction.lean')
s = p.read_text()

old = '''        _ ≤ alpha * (N : ℝ) * L ^ 2 - delta * (N : ℝ) * L ^ 2 :=
          add_le_add_left htail _
        _ = (alpha - delta) * (N : ℝ) * L ^ 2 := by ring
    have hLsq : 0 < L ^ 2 := sq_pos_of_pos hLpos
    have hcancel := (mul_le_mul_right hLsq).mp
      (show |nativePNTError N| * L ^ 2 ≤
        ((alpha - delta) * (N : ℝ)) * L ^ 2 by
          simpa [mul_assoc] using hsq)
    exact hcancel
'''
new = '''        _ ≤ alpha * (N : ℝ) * L ^ 2 - delta * (N : ℝ) * L ^ 2 := by
          simpa [sub_eq_add_neg] using
            (add_le_add_left htail (alpha * (N : ℝ) * L ^ 2))
        _ = (alpha - delta) * (N : ℝ) * L ^ 2 := by ring
    have hLsq : 0 < L ^ 2 := sq_pos_of_pos hLpos
    exact (mul_le_mul_iff_right₀ hLsq).mp
      (show |nativePNTError N| * L ^ 2 ≤
        ((alpha - delta) * (N : ℝ)) * L ^ 2 by
          simpa [mul_assoc] using hsq)
'''
assert s.count(old) == 1
s = s.replace(old, new, 1)
old2 = '''      exact hold.trans htarget
  simpa [delta]

end RHLean.Analysis
'''
new2 = '''      exact hold.trans htarget

end RHLean.Analysis
'''
assert s.count(old2) == 1
s = s.replace(old2, new2, 1)
p.write_text(s)
