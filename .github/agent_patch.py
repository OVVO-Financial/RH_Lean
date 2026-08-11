from pathlib import Path

p = Path('RHLean/Analysis/NativePNTSummatorySelberg.lean')
s = p.read_text()

reps = [
    ("""      simp only [abs_mul, abs_of_nonneg hfr0, abs_of_nonneg (sq_nonneg _)]
      exact mul_le_mul_of_nonneg_right hmf
        (sq_nonneg (Real.log ((N / d : ℕ) : ℝ)))
""", """      have hlog2 : 0 ≤ (Real.log ((N / d : ℕ) : ℝ)) ^ 2 :=
        sq_nonneg (Real.log ((N / d : ℕ) : ℝ))
      rw [abs_mul, abs_mul, abs_of_nonneg hfr0, abs_of_nonneg hlog2]
      simpa using mul_le_mul_of_nonneg_right hmf hlog2
"""),
    ("""      simp only [abs_mul, abs_of_nonneg hfr0, abs_of_nonneg hlog0]
      exact mul_le_mul_of_nonneg_right hmf hlog0
""", """      rw [abs_mul, abs_mul, abs_of_nonneg hfr0, abs_of_nonneg hlog0]
      simpa using mul_le_mul_of_nonneg_right hmf hlog0
"""),
    ("""      intro d _hd
      push_cast
      ring
""", """      intro d _hd
      ring
"""),
    ("""  intro d _hd
  simpa [mul_comm]

private theorem nativeMobiusLogSquareMainMass_eq
""", """  intro d _hd
  ring

private theorem nativeMobiusLogSquareMainMass_eq
"""),
    ("""        rw [abs_neg]
        norm_num <;> ring
""", """        rw [abs_neg]
        norm_num
"""),
]

for old, new in reps:
    if old not in s:
        raise SystemExit('target not found:\n' + old[:220])
    s = s.replace(old, new, 1)

p.write_text(s)
