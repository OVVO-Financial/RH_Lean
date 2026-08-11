from pathlib import Path

p = Path('RHLean/Analysis/NativePNTSummatorySelberg.lean')
s = p.read_text()

reps = [
    ("    (N d : ℕ) (hd : 1 ≤ d) :\n", "    (N d : ℕ) (_hd : 1 ≤ d) :\n"),
    ("""        have hident :
            (Real.sqrt ((N + 1 : ℕ) : ℝ) - Real.sqrt (N : ℝ)) *
                (Real.sqrt ((N + 1 : ℕ) : ℝ) + Real.sqrt (N : ℝ)) = 1 := by
          push_cast at hsSSq
          nlinarith [hsNSq, hsSSq]
""", """        have hident :
            (Real.sqrt ((N + 1 : ℕ) : ℝ) - Real.sqrt (N : ℝ)) *
                (Real.sqrt ((N + 1 : ℕ) : ℝ) + Real.sqrt (N : ℝ)) = 1 := by
          calc
            (Real.sqrt ((N + 1 : ℕ) : ℝ) - Real.sqrt (N : ℝ)) *
                (Real.sqrt ((N + 1 : ℕ) : ℝ) + Real.sqrt (N : ℝ)) =
                (Real.sqrt ((N + 1 : ℕ) : ℝ)) ^ 2 -
                  (Real.sqrt (N : ℝ)) ^ 2 := by ring
            _ = ((N + 1 : ℕ) : ℝ) - (N : ℝ) := by rw [hsSSq, hsNSq]
            _ = 1 := by push_cast; ring
"""),
    ("        simpa using Real.sqrt_div (show 0 ≤ (N : ℝ) by positivity) (d : ℝ)\n",
     "        exact Real.sqrt_div (show 0 ≤ (N : ℝ) by positivity) (d : ℝ)\n"),
    ("""      _ = 32 * (N : ℝ) := by
        rw [show Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) from
          Real.mul_self_sqrt (by positivity)]
        ring
""", """      _ = 32 * (N : ℝ) := by
        calc
          (16 * Real.sqrt (N : ℝ)) * (2 * Real.sqrt (N : ℝ)) =
              32 * (Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ)) := by ring
          _ = 32 * (N : ℝ) := by
            rw [Real.mul_self_sqrt (show 0 ≤ (N : ℝ) by positivity)]
"""),
    ("""      have hmf :
          |(ArithmeticFunction.moebius d : ℝ)| *
              Int.fract ((N : ℝ) / (d : ℝ)) ≤ 1 := by
        have := mul_le_mul hmu hfr1 hfr0 (abs_nonneg (ArithmeticFunction.moebius d : ℝ))
        norm_num at this ⊢
        exact this
      rw [abs_mul, abs_mul, abs_of_nonneg hfr0, abs_of_nonneg (sq_nonneg _)]
      simpa using mul_le_mul_of_nonneg_right hmf
        (sq_nonneg (Real.log ((N / d : ℕ) : ℝ)))
""", """      have hmf :
          |(ArithmeticFunction.moebius d : ℝ)| *
              Int.fract ((N : ℝ) / (d : ℝ)) ≤ 1 := by
        calc
          |(ArithmeticFunction.moebius d : ℝ)| *
              Int.fract ((N : ℝ) / (d : ℝ)) ≤
              1 * Int.fract ((N : ℝ) / (d : ℝ)) :=
            mul_le_mul_of_nonneg_right hmu hfr0
          _ ≤ 1 := by simpa using hfr1
      simp only [abs_mul, abs_of_nonneg hfr0, abs_of_nonneg (sq_nonneg _)]
      exact mul_le_mul_of_nonneg_right hmf
        (sq_nonneg (Real.log ((N / d : ℕ) : ℝ)))
"""),
    ("""      have hmf :
          |(ArithmeticFunction.moebius d : ℝ)| *
              Int.fract ((N : ℝ) / (d : ℝ)) ≤ 1 := by
        have := mul_le_mul hmu hfr1 hfr0 (abs_nonneg (ArithmeticFunction.moebius d : ℝ))
        norm_num at this ⊢
        exact this
      rw [abs_mul, abs_mul, abs_of_nonneg hfr0, abs_of_nonneg hlog0]
      simpa using mul_le_mul_of_nonneg_right hmf hlog0
""", """      have hmf :
          |(ArithmeticFunction.moebius d : ℝ)| *
              Int.fract ((N : ℝ) / (d : ℝ)) ≤ 1 := by
        calc
          |(ArithmeticFunction.moebius d : ℝ)| *
              Int.fract ((N : ℝ) / (d : ℝ)) ≤
              1 * Int.fract ((N : ℝ) / (d : ℝ)) :=
            mul_le_mul_of_nonneg_right hmu hfr0
          _ ≤ 1 := by simpa using hfr1
      simp only [abs_mul, abs_of_nonneg hfr0, abs_of_nonneg hlog0]
      exact mul_le_mul_of_nonneg_right hmf hlog0
"""),
    ("""          ((N / d : ℕ) * (Real.log (N / d)) ^ 2 -
            2 * (N / d : ℕ) * Real.log (N / d) + 2 * (N / d : ℕ))) =
""", """          ((N / d : ℕ) * (Real.log ((N / d : ℕ) : ℝ)) ^ 2 -
            2 * (N / d : ℕ) * Real.log ((N / d : ℕ) : ℝ) + 2 * (N / d : ℕ))) =
"""),
    ("        exact mul_le_mul hmu herr (abs_nonneg _) (by positivity)\n",
     "        simpa using\n          (mul_le_mul hmu herr (abs_nonneg _)\n            (show (0 : ℝ) ≤ 1 by norm_num))\n"),
    ("  intro d _hd\n  ring\n\nprivate theorem nativeMobiusLogSquareMainMass_eq\n",
     "  intro d _hd\n  simpa [mul_comm]\n\nprivate theorem nativeMobiusLogSquareMainMass_eq\n"),
    ("        rw [abs_neg]\n        norm_num\n        ring\n",
     "        rw [abs_neg]\n        norm_num <;> ring\n"),
]

for old, new in reps:
    if old not in s:
        raise SystemExit('target not found:\n' + old[:220])
    s = s.replace(old, new, 1)

p.write_text(s)
