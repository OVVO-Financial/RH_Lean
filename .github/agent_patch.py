from pathlib import Path

p = Path('RHLean/Analysis/NativePNTErrorMass.lean')
s = p.read_text()

s = s.replace(
'''  · have h := nativePNTError_abs_log_le_weighted N hN3
    have hNR0 : 0 ≤ (N : ℝ) := by positivity
    calc
''',
'''  · have h := nativePNTError_abs_log_le_weighted N hN3
    calc
''',
1,
)
s = s.replace(
'''        gcongr
        exact mul_le_mul_of_nonneg_right nativePNTFirstErrorConstant_le_thousand hNR0
''',
'''        gcongr
        exact nativePNTFirstErrorConstant_le_thousand
''',
1,
)
s = s.replace(
'''    Real.log N ≤ Real.log d + Real.log (N / d) + 1 := by
''',
'''    Real.log (N : ℝ) ≤
      Real.log (d : ℝ) + Real.log ((N / d : ℕ) : ℝ) + 1 := by
''',
1,
)
s = s.replace(
'''  have hdivmod : N / d * d + N % d = N := Nat.div_add_mod N d
''',
'''  have hdivmod : d * (N / d) + N % d = N := Nat.div_add_mod N d
''',
1,
)
s = s.replace(
'''      N = N / d * d + N % d := hdivmod.symm
      _ < N / d * d + d := Nat.add_lt_add_left hrem _
      _ = d * (N / d + 1) := by ring
''',
'''      N = d * (N / d) + N % d := hdivmod.symm
      _ < d * (N / d) + d := Nat.add_lt_add_left hrem _
      _ = d * (N / d + 1) := by ring
''',
1,
)
s = s.replace(
'''  have hqsuccR0 : (((N / d + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hprodlog :
      Real.log ((d * (N / d + 1) : ℕ) : ℝ) =
        Real.log (d : ℝ) + Real.log ((N / d + 1 : ℕ) : ℝ) := by
    push_cast
    rw [Real.log_mul hdR0 hqsuccR0]
''',
'''  have hprodlog :
      Real.log ((d * (N / d + 1) : ℕ) : ℝ) =
        Real.log (d : ℝ) + Real.log ((N / d + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    rw [Real.log_mul hdR0 (by positivity)]
''',
1,
)
# Every occurrence below this point means the logarithm of the integer floor
# quotient, not the logarithm of the real quotient.
s = s.replace('Real.log (N / d)', 'Real.log ((N / d : ℕ) : ℝ)')

old = '''      _ ≤ nativeLambdaLogErrorMass N + nativeLambdaConvolutionErrorMass N +
          (1000 + (Real.log 4 + 3)) * ((N : ℝ) * Real.log N) := by
        gcongr
        · exact add_nonneg (by norm_num) hC0
        · exact nativeLambdaFloorMass_le_Nlog N hN
      _ ≤ nativeLambdaLogErrorMass N + nativeLambdaConvolutionErrorMass N +
          1006 * ((N : ℝ) * Real.log N) := by
        gcongr
        have : 1000 + (Real.log 4 + 3) ≤ (1006 : ℝ) := by linarith
        exact mul_le_mul_of_nonneg_right this (mul_nonneg (by positivity) hlog0)
'''
new = '''      _ ≤ nativeLambdaLogErrorMass N + nativeLambdaConvolutionErrorMass N +
          (1000 + (Real.log 4 + 3)) * ((N : ℝ) * Real.log N) := by
        have hcoef : 0 ≤ 1000 + (Real.log 4 + 3) :=
          add_nonneg (by norm_num) hC0
        exact add_le_add_left
          (mul_le_mul_of_nonneg_left (nativeLambdaFloorMass_le_Nlog N hN) hcoef)
          (nativeLambdaLogErrorMass N + nativeLambdaConvolutionErrorMass N)
      _ ≤ nativeLambdaLogErrorMass N + nativeLambdaConvolutionErrorMass N +
          1006 * ((N : ℝ) * Real.log N) := by
        have hcoef : 1000 + (Real.log 4 + 3) ≤ (1006 : ℝ) := by
          linarith [hC6]
        have hNlog0 : 0 ≤ (N : ℝ) * Real.log N :=
          mul_nonneg (by positivity) hlog0
        exact add_le_add_left
          (mul_le_mul_of_nonneg_right hcoef hNlog0)
          (nativeLambdaLogErrorMass N + nativeLambdaConvolutionErrorMass N)
'''
assert old in s, 'floor-mass coefficient block not found'
s = s.replace(old, new, 1)

old = '''    _ ≤ nativeLambdaLogErrorMass N + nativeLambdaConvolutionErrorMass N +
          2000 * (N : ℝ) * Real.log N := by
      gcongr
      exact mul_le_mul_of_nonneg_right (by norm_num : (1006 : ℝ) ≤ 2000)
        (mul_nonneg (by positivity) hlog0)
'''
new = '''    _ ≤ nativeLambdaLogErrorMass N + nativeLambdaConvolutionErrorMass N +
          2000 * (N : ℝ) * Real.log N := by
      have hNlog0 : 0 ≤ (N : ℝ) * Real.log N :=
        mul_nonneg (by positivity) hlog0
      have hcoef : 1006 * (N : ℝ) * Real.log N ≤
          2000 * (N : ℝ) * Real.log N := by
        calc
          1006 * (N : ℝ) * Real.log N = 1006 * ((N : ℝ) * Real.log N) := by ring
          _ ≤ 2000 * ((N : ℝ) * Real.log N) :=
            mul_le_mul_of_nonneg_right (by norm_num) hNlog0
          _ = 2000 * (N : ℝ) * Real.log N := by ring
      exact add_le_add_left hcoef
        (nativeLambdaLogErrorMass N + nativeLambdaConvolutionErrorMass N)
'''
assert old in s, 'final coefficient block not found'
s = s.replace(old, new, 1)

p.write_text(s)