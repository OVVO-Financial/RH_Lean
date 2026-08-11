from pathlib import Path

p = Path('RHLean/Analysis/NativePNTErrorMass.lean')
s = p.read_text()
start = s.index('/-- The sharp factorial remainder implies the cruder linear bound centered')
end = s.index('private theorem nativeLambdaErrorSum_abs_le', start)
new = '''/-- The elementary factorial bracket gives the cruder linear bound centered
at `N log N`, which is the form used by the absolute Selberg recurrence. -/
theorem nativeLogFactorial_sub_Nlog_abs_le
    (N : ℕ) (hN : 1 ≤ N) :
    |Real.log ((Nat.factorial N : ℕ) : ℝ) -
      (N : ℝ) * Real.log N| ≤ (N : ℝ) := by
  have hlo := nativeLogFactorial_lower N hN
  have hup := nativeLogFactorial_upper N hN
  rw [abs_le]
  constructor <;> linarith

'''
s = s[:start] + new + s[end:]
p.write_text(s)