from pathlib import Path

p = Path('RHLean/Analysis/NativePNTErrorMass.lean')
s = p.read_text()
old = '''/-- The log-factorial floor term is at most linear in absolute value. -/
theorem nativeLogFactorial_sub_main_abs_le
    (N : ℕ) (hN : 1 ≤ N) :
    |Real.log ((Nat.factorial N : ℕ) : ℝ) -
      (N : ℝ) * Real.log N| ≤ (N : ℝ) := by
  have hlo := nativeLogFactorial_lower N hN
  have hup := nativeLogFactorial_upper N hN
  rw [abs_le]
  constructor <;> linarith
'''
new = '''/-- The sharp factorial remainder implies the cruder linear bound centered
at `N log N`, which is the form used by the absolute Selberg recurrence. -/
theorem nativeLogFactorial_sub_Nlog_abs_le
    (N : ℕ) (hN : 1 ≤ N) :
    |Real.log ((Nat.factorial N : ℕ) : ℝ) -
      (N : ℝ) * Real.log N| ≤ (N : ℝ) := by
  have hsharp := nativeLogFactorial_sub_main_abs_le N hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have hlogle := Real.log_le_sub_one_of_pos hNpos
  have hNm1 : 0 ≤ (N : ℝ) - 1 := by
    exact_mod_cast hN
  have hrearrange :
      Real.log ((Nat.factorial N : ℕ) : ℝ) - (N : ℝ) * Real.log N =
        (Real.log ((Nat.factorial N : ℕ) : ℝ) -
          ((N : ℝ) * Real.log N - (N : ℝ) + 1)) - ((N : ℝ) - 1) := by
    ring
  rw [hrearrange]
  calc
    |(Real.log ((Nat.factorial N : ℕ) : ℝ) -
        ((N : ℝ) * Real.log N - (N : ℝ) + 1)) - ((N : ℝ) - 1)| ≤
      |Real.log ((Nat.factorial N : ℕ) : ℝ) -
        ((N : ℝ) * Real.log N - (N : ℝ) + 1)| + |(N : ℝ) - 1| :=
        abs_sub _ _
    _ = |Real.log ((Nat.factorial N : ℕ) : ℝ) -
        ((N : ℝ) * Real.log N - (N : ℝ) + 1)| + ((N : ℝ) - 1) := by
      rw [abs_of_nonneg hNm1]
    _ ≤ Real.log N + ((N : ℝ) - 1) := add_le_add_right hsharp _
    _ ≤ (N : ℝ) := by linarith
'''
assert old in s, 'factorial corollary target not found'
s = s.replace(old, new, 1)
s = s.replace(
    '  have hfac := nativeLogFactorial_sub_main_abs_le N (by omega)\n',
    '  have hfac := nativeLogFactorial_sub_Nlog_abs_le N (by omega)\n',
    1,
)
p.write_text(s)