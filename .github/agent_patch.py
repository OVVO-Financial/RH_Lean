from pathlib import Path

p = Path('RHLean/Analysis/NativePNTErdosContraction.lean')
s = p.read_text()

repls = [
('''private lemma nativePNT_shell_step_lt (E K i : ℕ) :
    E + i * (K + 2) + K + 1 < E + (i + 1) * (K + 2) := by
  omega
''',
 '''private lemma nativePNT_shell_step_lt (E K i : ℕ) :
    E + i * (K + 2) + K + 1 < E + (i + 1) * (K + 2) := by
  calc
    E + i * (K + 2) + K + 1 < E + i * (K + 2) + K + 2 := by omega
    _ = E + (i + 1) * (K + 2) := by ring
'''),
('''    field_simp [ne_of_gt hL]
    <;> ring
''',
 '''    field_simp [ne_of_gt hL]
    ring
'''),
('''  have hlogNupper : Real.log (N : ℝ) ≤ 2 * (q : ℝ) := by
    have hpowpos : (0 : ℝ) < ((2 ^ (q + 1) : ℕ) : ℝ) := by positivity
    have hcast : (N : ℝ) ≤ ((2 ^ (q + 1) : ℕ) : ℝ) := by exact_mod_cast hNpow.le
    have hlogle := Real.log_le_log (by exact_mod_cast (show 0 < N by omega)) hcast
    have hlogpow : Real.log ((2 ^ (q + 1) : ℕ) : ℝ) =
        ((q + 1 : ℕ) : ℝ) * Real.log 2 := by
      rw [Nat.cast_pow, Real.log_pow]
    rw [hlogpow] at hlogle
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q by omega)
    have hmul := mul_le_mul_of_nonneg_left hlog2le (by positivity : (0 : ℝ) ≤ ((q + 1 : ℕ) : ℝ))
    push_cast at hmul
    nlinarith
  have hsq : (Real.log (N : ℝ)) ^ 2 ≤ 4 * (q : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (Real.log (N : ℝ) - 2 * (q : ℝ))]
''',
 '''  have hq1nat : 1 ≤ q := by omega
  have hlogNupper : Real.log (N : ℝ) ≤ 2 * (q : ℝ) :=
    nativePNT_log_upper_from_binary hN1 hq1nat hNpow hlog2le
  have hsq : (Real.log (N : ℝ)) ^ 2 ≤ 4 * (q : ℝ) ^ 2 := by
    nlinarith only [hlogNnonneg, hlogNupper,
      sq_nonneg (Real.log (N : ℝ) - 2 * (q : ℝ))]
'''),
('''    have h := mul_le_mul_of_nonneg_left hsq hcoef
    nlinarith
''',
 '''    calc
      eps * Real.log 2 / (16384 * (L : ℝ)) * (Real.log (N : ℝ)) ^ 2 ≤
          eps * Real.log 2 / (16384 * (L : ℝ)) * (4 * (q : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hsq hcoef
      _ = eps * Real.log 2 / (4096 * (L : ℝ)) * (q : ℝ) ^ 2 := by ring
'''),
]
for old, new in repls:
    assert old in s, old
    s = s.replace(old, new, 1)

anchor = '''/-- **Quadratic logarithmic density of good reciprocal fibres.**  For every
fixed `0 < eps <= 1`, the PNT2 good intervals supplied on separated dyadic
shells contribute a positive fixed multiple of `log^2 N` to the reciprocal
`Lambda_2` compensation mass.  This is the quantitative packing step that
closes the Selberg--Erdos contraction. -/
'''
helper = r'''private lemma nativePNT_log_upper_from_binary
    {N q : ℕ} (hN : 1 ≤ N) (hq : 1 ≤ q)
    (hNpow : N < 2 ^ (q + 1))
    (hlog2le : Real.log (2 : ℝ) ≤ 1) :
    Real.log (N : ℝ) ≤ 2 * (q : ℝ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have hcast : (N : ℝ) ≤ ((2 ^ (q + 1) : ℕ) : ℝ) := by
    exact_mod_cast hNpow.le
  have hlogle := Real.log_le_log hNpos hcast
  have hlogpow : Real.log ((2 ^ (q + 1) : ℕ) : ℝ) =
      ((q + 1 : ℕ) : ℝ) * Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  rw [hlogpow] at hlogle
  have hqreal : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hmul :
      ((q + 1 : ℕ) : ℝ) * Real.log 2 ≤ ((q + 1 : ℕ) : ℝ) * 1 :=
    mul_le_mul_of_nonneg_left hlog2le (by positivity)
  have hqsum : ((q + 1 : ℕ) : ℝ) ≤ 2 * (q : ℝ) := by
    push_cast
    linarith
  calc
    Real.log (N : ℝ) ≤ ((q + 1 : ℕ) : ℝ) * Real.log 2 := hlogle
    _ ≤ ((q + 1 : ℕ) : ℝ) * 1 := hmul
    _ = ((q + 1 : ℕ) : ℝ) := by ring
    _ ≤ 2 * (q : ℝ) := hqsum

'''
assert anchor in s
assert 'private lemma nativePNT_log_upper_from_binary' not in s
s = s.replace(anchor, helper + anchor, 1)

p.write_text(s)
