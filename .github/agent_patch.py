from pathlib import Path

p = Path('RHLean/Analysis/NativePNTErdosContraction.lean')
s = p.read_text()
assert 'nativePNTError_good_forward_interval' not in s
marker = '\nend RHLean.Analysis\n'
assert marker in s
block = r'''

/-! ## Erdos PNT2: thicken a small point into a good interval -/

/-- A convenient explicit local Chebyshev increment estimate extracted from
the summatory Selberg formula.  The constants are deliberately coarse. -/
theorem nativePsi_interval_mul_log_le_gap_tail
    (a b : ℕ) (ha : 3 ≤ a) (hab : a ≤ b) (hb2 : b ≤ 2 * a) :
    (nativePsi b - nativePsi a) * Real.log (a : ℝ) ≤
      2 * ((b : ℝ) - (a : ℝ)) * Real.log (a : ℝ) + 550 * (a : ℝ) := by
  have hlocal := nativePsi_interval_mul_log_le_explicit a b ha hab
  have haR0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast (show 0 < a by omega)
  have hbR0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (show 0 < b by omega)
  have hb2R : (b : ℝ) ≤ 2 * (a : ℝ) := by exact_mod_cast hb2
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h ⊢
    exact h
  have hlogb : Real.log (b : ℝ) ≤ Real.log (a : ℝ) + 1 := by
    calc
      Real.log (b : ℝ) ≤ Real.log (2 * (a : ℝ)) := by
        apply Real.log_le_log
        · exact hbR0
        · exact hb2R
      _ = Real.log 2 + Real.log (a : ℝ) := by
        rw [Real.log_mul (by norm_num) (ne_of_gt haR0)]
      _ ≤ Real.log (a : ℝ) + 1 := by linarith
  have hmain1 :
      2 * (b : ℝ) * Real.log (b : ℝ) ≤
        2 * (b : ℝ) * (Real.log (a : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left hlogb (by positivity)
  have hmain :
      2 * (b : ℝ) * Real.log (b : ℝ) -
          2 * (a : ℝ) * Real.log (a : ℝ) ≤
        2 * ((b : ℝ) - (a : ℝ)) * Real.log (a : ℝ) + 4 * (a : ℝ) := by
    nlinarith
  have hlog4 : Real.log (4 : ℝ) ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
    norm_num at h ⊢
    exact h
  have hC : 2 * (Real.log 4 + 2) + 172 ≤ (182 : ℝ) := by
    linarith
  have hab3 : (a : ℝ) + (b : ℝ) ≤ 3 * (a : ℝ) := by
    linarith
  have htail :
      (2 * (Real.log 4 + 2) + 172) * ((a : ℝ) + (b : ℝ)) ≤
        546 * (a : ℝ) := by
    calc
      (2 * (Real.log 4 + 2) + 172) * ((a : ℝ) + (b : ℝ)) ≤
          182 * ((a : ℝ) + (b : ℝ)) :=
        mul_le_mul_of_nonneg_right hC (by positivity)
      _ ≤ 182 * (3 * (a : ℝ)) :=
        mul_le_mul_of_nonneg_left hab3 (by norm_num)
      _ = 546 * (a : ℝ) := by ring
  linarith

/-- Divided form of the local increment estimate. -/
theorem nativePsi_interval_le_gap_tail
    (a b : ℕ) (ha : 3 ≤ a) (hab : a ≤ b) (hb2 : b ≤ 2 * a)
    (hlog : 1 ≤ Real.log (a : ℝ)) :
    nativePsi b - nativePsi a ≤
      2 * ((b : ℝ) - (a : ℝ)) + 550 * (a : ℝ) / Real.log (a : ℝ) := by
  have hprod := nativePsi_interval_mul_log_le_gap_tail a b ha hab hb2
  have hlogpos : 0 < Real.log (a : ℝ) := lt_of_lt_of_le zero_lt_one hlog
  have heq :
      2 * ((b : ℝ) - (a : ℝ)) + 550 * (a : ℝ) / Real.log (a : ℝ) =
        (2 * ((b : ℝ) - (a : ℝ)) * Real.log (a : ℝ) + 550 * (a : ℝ)) /
          Real.log (a : ℝ) := by
    field_simp [ne_of_gt hlogpos]
    ring
  rw [heq, le_div_iff₀ hlogpos]
  exact hprod

/-- **Erdos PNT2 in forward-interval form.**  If one endpoint has normalized
error at most `ε/4`, and the endpoint is large enough that the Selberg linear
remainder is at most `ε/4`, then every forward displacement of relative size
at most `ε/8` has normalized error at most `ε`. -/
theorem nativePNTError_good_forward_interval
    (A h : ℕ) (ε : ℝ)
    (hA : 3 ≤ A) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlog : 1 ≤ Real.log (A : ℝ))
    (htail : 2200 ≤ ε * Real.log (A : ℝ))
    (hsmall : |nativePNTError A| ≤ ε * (A : ℝ) / 4)
    (hh : (h : ℝ) ≤ ε * (A : ℝ) / 8) :
    |nativePNTError (A + h)| ≤ ε * ((A + h : ℕ) : ℝ) := by
  have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast (show 0 < A by omega)
  have hlogpos : 0 < Real.log (A : ℝ) := lt_of_lt_of_le zero_lt_one hlog
  have hε0 : 0 ≤ ε := hε.le
  have hh0 : (0 : ℝ) ≤ (h : ℝ) := by positivity
  have hhAreal : (h : ℝ) ≤ (A : ℝ) := by
    calc
      (h : ℝ) ≤ ε * (A : ℝ) / 8 := hh
      _ ≤ (A : ℝ) / 8 := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hε1 (by positivity)) (by norm_num)
      _ ≤ (A : ℝ) := by nlinarith
  have hhA : h ≤ A := by exact_mod_cast hhAreal
  have hAB : A ≤ A + h := by omega
  have hB2 : A + h ≤ 2 * A := by omega
  have hinc := nativePsi_interval_le_gap_tail A (A + h) hA hAB hB2 hlog
  have htailTerm :
      550 * (A : ℝ) / Real.log (A : ℝ) ≤ ε * (A : ℝ) / 4 := by
    rw [div_le_iff₀ hlogpos]
    have hmul := mul_le_mul_of_nonneg_right htail (show 0 ≤ (A : ℝ) / 4 by positivity)
    nlinarith
  have hgap :
      2 * (((A + h : ℕ) : ℝ) - (A : ℝ)) ≤ ε * (A : ℝ) / 4 := by
    push_cast
    nlinarith
  have hpsi :
      nativePsi (A + h) - nativePsi A ≤ ε * (A : ℝ) / 2 := by
    calc
      nativePsi (A + h) - nativePsi A ≤
          2 * (((A + h : ℕ) : ℝ) - (A : ℝ)) +
            550 * (A : ℝ) / Real.log (A : ℝ) := hinc
      _ ≤ ε * (A : ℝ) / 4 + ε * (A : ℝ) / 4 :=
        add_le_add hgap htailTerm
      _ = ε * (A : ℝ) / 2 := by ring
  have hsmall' := hsmall
  rw [abs_le] at hsmall'
  have hlowerStep := nativePNTError_forward_lower A h
  have hupperRel :
      nativePNTError (A + h) =
        nativePNTError A + (nativePsi (A + h) - nativePsi A) - (h : ℝ) := by
    unfold nativePNTError
    push_cast
    ring
  rw [abs_le]
  constructor
  · have : -ε * ((A + h : ℕ) : ℝ) ≤ nativePNTError (A + h) := by
      push_cast
      nlinarith [hlowerStep, hsmall'.1]
    exact this
  · rw [hupperRel]
    push_cast
    nlinarith [hsmall'.2, hpsi]
'''
s = s.replace(marker, block + marker, 1)
p.write_text(s)