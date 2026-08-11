from pathlib import Path

p = Path('RHLean/Analysis/NativePNTErdosContraction.lean')
s = p.read_text()

old = '''    have hrnorm : ‖r‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_pos hrpos]
      exact hrlt
    have hrpow : Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hrnorm
'''
new = '''    have hrpow : Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hrpos.le hrlt
'''
assert s.count(old) == 1
s = s.replace(old, new, 1)

assert 'nativePNTError_abs_div_atTop_zero' not in s
marker = '\nend RHLean.Analysis\n'
assert s.count(marker) == 1
block = r'''

/-! ## The Chebyshev prime number theorem -/

/-- Arbitrarily small affine slopes force the normalized absolute Chebyshev
error to zero. -/
theorem nativePNTError_abs_div_atTop_zero :
    Tendsto (fun N : ℕ => |nativePNTError N| / (N : ℝ)) atTop (𝓝 0) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    have hnonneg : 0 ≤ |nativePNTError N| / (N : ℝ) :=
      div_nonneg (abs_nonneg _) hNpos.le
    linarith
  · intro b hb
    let eta : ℝ := b / 2
    have heta : 0 < eta := by
      dsimp [eta]
      positivity
    rcases nativePNTHasAffineEnvelope_arbitrarily_small eta heta with
      ⟨D, hD, henv⟩
    obtain ⟨M : ℕ, hMnat⟩ := exists_nat_gt (D / eta)
    have hM : D / eta < (M : ℝ) := by exact_mod_cast hMnat
    filter_upwards [eventually_ge_atTop (max 1 M)] with N hN
    have hN1 : 1 ≤ N := (le_max_left 1 M).trans hN
    have hMN : M ≤ N := (le_max_right 1 M).trans hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    have hMNcast : (M : ℝ) ≤ (N : ℝ) := by exact_mod_cast hMN
    have hfrac : D / eta < (N : ℝ) := hM.trans_le hMNcast
    have hDlt : D < (N : ℝ) * eta :=
      (div_lt_iff₀ heta).mp hfrac
    have herr := henv N
    have hnum : |nativePNTError N| < b * (N : ℝ) := by
      dsimp [eta] at hDlt herr ⊢
      nlinarith
    rw [div_lt_iff₀ hNpos]
    exact hnum

/-- The signed normalized Chebyshev error tends to zero. -/
theorem nativePNTError_div_atTop_zero :
    Tendsto (fun N : ℕ => nativePNTError N / (N : ℝ)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine nativePNTError_abs_div_atTop_zero.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : 0 ≤ (N : ℝ) := by positivity
  rw [abs_div, abs_of_nonneg hN0]

/-- **Native Chebyshev PNT:** `psi(N) / N -> 1`. -/
theorem nativePsi_div_atTop_one :
    Tendsto (fun N : ℕ => nativePsi N / (N : ℝ)) atTop (𝓝 1) := by
  have hsum : Tendsto
      (fun N : ℕ => nativePNTError N / (N : ℝ) + 1)
      atTop (𝓝 1) := by
    simpa using nativePNTError_div_atTop_zero.add tendsto_const_nhds
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNne : (N : ℝ) ≠ 0 := by
    exact_mod_cast (show N ≠ 0 by omega)
  unfold nativePNTError
  field_simp [hNne]
  ring
'''
s = s.replace(marker, block + marker)
p.write_text(s)
