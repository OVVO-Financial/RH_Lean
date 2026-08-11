from pathlib import Path

p = Path('RHLean/Analysis/NativePNTErdosContraction.lean')
s = p.read_text()
assert 'nativePNT_exists_small_error_dyadic_of_endpoint' not in s
marker = '\nend RHLean.Analysis\n'
assert marker in s
block = r'''

/-! ## Quantified PNT1/PNT2 block -/

/-- The pointwise no-crossing hypotheses in `nativePNT_exists_small_error_dyadic`
follow from two scalar endpoint inequalities.  This is the form used in the
geometric packing argument. -/
theorem nativePNT_exists_small_error_dyadic_of_endpoint
    (A K : ℕ) (ε : ℝ)
    (hA : 1 ≤ A) (hε : 0 < ε)
    (hdownA : 1 < ε * (2 * (A : ℝ) + 1))
    (hupA :
      Real.log ((A * 2 ^ K : ℕ) : ℝ) - 1 <
        ε * (2 * (A : ℝ) + 1))
    (hdepth :
      2 * (2 * (Real.log 4 + 2) + Real.log 2 + 3) <
        ε * ((K : ℝ) * Real.log 2 - 1)) :
    ∃ n ∈ Finset.Icc A (A * 2 ^ K),
      |nativePNTError n| < ε * (n : ℝ) := by
  have hpow1 : 1 ≤ 2 ^ K := one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 2)
  have hAB : A ≤ A * 2 ^ K := by
    calc A = A * 1 := by omega
      _ ≤ A * 2 ^ K := Nat.mul_le_mul_left A hpow1
  refine nativePNT_exists_small_error_dyadic A K ε hA hε ?_ ?_ hdepth
  · intro n hAn _hnB
    have hAnR : (A : ℝ) ≤ (n : ℝ) := by exact_mod_cast hAn
    have hε0 : 0 ≤ ε := hε.le
    nlinarith
  · intro n hAn hnB
    have hn1B : n + 1 ≤ A * 2 ^ K := by omega
    have hn1pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hBpos : (0 : ℝ) < ((A * 2 ^ K : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < A * 2 ^ K by positivity)
    have hlog :
        Real.log ((n + 1 : ℕ) : ℝ) ≤
          Real.log ((A * 2 ^ K : ℕ) : ℝ) := by
      apply Real.log_le_log
      · exact hn1pos
      · exact_mod_cast hn1B
    have hAnR : (A : ℝ) ≤ (n : ℝ) := by exact_mod_cast hAn
    have hε0 : 0 ≤ ε := hε.le
    nlinarith

/-- **Combined Erdos PNT1/PNT2 good block.**  A dyadic search block satisfying
only scalar endpoint and depth conditions contains a point whose forward
relative `ε/8` interval stays inside the `ε`-tube. -/
theorem nativePNT_exists_good_forward_dyadic
    (A K : ℕ) (ε : ℝ)
    (hA : 3 ≤ A) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlogA : 1 ≤ Real.log (A : ℝ))
    (htailA : 2200 ≤ ε * Real.log (A : ℝ))
    (hdownA : 1 < (ε / 4) * (2 * (A : ℝ) + 1))
    (hupA :
      Real.log ((A * 2 ^ K : ℕ) : ℝ) - 1 <
        (ε / 4) * (2 * (A : ℝ) + 1))
    (hdepth :
      2 * (2 * (Real.log 4 + 2) + Real.log 2 + 3) <
        (ε / 4) * ((K : ℝ) * Real.log 2 - 1)) :
    ∃ t ∈ Finset.Icc A (A * 2 ^ K),
      |nativePNTError t| ≤ ε * (t : ℝ) / 4 ∧
        ∀ h : ℕ, (h : ℝ) ≤ ε * (t : ℝ) / 8 →
          |nativePNTError (t + h)| ≤ ε * ((t + h : ℕ) : ℝ) := by
  have hδ : 0 < ε / 4 := by positivity
  rcases nativePNT_exists_small_error_dyadic_of_endpoint
      A K (ε / 4) (by omega) hδ hdownA hupA hdepth with
    ⟨t, ht, hsmall⟩
  have htA : A ≤ t := (Finset.mem_Icc.mp ht).1
  have ht3 : 3 ≤ t := hA.trans htA
  have hApos : (0 : ℝ) < (A : ℝ) := by
    exact_mod_cast (show 0 < A by omega)
  have htpos : (0 : ℝ) < (t : ℝ) := by
    exact_mod_cast (show 0 < t by omega)
  have hlogmono : Real.log (A : ℝ) ≤ Real.log (t : ℝ) := by
    apply Real.log_le_log
    · exact hApos
    · exact_mod_cast htA
  have hlogt : 1 ≤ Real.log (t : ℝ) := hlogA.trans hlogmono
  have htailt : 2200 ≤ ε * Real.log (t : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hlogmono hε.le
    linarith
  have hsmall' : |nativePNTError t| ≤ ε * (t : ℝ) / 4 := by
    nlinarith [hsmall]
  refine ⟨t, ht, hsmall', ?_⟩
  intro h hh
  exact nativePNTError_good_forward_interval
    t h ε ht3 hε hε1 hlogt htailt hsmall' hh
'''
s = s.replace(marker, block + marker, 1)
p.write_text(s)
