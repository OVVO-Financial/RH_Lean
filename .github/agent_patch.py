from pathlib import Path

p = Path('RHLean/Analysis/NativePNTErdosContraction.lean')
s = p.read_text()
assert 'nativePNT_exists_dyadic_depth' not in s
marker = '\nend RHLean.Analysis\n'
assert s.count(marker) == 1
block = r'''

/-! ## Eventual supply of good dyadic shells -/

/-- For every positive error tolerance one can choose a fixed dyadic search
depth large enough for the PNT1/PNT2 pigeonhole inequality. -/
theorem nativePNT_exists_dyadic_depth
    (eps : ℝ) (heps : 0 < eps) :
    ∃ K : ℕ,
      2 * (2 * (Real.log 4 + 2) + Real.log 2 + 3) <
        (eps / 4) * ((K : ℝ) * Real.log 2 - 1) := by
  let C : ℝ := 2 * (2 * (Real.log 4 + 2) + Real.log 2 + 3)
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  obtain ⟨K : ℕ, hKnat⟩ :=
    exists_nat_gt ((4 * C / eps + 1) / Real.log 2)
  have hK : (4 * C / eps + 1) / Real.log 2 < (K : ℝ) := by
    exact_mod_cast hKnat
  have hmul : 4 * C / eps + 1 < (K : ℝ) * Real.log 2 := by
    have h := (div_lt_iff₀ hlog2).mp hK
    simpa [mul_comm] using h
  have hsub : 4 * C / eps < (K : ℝ) * Real.log 2 - 1 := by
    linarith
  have hscaled :=
    mul_lt_mul_of_pos_left hsub (show (0 : ℝ) < eps / 4 by positivity)
  have hcancel : (eps / 4) * (4 * C / eps) = C := by
    field_simp [ne_of_gt heps]
    ring
  rw [hcancel] at hscaled
  exact ⟨K, by simpa [C] using hscaled⟩

/-- Once the dyadic depth is fixed, all auxiliary endpoint hypotheses in the
PNT1/PNT2 good-interval theorem hold on every sufficiently large shell.  The
only growth input is the generic real-analysis fact `log x = o(x)`. -/
theorem nativePNT_exists_good_radius_dyadic_eventually
    (K : ℕ) (eps : ℝ)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hdepth :
      2 * (2 * (Real.log 4 + 2) + Real.log 2 + 3) <
        (eps / 4) * ((K : ℝ) * Real.log 2 - 1)) :
    ∀ᶠ A : ℕ in atTop,
      ∃ t ∈ Finset.Icc A (A * 2 ^ K),
        |nativePNTError t| ≤ eps * (t : ℝ) / 4 ∧
          ∀ q ∈ Finset.Icc t (t + nativePNTGoodForwardRadius t eps),
            |nativePNTError q| ≤ eps * (q : ℝ) := by
  have hlogTop :
      Tendsto (fun A : ℕ => Real.log (A : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog1 : ∀ᶠ A : ℕ in atTop, (1 : ℝ) ≤ Real.log (A : ℝ) :=
    hlogTop.eventually_ge_atTop 1
  have htailRaw : ∀ᶠ A : ℕ in atTop,
      2200 / eps ≤ Real.log (A : ℝ) :=
    hlogTop.eventually_ge_atTop (2200 / eps)
  have hlittle :
      (fun A : ℕ => Real.log (A : ℝ)) =o[atTop]
        (fun A : ℕ => (A : ℝ)) :=
    Real.isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop
  have hsmallRaw : ∀ᶠ A : ℕ in atTop,
      ‖Real.log (A : ℝ)‖ ≤ (eps / 8) * ‖(A : ℝ)‖ :=
    hlittle.bound (by positivity)
  filter_upwards
      [eventually_ge_atTop (max 3 (2 ^ K)), hlog1, htailRaw, hsmallRaw]
      with A hA hlogA htail hsmall
  have hA3 : 3 ≤ A := le_trans (le_max_left _ _) hA
  have hpowA : 2 ^ K ≤ A := le_trans (le_max_right _ _) hA
  have hApos : 0 < A := by omega
  have hARpos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hApos
  have htailA : 2200 ≤ eps * Real.log (A : ℝ) := by
    have h := (div_le_iff₀ heps).mp htail
    simpa [mul_comm] using h
  have hlogSmall :
      Real.log (A : ℝ) ≤ (eps / 8) * (A : ℝ) := by
    have hlognn : 0 ≤ Real.log (A : ℝ) := Real.log_natCast_nonneg A
    have hAnn : 0 ≤ (A : ℝ) := by positivity
    simpa [Real.norm_eq_abs, abs_of_nonneg hlognn, abs_of_nonneg hAnn] using hsmall
  have hlogLeA : Real.log (A : ℝ) ≤ (A : ℝ) :=
    Real.log_le_self hARpos.le
  have hepsA : 2200 ≤ eps * (A : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hlogLeA heps.le
    exact htailA.trans hmul
  have hdownA : 1 < (eps / 4) * (2 * (A : ℝ) + 1) := by
    nlinarith
  have hAA : A * 2 ^ K ≤ A ^ 2 := by
    have h := Nat.mul_le_mul_left A hpowA
    simpa [pow_two] using h
  have hprodPos : 0 < A * 2 ^ K := mul_pos hApos (pow_pos (by norm_num) K)
  have hlogProd :
      Real.log ((A * 2 ^ K : ℕ) : ℝ) ≤ 2 * Real.log (A : ℝ) := by
    calc
      Real.log ((A * 2 ^ K : ℕ) : ℝ) ≤
          Real.log ((A ^ 2 : ℕ) : ℝ) := by
        apply Real.log_le_log
        · exact_mod_cast hprodPos
        · exact_mod_cast hAA
      _ = 2 * Real.log (A : ℝ) := by
        rw [Nat.cast_pow, Real.log_pow]
        norm_num
  have hupA :
      Real.log ((A * 2 ^ K : ℕ) : ℝ) - 1 <
        (eps / 4) * (2 * (A : ℝ) + 1) := by
    nlinarith [hlogProd, hlogSmall]
  exact nativePNT_exists_good_radius_dyadic
    A K eps hA3 heps heps1 hlogA htailA hdownA hupA hdepth
'''
s = s.replace(marker, block + marker)
p.write_text(s)
