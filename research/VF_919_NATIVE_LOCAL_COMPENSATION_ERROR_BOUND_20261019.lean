import «research.NATIVE_SEVEN_EIGHTHS_LOCAL_COMPENSATION_20261019»

/-!
# Native quantitative high-row local compensation

The original OAI proof pays a **quantitative**, not just algebraic,
compensated Euler-factor remainder. This module proves the corresponding
720*T inequality from explicit local size hypotheses in RH_Lean's own
native local Euler coordinates, without importing any OAI theorem.

The hypotheses on the ACTUAL prime-ideal coefficients (especially
amp^2 * ‖E‖ <= 28*T and amp * ‖A‖ * ‖E‖ <= 28*T)
must be derived from original unramified/ramified Euler coefficients,
uniformly in the conductor. They are NOT claimed here. The theorem is
a rigorous local norm-bound consumer, not a global 7/8 proof.
-/

noncomputable section

namespace RHLean.Analysis

private theorem vf919_one_sub_nonzero_of_norm_le_half
    (z : ℂ) (hz : ‖z‖ ≤ 1 / 2) : 1 - z ≠ 0 := by
  have ht := norm_add_le (1 - z) z
  simp only [sub_add_cancel, norm_one] at ht
  have hn : 0 < ‖1 - z‖ := by linarith
  exact norm_pos_iff.mp hn

private theorem vf919_norm_inv_one_sub_le_two
    (z : ℂ) (hz : ‖z‖ ≤ 1 / 2) :
    ‖(1 - z)⁻¹‖ ≤ (2 : ℝ) := by
  have ht := norm_add_le (1 - z) z
  simp only [sub_add_cancel, norm_one] at ht
  have hn : 0 < ‖1 - z‖ := by linarith
  have hb : (1 : ℝ) ≤ 2 * ‖1 - z‖ := by linarith
  rw [norm_inv]
  have hdiv : (1 : ℝ) / ‖1 - z‖ ≤ 2 :=
    (div_le_iff₀ hn).mpr (by nlinarith)
  simpa only [one_div] using hdiv

/-- Quantitative form of the compensated local cancellation (OAI 5.13b).
Unlike the finite polynomial identity, this is a REAL norm inequality.
All hypotheses are explicit local magnitude claims, not a hidden global
moment assumption. This bound becomes available to the genuine Hecke
row only once its actual Euler-coefficient estimates discharge them. -/
theorem vf919NativeLocalCompensation_norm_le_720
    (A U Qw V W D E P Ps : ℂ) (amp budget : ℝ)
    (hamp : 1 ≤ amp)
    (hV : ‖V‖ ≤ 1 / 2) (hD : ‖D‖ ≤ 1 / 2)
    (hW : ‖W‖ ≤ amp) (hQw : ‖Qw‖ ≤ amp) (hU : ‖U‖ ≤ 1)
    (hVbudget : amp ^ 2 * ‖V‖ ≤ budget)
    (hDbudget : amp ^ 2 * ‖D‖ ≤ budget)
    (hEbudget : amp ^ 2 * ‖E‖ ≤ 28 * budget)
    (hAEbudget : amp * ‖A‖ * ‖E‖ ≤ 28 * budget)
    (hWne : 1 - W ≠ 0)
    (hphase1 : A * D = U) (hphase2 : U * W = Qw)
    (hstar : Ps = E - D)
    (hfull : P = (1 - V)⁻¹ + W / (1 - W) + Ps) :
    ‖nativeSelectedEulerFactor A Qw V W D Ps +
      U * nativeUnselectedEulerFactor P V W D‖ ≤ 720 * budget := by
  have hamp0 : 0 ≤ amp := by linarith
  have hbudget : 0 ≤ budget :=
    (mul_nonneg (sq_nonneg amp) (norm_nonneg V)).trans hVbudget
  have hVne : 1 - V ≠ 0 :=
    vf919_one_sub_nonzero_of_norm_le_half V hV
  have hinvV : ‖(1 - V)⁻¹‖ ≤ (2 : ℝ) :=
    vf919_norm_inv_one_sub_le_two V hV
  have hinvD : ‖(1 - D)⁻¹‖ ≤ (2 : ℝ) :=
    vf919_norm_inv_one_sub_le_two D hD
  have h1V : ‖1 - V‖ ≤ (2 : ℝ) := by
    have hh := norm_sub_le (1 : ℂ) V
    rw [norm_one] at hh
    linarith
  have h1W : ‖1 - W‖ ≤ 2 * amp := by
    have hh := norm_sub_le (1 : ℂ) W
    rw [norm_one] at hh
    linarith
  have hdiff : ‖U - Qw‖ ≤ 2 * amp := by
    have hh := norm_sub_le U Qw
    linarith
  have hfac : ‖((1 - V) * (1 - W)) / (1 - D)‖ ≤ 8 * amp := by
    rw [div_eq_mul_inv, norm_mul, norm_mul]
    calc
      ‖1 - V‖ * ‖1 - W‖ * ‖(1 - D)⁻¹‖ ≤
        2 * (2 * amp) * 2 := by gcongr
      _ = 8 * amp := by ring
  have hleft :
      ‖(U - Qw) * (V / (1 - V) - D)‖ ≤
        2 * amp * (2 * ‖V‖ + ‖D‖) := by
    rw [norm_mul]
    apply mul_le_mul hdiff _ (norm_nonneg _) (by positivity)
    calc
      ‖V / (1 - V) - D‖ ≤ ‖V / (1 - V)‖ + ‖D‖ :=
        norm_sub_le _ _
      _ ≤ 2 * ‖V‖ + ‖D‖ := by
        rw [div_eq_mul_inv, norm_mul]
        nlinarith [mul_le_mul_of_nonneg_left hinvV (norm_nonneg V)]
  have hright :
      ‖(A + U - Qw) * E‖ ≤
        (‖A‖ + 2 * amp) * ‖E‖ := by
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    calc
      ‖A + U - Qw‖ = ‖A + (U - Qw)‖ := by ring
      _ ≤ ‖A‖ + ‖U - Qw‖ := norm_add_le _ _
      _ ≤ ‖A‖ + 2 * amp := by linarith
  rw [nativeLocalCompensation_equation_5_13b
    A U Qw V W D E P Ps hVne hWne hphase1 hphase2 hstar hfull,
    norm_mul]
  calc
    ‖((1 - V) * (1 - W)) / (1 - D)‖ *
        ‖(U - Qw) * (V / (1 - V) - D) + (A + U - Qw) * E‖ ≤
      (8 * amp) *
        (2 * amp * (2 * ‖V‖ + ‖D‖) +
          (‖A‖ + 2 * amp) * ‖E‖) := by
      apply mul_le_mul hfac _ (norm_nonneg _) (by positivity)
      exact (norm_add_le _ _).trans (add_le_add hleft hright)
    _ = 32 * (amp ^ 2 * ‖V‖) +
        16 * (amp ^ 2 * ‖D‖) +
        8 * (amp * ‖A‖ * ‖E‖) +
        16 * (amp ^ 2 * ‖E‖) := by ring
    _ ≤ 720 * budget := by linarith

#print axioms vf919NativeLocalCompensation_norm_le_720

end RHLean.Analysis
