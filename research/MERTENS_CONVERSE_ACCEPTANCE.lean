import «research.MERTENS_CONVERSE_INVERSION»

/-! Exact signatures and kernel dependencies for the converse development. -/

open RHLean.Analysis RHLean.Analysis.MertensExponent

example {a : ℝ} (ha : 0 ≤ a) (h : ZerosInSymmetricStrip a) :
    DifferentiableOn ℂ nativeInvZetaRegularized (exponentHalfPlane a) :=
  regularizedReciprocal_holomorphic_of_strip ha h

example {a σ η : ℝ} (ha : 0 ≤ a) (haσ : a < σ) (hσ : σ < 1)
    (h : ZerosInSymmetricStrip a) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, σ ≤ s.re → s.re ≤ 2 →
      ‖nativeInvZetaRegularized s‖ ≤ C * (1 + |s.im|) ^ η :=
  regularizedReciprocal_subpower_of_strip ha haσ hσ h hη

#print axioms RHLean.Analysis.MertensExponent.zeta_ne_zero_of_strip
#print axioms RHLean.Analysis.MertensExponent.regularizedReciprocal_differentiableAt_off_pole
#print axioms RHLean.Analysis.MertensExponent.regularizedReciprocal_differentiableAt_of_strip
#print axioms RHLean.Analysis.MertensExponent.regularizedReciprocal_holomorphic_of_strip
#print axioms RHLean.Analysis.MertensExponent.regularizedReciprocal_eq_mellin_classical
#print axioms RHLean.Analysis.MertensExponent.threeCircle_power_bound
#print axioms RHLean.Analysis.MertensExponent.threeCircle_exponent_mem_Ioo
#print axioms RHLean.Analysis.MertensExponent.zeta_bounded_right_halfPlane
#print axioms RHLean.Analysis.MertensExponent.zeta_norm_le_positive_strip
#print axioms RHLean.Analysis.MertensExponent.zetaDiscPoint_ne_one
#print axioms RHLean.Analysis.MertensExponent.zeta_norm_le_on_shifted_disk
#print axioms RHLean.Analysis.MertensExponent.reciprocal_stretchedLog_of_local_data
#print axioms RHLean.Analysis.MertensExponent.reciprocal_stretchedLog_of_strip
#print axioms RHLean.Analysis.MertensExponent.exp_stretchedLog_eventually_le_rpow
#print axioms RHLean.Analysis.MertensExponent.regularizedReciprocal_subpower_of_strip
#print axioms RHLean.Analysis.MertensExponent.horizontalIntegral_tendsto_zero_of_bound
#print axioms RHLean.Analysis.MertensExponent.verticalIntegral_eq_of_holomorphic_and_horizontal_limits
#print axioms RHLean.Analysis.MertensExponent.mellin_compactSupport_bounded_positive_strip
#print axioms RHLean.Analysis.MertensExponent.smoothingMellin_simple_decay
#print axioms RHLean.Analysis.MertensExponent.interpolate_simple_and_quadratic_decay
#print axioms RHLean.Analysis.MertensExponent.smoothingMellin_fractional_decay
#print axioms RHLean.Analysis.MertensExponent.regularizedSmoothedIntegrand_eq_native
#print axioms RHLean.Analysis.MertensExponent.regularizedSmoothedIntegrand_differentiableAt
#print axioms RHLean.Analysis.MertensExponent.norm_ge_scaled_height
#print axioms RHLean.Analysis.MertensExponent.converseHeightWeight_integrable
#print axioms RHLean.Analysis.MertensExponent.regularizedSmoothedIntegrand_bound
#print axioms RHLean.Analysis.MertensExponent.converseIntegralConstant_pos
#print axioms RHLean.Analysis.MertensExponent.integrable_vertical_of_heightBound
#print axioms RHLean.Analysis.MertensExponent.verticalIntegral_norm_le_heightBound
#print axioms RHLean.Analysis.MertensExponent.converseHeightWeight_tendsto_zero
#print axioms RHLean.Analysis.MertensExponent.verticalIntegral_congr_line
#print axioms RHLean.Analysis.MertensExponent.smoothedMobius_bound_of_strip
