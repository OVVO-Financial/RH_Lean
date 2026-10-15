import «research.MERTENS_AMPLITUDE_STRIP_MAP»

/-! Exact finite-amplitude statements, domain regressions and kernel audits. -/
open RHLean.Analysis RHLean.Analysis.MertensAmplitude RHLean.Analysis.MertensExponent

example {x A : ℝ} (hx : 1 < x) (hA : 0 < A) :
    x ^ (Real.log A / Real.log x) = A := rpow_coordinate hx hA

example {x A : ℝ} (hx : 1 < x) (hA : 0 < A) :
    (x ^ ((1 : ℝ) / 8) ≤ A ∧ A ≤ x ^ ((7 : ℝ) / 8)) ↔
      ((1 : ℝ) / 8 ≤ Real.log A / Real.log x ∧ Real.log A / Real.log x ≤ (7 : ℝ) / 8) :=
  eighths_band_iff hx hA

example {x A : ℝ} (hx : 1 < x) (hA : 0 < A) :
    Real.log (x / A) / Real.log x = 1 - Real.log A / Real.log x :=
  coordinate_reflection hx hA

example {x A : ℝ} (hx : 1 < x) (hA : 0 < A) :
    x / A = A ↔ A = Real.sqrt x := reflection_fixed_iff hx hA

example {x : ℝ} (hx : 1 < x) :
    amplitudeCoordinate x '' amplitudeBand x ((1 : ℝ) / 8) ((7 : ℝ) / 8) =
      Set.Icc ((1 : ℝ) / 8) ((7 : ℝ) / 8) := image_amplitudeBand hx _ _

example {n : ℕ} (hn : 2 ≤ n) (hM : mertensSummatory n ≠ 0) :
    (n : ℝ) ^ ((1 : ℝ) / 8) < ‖mertensSummatory n‖ ↔
      Real.log ((n : ℝ) / ‖mertensSummatory n‖) / Real.log (n : ℝ) < (7 : ℝ) / 8 :=
  mertens_eighth_crossing_iff hn hM

example : mertensAmplitudeCoordinate 2 = none := mertensCoordinate_two
example : mertensAmplitudeCoordinate 3 = some 0 := mertensCoordinate_three
example : ¬ (mertensAmplitude 3 ∈ amplitudeBand 3 ((1 : ℝ) / 8) ((7 : ℝ) / 8)) :=
  mertens_three_outside_eighths

example : Filter.limsup
    (fun n : ℕ => Real.log (max 1 ‖mertensSummatory n‖) / Real.log (n : ℝ)) Filter.atTop =
      zetaRightmostRealPart := amplitude_limsup_eq_rightmost

#print axioms RHLean.Analysis.MertensAmplitude.coordinate_rpow
#print axioms RHLean.Analysis.MertensAmplitude.rpow_coordinate
#print axioms RHLean.Analysis.MertensAmplitude.coordinate_sqrt
#print axioms RHLean.Analysis.MertensAmplitude.coordinate_mem_Icc_iff
#print axioms RHLean.Analysis.MertensAmplitude.image_amplitudeBand
#print axioms RHLean.Analysis.MertensAmplitude.coordinate_mem_unit_iff
#print axioms RHLean.Analysis.MertensAmplitude.coordinate_reflection
#print axioms RHLean.Analysis.MertensAmplitude.amplitude_mul_reflection
#print axioms RHLean.Analysis.MertensAmplitude.reflection_involutive
#print axioms RHLean.Analysis.MertensAmplitude.reflection_fixed_iff
#print axioms RHLean.Analysis.MertensAmplitude.reflection_mem_symmetricBand_iff
#print axioms RHLean.Analysis.MertensAmplitude.symmetricBand_iff_centered
#print axioms RHLean.Analysis.MertensAmplitude.crossing_iff_reflected_coordinate
#print axioms RHLean.Analysis.MertensAmplitude.coordinate_scaled_power
#print axioms RHLean.Analysis.MertensAmplitude.eighths_band_iff
#print axioms RHLean.Analysis.MertensAmplitude.one_le_mertensAmplitude
#print axioms RHLean.Analysis.MertensAmplitude.mertensCoordinate_some
#print axioms RHLean.Analysis.MertensAmplitude.mertensCoordinate_none_of_zero
#print axioms RHLean.Analysis.MertensAmplitude.mertensCoordinate_mem_unit
#print axioms RHLean.Analysis.MertensAmplitude.mertens_amplitudeBand_iff
#print axioms RHLean.Analysis.MertensAmplitude.mertens_eighth_crossing_iff
#print axioms RHLean.Analysis.MertensAmplitude.actual_coordinate_eq_logSlope
#print axioms RHLean.Analysis.MertensAmplitude.amplitude_limsup_eq_rightmost
#print axioms RHLean.Analysis.MertensAmplitude.mertensCoordinate_two
#print axioms RHLean.Analysis.MertensAmplitude.mertensCoordinate_three
#print axioms RHLean.Analysis.MertensAmplitude.mertens_three_outside_eighths
