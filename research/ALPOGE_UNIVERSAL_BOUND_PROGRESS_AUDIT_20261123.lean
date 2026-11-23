import RHLean.Geometry.NativeTranslationTraceVolume
import RHLean.Analysis.AlpogeThin.NativeRayCountTheta
import RHLean.Analysis.AlpogeThin.NativeRayPrimePowerMass
import RHLean.Analysis.AlpogeThin.NativeRayNormOne
import RHLean.Analysis.AlpogeThin.NativeRayClassBound
import RHLean.Analysis.AlpogeThin.NativeRayRealCharacter
import RHLean.Analysis.AlpogeThin.NativeRayLFam

/-!
# Universal ray-count/theta and integral-volume terminal-axiom audit

These guards inspect the actual quantitative theorems. No conditional RH
consumer is used to supply a source estimate.
-/

set_option pp.width 240

/-- info: 'RHLean.Geometry.NumberFieldDescent.gram_det_le_power_of_mean_energy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RHLean.Geometry.NumberFieldDescent.gram_det_le_power_of_mean_energy

/-- info: 'RHLean.Geometry.NumberFieldDescent.jointMapMatrix_gram_det_le_of_rank_saturation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RHLean.Geometry.NumberFieldDescent.jointMapMatrix_gram_det_le_of_rank_saturation

/-- info: 'RHLean.Geometry.NumberFieldDescent.mean_energy_weighted_descent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RHLean.Geometry.NumberFieldDescent.mean_energy_weighted_descent

/-- info: 'RHLean.Geometry.nativeTranslationTrace_normalized_volume_le_qSquared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RHLean.Geometry.nativeTranslationTrace_normalized_volume_le_qSquared

/-- info: 'RHLean.Geometry.nativeFourTrace_normalized_volume_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RHLean.Geometry.nativeFourTrace_normalized_volume_sharp

/-- info: 'RHLean.Analysis.AlpogeThin.NativeRay.QuadraticForm.exists_quadratic_norm_coordinates_with_scale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRay.QuadraticForm.exists_quadratic_norm_coordinates_with_scale

/-- info: 'RHLean.Analysis.AlpogeThin.NativeRay.LatticeBounds.qForm_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRay.LatticeBounds.qForm_count

/-- info: 'RHLean.Analysis.AlpogeThin.NativeRay.LatticeBounds.theta_qForm_all_time' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRay.LatticeBounds.theta_qForm_all_time

/-- info: 'RHLean.Analysis.AlpogeThin.NativeRay.rayCountTheta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRay.rayCountTheta

/-- info: 'RHLean.Analysis.AlpogeThin.NativeRay.PrimePowerMass.finite_mass_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRay.PrimePowerMass.finite_mass_le

/-- info: 'RHLean.Analysis.AlpogeThin.NativeRay.PrimePowerMass.ray_mass_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRay.PrimePowerMass.ray_mass_le

/-- info: 'RHLean.Analysis.AlpogeThin.NativeRay.PrimePowerMass.quadratic_ray_mass_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRay.PrimePowerMass.quadratic_ray_mass_le

/-- info: 'RHLean.Analysis.AlpogeThin.NativeRay.NormOne.exists_generator_absNorm_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRay.NormOne.exists_generator_absNorm_formula

/-- info: 'RHLean.Analysis.AlpogeThin.NativeRay.NormOne.isNormOne_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRay.NormOne.isNormOne_span

/-- info: 'RHLean.Analysis.AlpogeThin.NativeRay.NormOne.isNormOne_of_lamRay_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRay.NormOne.isNormOne_of_lamRay_ne_zero

/-- info: 'RHLean.Analysis.AlpogeThin.NativeIdealClassBound.ncard_ideal_absNorm_eq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeIdealClassBound.ncard_ideal_absNorm_eq_le

/-- info: 'RHLean.Analysis.AlpogeThin.NativeIdealClassBound.classNumber_le_abs_discr_of_finrank_eq_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeIdealClassBound.classNumber_le_abs_discr_of_finrank_eq_two

/-- info: 'RHLean.Analysis.AlpogeThin.NativeRay.discr_eq_neg_of_sq_eq_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRay.discr_eq_neg_of_sq_eq_neg

/-- info: 'RHLean.Analysis.AlpogeThin.NativeRay.RayData.card_le_d_mul_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRay.RayData.card_le_d_mul_sq

/-- info: 'RHLean.Analysis.AlpogeThin.NativeRay.card_ray_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRay.card_ray_le

/-- info: 'RHLean.Analysis.AlpogeThin.NativeRay.RealCharacter.r_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRay.RealCharacter.r_bounds

/-- info: 'RHLean.Analysis.AlpogeThin.NativeRay.RealCharacter.conv_aRay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRay.RealCharacter.conv_aRay

/-- info: 'RHLean.Analysis.AlpogeThin.NativeRay.RealCharacter.conv_real_char' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRay.RealCharacter.conv_real_char

/-- info: 'RHLean.Analysis.AlpogeThin.NativeRay.RealCharacter.conv_real_addChar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRay.RealCharacter.conv_real_addChar

/-- info: 'RHLean.Analysis.AlpogeThin.NativeRay.LFam.ofRayData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRay.LFam.ofRayData

/-- info: 'RHLean.Analysis.AlpogeThin.NativeRay.LFam.ofRayData_sharp_theta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRay.LFam.ofRayData_sharp_theta

/-- info: 'RHLean.Analysis.AlpogeThin.NativeRay.LFam.ofRayData_normOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRay.LFam.ofRayData_normOne

