import RHLean.Geometry.NativeTranslationTraceVolume
import RHLean.Analysis.AlpogeThin.NativeRayCountTheta

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

