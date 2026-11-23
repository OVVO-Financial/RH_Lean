import RHLean.Geometry.NativeNumberFieldIntegralDescent
import RHLean.Analysis.AlpogeNativeZetaWindowRHBridge

/-!
# Kernel axiom audit for native O_K-lattice descent and window-witness RH bridge

Each guard accepts only Lean's three standard logical axioms (`propext`,
`Classical.choice`, `Quot.sound`). Clean axiom footprints confirm zero `sorry`
and zero synthetic axioms; they do not discharge the open window-witness
existence hypothesis.
-/

/--
info: 'RHLean.Geometry.NumberFieldDescent.completed_image_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NumberFieldDescent.completed_image_bound

/--
info: 'RHLean.Geometry.NumberFieldDescent.spectral_descent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NumberFieldDescent.spectral_descent

/--
info: 'RHLean.Geometry.NumberFieldDescent.descent_of_linear_maps' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NumberFieldDescent.descent_of_linear_maps

/--
info: 'RHLean.Geometry.NumberFieldDescent.isogeny_to_power' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NumberFieldDescent.isogeny_to_power

/--
info: 'RHLean.Geometry.NumberFieldDescent.endomorphism_norm_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NumberFieldDescent.endomorphism_norm_bound

/--
info: 'RHLean.Analysis.alpogeNativeGzArithmetic_mellin' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.alpogeNativeGzArithmetic_mellin

/--
info: 'RHLean.Analysis.alpogeNativeGzTransform_at_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.alpogeNativeGzTransform_at_zero

/--
info: 'RHLean.Analysis.riemannZeta_ne_zero_of_Gz_window' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.riemannZeta_ne_zero_of_Gz_window

/--
info: 'RHLean.Analysis.riemannHypothesis_of_Gz_windows' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.riemannHypothesis_of_Gz_windows

/--
info: 'RHLean.Analysis.riemannHypothesis_of_squareClock_Gz_windows' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.riemannHypothesis_of_squareClock_Gz_windows

/--
info: 'RHLean.Analysis.alpogeNativeDerivInt_moveConstant' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.alpogeNativeDerivInt_moveConstant

/--
info: 'RHLean.Analysis.alpogeNativeGz_sub_le_projectedSignal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.alpogeNativeGz_sub_le_projectedSignal

/--
info: 'RHLean.Analysis.alpogeNativeGz_balance_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.alpogeNativeGz_balance_le

/--
info: 'RHLean.Analysis.alpogeNativeGz_le_of_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.alpogeNativeGz_le_of_witness

/--
info: 'RHLean.Analysis.alpogeNativeGz_windows_of_witnesses' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.alpogeNativeGz_windows_of_witnesses

/--
info: 'RHLean.Analysis.riemannZeta_ne_zero_of_zetaWindowWitnesses' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.riemannZeta_ne_zero_of_zetaWindowWitnesses

/--
info: 'RHLean.Analysis.riemannHypothesis_of_zetaWindowWitnesses' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.riemannHypothesis_of_zetaWindowWitnesses
