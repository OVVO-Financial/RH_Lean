import RHLean.Analysis.AlpogeLandau
import RHLean.Geometry.NativeRegularSectionSelection
import RHLean.Geometry.NativeGroupDeterminant

/-!
# Axiom guards for the reconstructed geometric/analytic closure

The window hypothesis is explicit in the analytic consumer. This audit does
not assert that the geometric family supplying it has already been built.
-/

set_option pp.width 2000

/--
info: 'RHLean.Analysis.AlpogeLandau.zeroFree_of_rpow_window' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeLandau.zeroFree_of_rpow_window

/--
info: 'RHLean.Geometry.nativeExists_short_integral_regular_section' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.nativeExists_short_integral_regular_section

/--
info: 'RHLean.Analysis.AlpogeLandau.G_eq_nativeGzArithmetic' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeLandau.G_eq_nativeGzArithmetic

/--
info: 'RHLean.Analysis.AlpogeLandau.riemannHypothesis_of_nativeGz_windows' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeLandau.riemannHypothesis_of_nativeGz_windows

/--
info: 'RHLean.Geometry.nativeExists_short_integral_group_section' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.nativeExists_short_integral_group_section
