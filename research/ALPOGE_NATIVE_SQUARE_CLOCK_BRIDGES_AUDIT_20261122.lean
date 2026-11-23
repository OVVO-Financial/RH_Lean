import RHLean.Analysis.AlpogeNativeDyadicWindow
import RHLean.Analysis.AlpogeNativeGzRealInterpolation
import RHLean.Analysis.AlpogeNativeSquareClockCriterion

/-!
# Terminal-axiom audit for the native signed-source bridges

The exact finite source identity, real interpolation estimates, and conditional
RH consumers must use only the standard logical axioms. The guards do not
discharge the quantitative hypotheses in the conditional theorems.
-/

/--
info: 'RHLean.Analysis.nativeAlpogeDyadicPrimePowerWindow_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.nativeAlpogeDyadicPrimePowerWindow_eq

/--
info: 'RHLean.Analysis.nativeAlpogeDyadicDifference_eq_primePowerWindow' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.nativeAlpogeDyadicDifference_eq_primePowerWindow

/--
info: 'RHLean.Analysis.alpogeNativeGzArithmetic_unitCell_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.alpogeNativeGzArithmetic_unitCell_eq

/--
info: 'RHLean.Analysis.alpogeNativeGzArithmetic_unitCell_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.alpogeNativeGzArithmetic_unitCell_bounds

/--
info: 'RHLean.Analysis.alpogeNativeGzArithmetic_sub_floor_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.alpogeNativeGzArithmetic_sub_floor_abs_le

/--
info: 'RHLean.Analysis.alpogeNativeGzArithmetic_abs_le_of_square_lattice_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.alpogeNativeGzArithmetic_abs_le_of_square_lattice_bound

/--
info: 'RHLean.Analysis.riemannHypothesis_of_eventual_squareClock_Gz_rpow' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.riemannHypothesis_of_eventual_squareClock_Gz_rpow

/--
info: 'RHLean.Analysis.riemannHypothesis_of_eventual_squareClock_Gz_linear' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.riemannHypothesis_of_eventual_squareClock_Gz_linear

/--
info: 'RHLean.Analysis.riemannHypothesis_of_square_lattice_Gz_critical' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.riemannHypothesis_of_square_lattice_Gz_critical
