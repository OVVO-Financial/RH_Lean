import RHLean.Analysis.AlpogeThin.NativePrincipalThin
import RHLean.Geometry.NativeRegularCharacterSlopeDescent
import RHLean.Analysis.AlpogeThin
import RHLean.Geometry.NativeComponentRegularSection
import RHLean.Geometry.NativeAllPlaceEigenGenerators
import RHLean.Geometry.NativeAllPlaceDescent
import RHLean.Geometry.NativeCharacterTraceMaps
import RHLean.Geometry.NativeComponentRegularity
import RHLean.Geometry.NativeTwistedTraceRank
import RHLean.Analysis.AlpogeNativePrincipalProjection
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

/--
info: 'RHLean.Geometry.NativeTransference.transference_dual' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeTransference.transference_dual

/--
info: 'RHLean.Geometry.NativeNumberFieldLattice.exists_short_independent_integers' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeNumberFieldLattice.exists_short_independent_integers

/--
info: 'RHLean.Geometry.NativeNumberFieldLattice.exists_isShortGen_of_short_span' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeNumberFieldLattice.exists_isShortGen_of_short_span

/--
info: 'RHLean.Geometry.nativeExists_component_short_integral_group_section' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.nativeExists_component_short_integral_group_section

/--
info: 'RHLean.Geometry.nativeExists_allPlace_short_eigen' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.nativeExists_allPlace_short_eigen

/--
info: 'RHLean.Geometry.nativeAllPlaceDescent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.nativeAllPlaceDescent

/--
info: 'RHLean.Geometry.nativeCharacterTrace_mem_lattice' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.nativeCharacterTrace_mem_lattice

/--
info: 'RHLean.Geometry.nativeCharacterTrace_jointNorm_paid' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.nativeCharacterTrace_jointNorm_paid

/--
info: 'RHLean.Geometry.NativeAlgebraicDescent.finrank_le_card_mul_finrank_eigenspace_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeAlgebraicDescent.finrank_le_card_mul_finrank_eigenspace_le

/--
info: 'RHLean.Geometry.nativeTwistedTrace_injective_of_componentDet' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.nativeTwistedTrace_injective_of_componentDet

/--
info: 'RHLean.Geometry.nativeDescent_mainTermPayment' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.nativeDescent_mainTermPayment

/--
info: 'RHLean.Analysis.alpogeNativeProjectionChars_card_index' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.alpogeNativeProjectionChars_card_index

/--
info: 'RHLean.Analysis.alpogeNativeProjectedSignal_top_eq_Gsig' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.alpogeNativeProjectedSignal_top_eq_Gsig

/--
info: 'RHLean.Geometry.nativeAllPlaceDescent_of_regular_character_section' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.nativeAllPlaceDescent_of_regular_character_section

/--
info: 'RHLean.Analysis.AlpogeThin.nativeSelectedPairThin' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeSelectedPairThin

/--
info: 'RHLean.Analysis.AlpogeThin.hostResponse_eq_nativeResponse' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.hostResponse_eq_nativeResponse

/--
info: 'RHLean.Analysis.AlpogeThin.principalPair_uniform_noExc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.principalPair_uniform_noExc

/--
info: 'RHLean.Analysis.AlpogeThin.nativePrincipalSelectedPairThin' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativePrincipalSelectedPairThin
