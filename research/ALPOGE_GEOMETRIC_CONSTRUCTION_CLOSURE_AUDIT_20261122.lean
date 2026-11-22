import RHLean.Analysis.AlpogePrimeFreeCommutatorConditioning
import RHLean.Analysis.AlpogeSquareRootArithmeticMultiplicity
import RHLean.Analysis.AlpogePrimeFreeForwardJet
import RHLean.Geometry.NativePolarizationCoefficientLattice
import RHLean.Geometry.NativeThetaLetterFamily
import RHLean.Geometry.NativeThetaSpanningFamily
import RHLean.Geometry.NativeDerivedGeometricHost
import RHLean.Analysis.AlpogeThin.NativeDyadicHostDer
import RHLean.Analysis.AlpogeNativeCMUnramified
import RHLean.Analysis.AlpogeThin.NativeDyadicHostDecomposition
import RHLean.Analysis.AlpogeNativeIntegralQuadraticRoot
import RHLean.Analysis.AlpogeThin.NativeDyadicHostPrimes
import RHLean.Analysis.AlpogeThin.NativeDyadicHostSideConditions
import RHLean.Geometry.NativeHostThetaPolynomial
import RHLean.Geometry.NativeFramedShortSectionConstruction
import RHLean.Analysis.AlpogeThin.NativeDyadicHostRaw
import RHLean.Analysis.AlpogeThin.NativeDyadicChiField
import RHLean.Geometry.NativeGradedPeterssonConstruction
import RHLean.Analysis.AlpogeThin.NativeConstructedDyadicGzPayment
import RHLean.Geometry.NativeGradedCharacterSlopeDescent
import RHLean.Geometry.NativeGradedShortSectionConstruction
import RHLean.Analysis.AlpogeNativeReciprocitySurjective
import RHLean.Analysis.AlpogeNativeDyadicHostSize
import RHLean.Analysis.AlpogeThin.NativeDyadicGzPayment
import RHLean.Geometry.NativeGradedSectionRegularity
import RHLean.Analysis.AlpogeThin.NativeCftThin
import RHLean.Geometry.NativeJetRankBudget
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

/--
info: 'RHLean.Geometry.NativeJetRank.exists_jet_order' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeJetRank.exists_jet_order

/--
info: 'RHLean.Geometry.NativeJetRank.rank_growth_of_component_jets' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeJetRank.rank_growth_of_component_jets

/--
info: 'RHLean.Analysis.AlpogeThin.nativeCftGPsi_eq_nativeResponse' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeCftGPsi_eq_nativeResponse

/--
info: 'RHLean.Analysis.AlpogeThin.nativeSelectedCftThinReturn' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeSelectedCftThinReturn

/--
info: 'RHLean.Geometry.nativeGradedSection_groupDet_regular' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.nativeGradedSection_groupDet_regular

/--
info: 'RHLean.Geometry.nativeAllPlaceDescent_of_regular_groupDet' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.nativeAllPlaceDescent_of_regular_groupDet

/--
info: 'RHLean.Geometry.nativeAllPlaceDescent_of_graded_component_section' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.nativeAllPlaceDescent_of_graded_component_section

/--
info: 'RHLean.Geometry.nativeExists_graded_short_integral_injective_section' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.nativeExists_graded_short_integral_injective_section

/--
info: 'RHLean.Analysis.alpogeNativeRecMap_surjective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.alpogeNativeRecMap_surjective

/--
info: 'RHLean.Analysis.alpogeNativeDyadicH_card' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.alpogeNativeDyadicH_card

/--
info: 'RHLean.Analysis.AlpogeThin.nativeSelectedDyadicHostThin' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeSelectedDyadicHostThin

/--
info: 'RHLean.Analysis.AlpogeThin.nativeThinBill_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeThinBill_eq

/--
info: 'RHLean.Analysis.AlpogeThin.nativeThinBill_div_projectionDivisor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeThinBill_div_projectionDivisor

/--
info: 'RHLean.Analysis.AlpogeThin.nativeSelectedDyadicCompleteProjection' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeSelectedDyadicCompleteProjection

/--
info: 'RHLean.Analysis.AlpogeThin.nativeDyadicTwoBitCharacter_induces' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeDyadicTwoBitCharacter_induces

/--
info: 'RHLean.Analysis.AlpogeThin.nativePairGood_dyadicGsig_sub_Gz_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativePairGood_dyadicGsig_sub_Gz_norm_le

/--
info: 'RHLean.Analysis.AlpogeThin.nativeSelectedDyadicGzPayment' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeSelectedDyadicGzPayment

/--
info: 'RHLean.Geometry.nativePeterssonNorm_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.nativePeterssonNorm_mul_le

/--
info: 'RHLean.Geometry.nativeExists_graded_regular_petersson_multiplier' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.nativeExists_graded_regular_petersson_multiplier

/--
info: 'RHLean.Geometry.nativeAllPlaceDescent_of_constructed_petersson_section' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.nativeAllPlaceDescent_of_constructed_petersson_section

/--
info: 'RHLean.Geometry.nativeShortSectionCost_le_exp_of_source_scales' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.nativeShortSectionCost_le_exp_of_source_scales

/--
info: 'RHLean.Analysis.AlpogeThin.nativeDyadicHost_windows' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeDyadicHost_windows

/--
info: 'RHLean.Analysis.AlpogeThin.nativeDyadicAnalyticRemainder_eventually' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeDyadicAnalyticRemainder_eventually

/--
info: 'RHLean.Analysis.AlpogeThin.nativeConstructedDyadicGzPayment' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeConstructedDyadicGzPayment

/--
info: 'RHLean.Analysis.alpogeNativeHostField_finrank' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.alpogeNativeHostField_finrank

/--
info: 'RHLean.Analysis.alpogeNativeHostField_art_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.alpogeNativeHostField_art_spec

/--
info: 'RHLean.Analysis.alpogeNativeHostGalEquiv_conj_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.alpogeNativeHostGalEquiv_conj_iff

/--
info: 'RHLean.Analysis.alpogeNativeHostField_isCMField' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.alpogeNativeHostField_isCMField

/--
info: 'RHLean.Analysis.AlpogeThin.nativeDyadicHostField_isChiField' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeDyadicHostField_isChiField

/--
info: 'RHLean.Analysis.NativeQuadraticRoot.gauss_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.NativeQuadraticRoot.gauss_sq

/--
info: 'RHLean.Analysis.alpogeNativeSqrtD_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.alpogeNativeSqrtD_sq

/--
info: 'RHLean.Analysis.alpogeNativeSqrtD_galois_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.alpogeNativeSqrtD_galois_apply

/--
info: 'RHLean.Analysis.AlpogeThin.nativeDyadicGenerator_order' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeDyadicGenerator_order

/--
info: 'RHLean.Analysis.AlpogeThin.nativeDyadicFrame_n0' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeDyadicFrame_n0

/--
info: 'RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw

/--
info: 'RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_kerChi' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_kerChi

/--
info: 'RHLean.Analysis.AlpogeThin.nativeDyadicPageN_two_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeDyadicPageN_two_le

/--
info: 'RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_of_pageN_winPair' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_of_pageN_winPair

/--
info: 'RHLean.Geometry.NativeFramedRules.secZ_eq_zero_of_generic' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeFramedRules.secZ_eq_zero_of_generic

/--
info: 'RHLean.Geometry.NativeFramedRules.section_regular_of_atlas' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeFramedRules.section_regular_of_atlas

/--
info: 'RHLean.Geometry.nativeExists_framed_short_integral_injective_section' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.nativeExists_framed_short_integral_injective_section

/--
info: 'RHLean.Analysis.NativeIntegralQuadratic.halfRoot_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.NativeIntegralQuadratic.halfRoot_integral

/--
info: 'RHLean.Analysis.alpogeNativeIntegralSqrtD_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.alpogeNativeIntegralSqrtD_sq

/--
info: 'RHLean.Analysis.alpogeNativeIntegralHalfRoot_two_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.alpogeNativeIntegralHalfRoot_two_mul

/--
info: 'RHLean.Analysis.alpogeNativeIntegralBar_eq_complexConj' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.alpogeNativeIntegralBar_eq_complexConj

/--
info: 'RHLean.Analysis.alpogeNativeIntegralHalfRoot_add_bar' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.alpogeNativeIntegralHalfRoot_add_bar

/--
info: 'RHLean.Analysis.NativePrimeLift.inertia_lift' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.NativePrimeLift.inertia_lift

/--
info: 'RHLean.Analysis.NativePrimeLift.exists_over' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.NativePrimeLift.exists_over

/--
info: 'RHLean.Analysis.NativeCyclotomicResidue.zO_sub_mem_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.NativeCyclotomicResidue.zO_sub_mem_iff

/--
info: 'RHLean.Analysis.NativeCyclotomicResidue.tauN_inertia_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.NativeCyclotomicResidue.tauN_inertia_iff

/--
info: 'RHLean.Analysis.NativeCyclotomicResidue.tauN_frob' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.NativeCyclotomicResidue.tauN_frob

/--
info: 'RHLean.Analysis.alpogeNativeHostField_inertia_iff_hostData' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.alpogeNativeHostField_inertia_iff_hostData

/--
info: 'RHLean.Analysis.alpogeNativeHostField_hostData_frob' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.alpogeNativeHostField_hostData_frob

/--
info: 'RHLean.Analysis.alpogeNativeHostField_frob_iff_hostData' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.alpogeNativeHostField_frob_iff_hostData

/--
info: 'RHLean.Analysis.alpogeNativeHostConj_unramEF' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.alpogeNativeHostConj_unramEF

/--
info: 'RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_inertia' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_inertia

/--
info: 'RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_frob_any' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_frob_any

/--
info: 'RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_unramEF' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_unramEF

/--
info: 'RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_coprimeFifteen' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_coprimeFifteen

/--
info: 'RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_psQ' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_psQ

/--
info: 'RHLean.Analysis.AlpogeThin.nativeDyadicArt_halfConductor_nontrivial' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeDyadicArt_halfConductor_nontrivial

/--
info: 'RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_exact

/--
info: 'RHLean.Geometry.NativeTheta.CoeffNorm.allEmbeddingNorm_le_of_l1Bound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeTheta.CoeffNorm.allEmbeddingNorm_le_of_l1Bound

/--
info: 'RHLean.Geometry.NativeTheta.exists_short_integral_harmonic_of_signature' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeTheta.exists_short_integral_harmonic_of_signature

/--
info: 'RHLean.Geometry.nativeExists_host_short_integral_harmonic_polynomial' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.nativeExists_host_short_integral_harmonic_polynomial

/--
info: 'RHLean.Analysis.NativeCMUnramified.unramified_of_conjugation_separates' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.NativeCMUnramified.unramified_of_conjugation_separates

/--
info: 'RHLean.Analysis.alpogeNativeHostField_unramified' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.alpogeNativeHostField_unramified

/--
info: 'RHLean.Analysis.alpogeNativeHostField_decomp_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.alpogeNativeHostField_decomp_iff

/--
info: 'RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_decomp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_decomp

/--
info: 'RHLean.Analysis.AlpogeThin.nativeDyadicHostDer' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeDyadicHostDer

/--
info: 'RHLean.Analysis.AlpogeThin.nativeDyadicHostAx' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeDyadicHostAx

/--
info: 'RHLean.Analysis.AlpogeThin.nativeDyadicHostAx_of_pageN_winPair' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeDyadicHostAx_of_pageN_winPair

/--
info: 'RHLean.Analysis.AlpogeThin.nativeDyadicHostAx_sideConditions' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeDyadicHostAx_sideConditions

/--
info: 'RHLean.Analysis.AlpogeThin.nativeDyadicHostAx_kerChi' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeDyadicHostAx_kerChi

/--
info: 'RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_exists_traceSelfDualIdeal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_exists_traceSelfDualIdeal

/--
info: 'RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_rd_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_rd_ge

/--
info: 'RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_rd_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_rd_le

/--
info: 'RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_rd_sq_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_rd_sq_ge

/--
info: 'RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_splitK' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_splitK

/--
info: 'RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_ordinary' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_ordinary

/--
info: 'RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_eta' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_eta

/--
info: 'RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_norm_mu' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_norm_mu

/--
info: 'RHLean.Geometry.nativeDyadicGeometricHost' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.nativeDyadicGeometricHost

/--
info: 'RHLean.Geometry.nativeDyadicGeometricHostOfDerived' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.nativeDyadicGeometricHostOfDerived

/--
info: 'RHLean.Geometry.nativeDyadicGeometricHostOfDerived_inPsi' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.nativeDyadicGeometricHostOfDerived_inPsi

/--
info: 'RHLean.Geometry.nativeDyadicThetaEmbedding_sqrtD' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.nativeDyadicThetaEmbedding_sqrtD

/--
info: 'RHLean.Geometry.NativeHermitianLattice.span_eq_top' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeHermitianLattice.span_eq_top

/--
info: 'RHLean.Geometry.NativeHermitianLattice.trace_dual_min' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeHermitianLattice.trace_dual_min

/--
info: 'RHLean.Geometry.NativeHermitianLattice.exists_short_vectors' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeHermitianLattice.exists_short_vectors

/--
info: 'RHLean.Geometry.NativeTheta.Paired.exists_short_lattice_family' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeTheta.Paired.exists_short_lattice_family

/--
info: 'RHLean.Geometry.NativeTheta.Paired.exists_finite_integral_harmonic_family' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeTheta.Paired.exists_finite_integral_harmonic_family

/--
info: 'RHLean.Geometry.NativeTheta.Paired.exists_finite_integral_HHa_family' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeTheta.Paired.exists_finite_integral_HHa_family

/--
info: 'RHLean.Geometry.NativeTheta.Paired.rowHighest_orbitSpan_main' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeTheta.Paired.rowHighest_orbitSpan_main

/--
info: 'RHLean.Geometry.NativeTheta.Paired.span_range_coordProd_eq_rowHighest' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeTheta.Paired.span_range_coordProd_eq_rowHighest

/--
info: 'RHLean.Geometry.NativeTheta.Paired.injective_liftedCMEmbeddings' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeTheta.Paired.injective_liftedCMEmbeddings

/--
info: 'RHLean.Geometry.NativeTheta.Paired.exists_short_integral_HHa_spanning_family' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeTheta.Paired.exists_short_integral_HHa_spanning_family

/--
info: 'RHLean.Analysis.NativeQuadraticDifferent.different_eq_span_root' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.NativeQuadraticDifferent.different_eq_span_root

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.principalIdentity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.principalIdentity

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.xi_im_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.xi_im_pos

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.coefficientIdeal_projective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.coefficientIdeal_projective

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.integralTraceForm_bijective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.integralTraceForm_bijective

/--
info: 'RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_exists_principalPolarizationArithmetic' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_exists_principalPolarizationArithmetic

/--
info: 'RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_exists_polarizationCoefficientLattice' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_exists_polarizationCoefficientLattice

/--
info: 'RHLean.Analysis.alpogeNativeAlternatingSignal_even_window' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.alpogeNativeAlternatingSignal_even_window

/--
info: 'RHLean.Analysis.alpogeSquareRootArithmeticJet_sharp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.alpogeSquareRootArithmeticJet_sharp

/--
info: 'RHLean.Analysis.alpogeNativeAdditiveWheel_rectangular_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.alpogeNativeAdditiveWheel_rectangular_abs_le

/--
info: 'RHLean.Analysis.NativeCommutatorConditioning.joint_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.NativeCommutatorConditioning.joint_injective

/--
info: 'RHLean.Analysis.NativeCommutatorConditioning.coercive' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.NativeCommutatorConditioning.coercive

/--
info: 'RHLean.Analysis.NativeCommutatorConditioning.exponential_constant_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.NativeCommutatorConditioning.exponential_constant_lower_bound
