import RHLean.Analysis.AlpogeThin.NativeRayIdealCounts
import RHLean.Analysis.AlpogeThin.NativeRayClassData
import RHLean.Geometry.NativePrescribedGeometricPeriod
import RHLean.Geometry.NativePeriodTypeCoordinates
import RHLean.Geometry.NativeGeometricPeriods
import RHLean.Analysis.AlpogeThin.NativeDyadicRayNorm
import RHLean.Geometry.NativePrescribedGeometricDatum
import RHLean.Geometry.NativeGeometricDatum
import RHLean.Geometry.NativePrescribedCMData
import RHLean.Geometry.NativePrescribedPolarizationDomain
import RHLean.Geometry.NativePolarizationComplexCoordinates
import RHLean.Geometry.NativeDyadicAdelicIsometry
import RHLean.Geometry.NativeDyadicAdelicNorm
import RHLean.Geometry.NativePrescribedPolarizationRealization
import RHLean.Geometry.NativePolarizationRealCoordinates
import RHLean.Geometry.NativeAdicQuadraticNorm
import RHLean.Geometry.NativeLocalQuadraticNorm
import RHLean.Analysis.AlpogeThin.NativeGeometricCostWindows
import RHLean.Geometry.NativePrescribedPolarizationLattice
import RHLean.Geometry.NativePrescribedHermitianSpaces
import RHLean.Analysis.AlpogeThin.NativeConstructedDyadicSignedSlopePayment
import RHLean.Geometry.NativeThetaEvaluatedFamily
import RHLean.Geometry.NativeThetaJetEvaluation
import RHLean.Geometry.NativeThetaLatticeNormalization
import RHLean.Analysis.AlpogeNativeSignedSlopeComparison
import RHLean.Geometry.AlpogeSignedSlope.Formalism.SizeWindowBrackets.ChainSlopeWindows.StrongErrorBound
import RHLean.Geometry.AlpogeSignedSlope.Formalism.SizeWindowBrackets.ChainSlopeWindows.LevelOfCongruence
import RHLean.Geometry.NativeDescentCostPayment
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

/--
info: 'RHLean.Geometry.nativeDescent_collectiveLog_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.nativeDescent_collectiveLog_le

/--
info: 'RHLean.Geometry.nativeDescent_heightReserve_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.nativeDescent_heightReserve_ge

/--
info: 'RHLean.Geometry.nativeDescent_collectiveNorm_eq_exp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.nativeDescent_collectiveNorm_eq_exp

/--
info: 'RHLean.Geometry.nativeDescent_collectiveNormBudget_strong' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.nativeDescent_collectiveNormBudget_strong

/--
info: 'RHLean.Geometry.nativeDescent_collectiveNormBudget_withFactor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.nativeDescent_collectiveNormBudget_withFactor

/--
info: 'RHLean.Geometry.nativeDescent_collectiveNormBudget_withFactor_of_log_le_b' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.nativeDescent_collectiveNormBudget_withFactor_of_log_le_b

/--
info: 'RHLean.Geometry.nativeDescent_collectiveNormBudget_fourPow' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.nativeDescent_collectiveNormBudget_fourPow

/--
info: 'RHLean.Geometry.nativeDescent_scaledJointEnergy_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.nativeDescent_scaledJointEnergy_le

/--
info: 'RHLean.Geometry.nativeDescent_scaledJointEnergy_fourPow_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.nativeDescent_scaledJointEnergy_fourPow_le

/--
info: 'RHLean.Geometry.AlpogeSignedSlope.Formalism.LFunctionChainParameters.WeightedSlopeBounds.uniform_bound_statement' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.AlpogeSignedSlope.Formalism.LFunctionChainParameters.WeightedSlopeBounds.uniform_bound_statement

/--
info: 'RHLean.Geometry.AlpogeSignedSlope.Formalism.LFunctionChainParameters.LErr.error_sizes' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.AlpogeSignedSlope.Formalism.LFunctionChainParameters.LErr.error_sizes

/--
info: 'RHLean.Analysis.AlpogeNativeSignedSlope.physicalData_main' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeNativeSignedSlope.physicalData_main

/--
info: 'RHLean.Analysis.AlpogeNativeSignedSlope.physicalTopExcess_eq_meanGap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeNativeSignedSlope.physicalTopExcess_eq_meanGap

/--
info: 'RHLean.Analysis.AlpogeNativeSignedSlope.physicalTopExcess_le_errorTerm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeNativeSignedSlope.physicalTopExcess_le_errorTerm

/--
info: 'RHLean.Analysis.AlpogeNativeSignedSlope.physicalTopExcess_le_strongWindowError' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeNativeSignedSlope.physicalTopExcess_le_strongWindowError

/--
info: 'RHLean.Analysis.AlpogeNativeSignedSlope.physicalTopExcess_div_le_strongWindowError' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeNativeSignedSlope.physicalTopExcess_div_le_strongWindowError

/--
info: 'RHLean.Analysis.AlpogeNativeSignedSlope.physicalTopExcess_div_le_normalizedGeometricCosts' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeNativeSignedSlope.physicalTopExcess_div_le_normalizedGeometricCosts

/--
info: 'RHLean.Geometry.NativeTheta.Lattice.standard_level' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeTheta.Lattice.standard_level

/--
info: 'RHLean.Geometry.NativeTheta.Lattice.standard_unimodular' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeTheta.Lattice.standard_unimodular

/--
info: 'RHLean.Geometry.NativeTheta.Lattice.exists_odd_level' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeTheta.Lattice.exists_odd_level

/--
info: 'RHLean.Geometry.NativeTheta.Lattice.unimodular_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeTheta.Lattice.unimodular_iff

/--
info: 'RHLean.Geometry.NativeTheta.Lattice.fg_of_level' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeTheta.Lattice.fg_of_level

/--
info: 'RHLean.Geometry.NativeTheta.Lattice.exists_short_vectors_of_level' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeTheta.Lattice.exists_short_vectors_of_level

/--
info: 'RHLean.Geometry.NativeTheta.Lattice.translationCount_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeTheta.Lattice.translationCount_eq

/--
info: 'RHLean.Geometry.NativeTheta.Lattice.intersectionIndex_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeTheta.Lattice.intersectionIndex_pos

/--
info: 'RHLean.Geometry.NativeTheta.Lattice.normalizationIndex_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeTheta.Lattice.normalizationIndex_pos

/--
info: 'RHLean.Geometry.NativeTheta.Lattice.translationCount_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeTheta.Lattice.translationCount_pos

/--
info: 'RHLean.Geometry.NativeTheta.Lattice.finite_lattice_levelQuotient' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeTheta.Lattice.finite_lattice_levelQuotient

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.coefficientIdeal_finite_levelQuotient' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.coefficientIdeal_finite_levelQuotient

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.coefficientIdeal_levelTuples_card_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.coefficientIdeal_levelTuples_card_pos

/--
info: 'RHLean.Geometry.NativeTheta.JetEvaluation.formalNablaValue_eq_contraction' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeTheta.JetEvaluation.formalNablaValue_eq_contraction

/--
info: 'RHLean.Geometry.NativeTheta.JetEvaluation.rawShortValue_eq_source_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeTheta.JetEvaluation.rawShortValue_eq_source_formula

/--
info: 'RHLean.Geometry.NativeTheta.JetEvaluation.rawShortValue_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeTheta.JetEvaluation.rawShortValue_sum

/--
info: 'RHLean.Geometry.NativeTheta.JetEvaluation.shortValueOfFormalGerms_eq_source_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeTheta.JetEvaluation.shortValueOfFormalGerms_eq_source_formula

/--
info: 'RHLean.Geometry.NativeTheta.JetEvaluation.shortValueOfFormalGerms_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeTheta.JetEvaluation.shortValueOfFormalGerms_sum

/--
info: 'RHLean.Geometry.NativeTheta.JetEvaluation.span_rawShortValue_family' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeTheta.JetEvaluation.span_rawShortValue_family

/--
info: 'RHLean.Geometry.NativeTheta.JetEvaluation.span_shortValueOfFormalGerms_family' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeTheta.JetEvaluation.span_shortValueOfFormalGerms_family

/--
info: 'RHLean.Geometry.NativeTheta.JetEvaluation.norm_rawShortValue_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeTheta.JetEvaluation.norm_rawShortValue_le

/--
info: 'RHLean.Geometry.NativeTheta.Paired.exists_short_integral_HHa_evaluation_family' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeTheta.Paired.exists_short_integral_HHa_evaluation_family

/--
info: 'RHLean.Analysis.AlpogeThin.nativeConstructedDyadicSignedSlopePayment' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeConstructedDyadicSignedSlopePayment

/--
info: 'RHLean.Geometry.NativePrescribedHermitian.diagForm_nondeg' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativePrescribedHermitian.diagForm_nondeg

/--
info: 'RHLean.Geometry.NativePrescribedHermitian.stdLat_isLattice' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativePrescribedHermitian.stdLat_isLattice

/--
info: 'RHLean.Geometry.NativePrescribedHermitian.stdLat_unimod' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativePrescribedHermitian.stdLat_unimod

/--
info: 'RHLean.Geometry.NativePrescribedHermitian.W_rank' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativePrescribedHermitian.W_rank

/--
info: 'RHLean.Geometry.NativePrescribedHermitian.W_hasSignature' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativePrescribedHermitian.W_hasSignature

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.twistedLattice_eq_pi' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.twistedLattice_eq_pi

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.twistedLattice_projective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.twistedLattice_projective

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.twistedLattice_rank' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.twistedLattice_rank

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.twistedLattice_rank_int' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.twistedLattice_rank_int

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.twistedTraceForm_cast' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.twistedTraceForm_cast

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.twistedTraceForm_bijective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.twistedTraceForm_bijective

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.twistedTraceForm_alternating' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.twistedTraceForm_alternating

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.twistedTraceForm_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.twistedTraceForm_adjoint

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.prescribedLattice_eq_source' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.prescribedLattice_eq_source

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.prescribedTraceForm_cast' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.prescribedTraceForm_cast

/--
info: 'RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_prescribed_conj' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_prescribed_conj

/--
info: 'RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_exists_prescribedPolarizationLattices' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_exists_prescribedPolarizationLattices

/--
info: 'RHLean.Analysis.AlpogeThin.NativeGeometricCostWindows.proposition_size_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeGeometricCostWindows.proposition_size_bound

/--
info: 'RHLean.Analysis.AlpogeThin.NativeGeometricCostWindows.GeometricSizeWindows.sizeWindows' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeGeometricCostWindows.GeometricSizeWindows.sizeWindows

/--
info: 'RHLean.Analysis.AlpogeThin.NativeGeometricCostWindows.sourceErrorBracket_eq_native' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeGeometricCostWindows.sourceErrorBracket_eq_native

/--
info: 'RHLean.Analysis.AlpogeThin.NativeGeometricCostWindows.normalizedCosts_add_analytic_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeGeometricCostWindows.normalizedCosts_add_analytic_le

/--
info: 'RHLean.Geometry.NativeLocalQuadraticNorm.finiteField_quadratic' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeLocalQuadraticNorm.finiteField_quadratic

/--
info: 'RHLean.Geometry.NativeLocalQuadraticNorm.henselian_quadratic_unit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeLocalQuadraticNorm.henselian_quadratic_unit

/--
info: 'RHLean.Geometry.NativeLocalQuadraticNorm.henselian_quadratic_neg_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeLocalQuadraticNorm.henselian_quadratic_neg_one

/--
info: 'RHLean.Geometry.NativeAdicQuadraticNorm.adicInt_isAdicComplete' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeAdicQuadraticNorm.adicInt_isAdicComplete

/--
info: 'RHLean.Geometry.NativeAdicQuadraticNorm.adicInt_henselian' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeAdicQuadraticNorm.adicInt_henselian

/--
info: 'RHLean.Geometry.NativeAdicQuadraticNorm.adicInt_residue_surj' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeAdicQuadraticNorm.adicInt_residue_surj

/--
info: 'RHLean.Geometry.NativeAdicQuadraticNorm.adicInt_residue_finite' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeAdicQuadraticNorm.adicInt_residue_finite

/--
info: 'RHLean.Geometry.NativeAdicQuadraticNorm.adicInt_exists_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeAdicQuadraticNorm.adicInt_exists_norm

/--
info: 'RHLean.Geometry.NativeAdicQuadraticNorm.numberField_adicInt_exists_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeAdicQuadraticNorm.numberField_adicInt_exists_norm

/--
info: 'RHLean.Geometry.NativePolarizationRealCoordinates.li1' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativePolarizationRealCoordinates.li1

/--
info: 'RHLean.Geometry.NativePolarizationRealCoordinates.two_card' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativePolarizationRealCoordinates.two_card

/--
info: 'RHLean.Geometry.NativePolarizationRealCoordinates.phi1_bijective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativePolarizationRealCoordinates.phi1_bijective

/--
info: 'RHLean.Geometry.NativePolarizationRealCoordinates.phiI_bijective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativePolarizationRealCoordinates.phiI_bijective

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.integer_mem_coefficientIdeal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.integer_mem_coefficientIdeal

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.twistedRealCoordinates_integralCoordinates' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.twistedRealCoordinates_integralCoordinates

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.twistedRealCoordinates_bijective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.twistedRealCoordinates_bijective

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.prescribedRealEquiv_tmul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.prescribedRealEquiv_tmul

/--
info: 'RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_exists_prescribedRealization' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_exists_prescribedRealization

/--
info: 'RHLean.Geometry.NativeDyadicAdelicNorm.conjugation_eq_host' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeDyadicAdelicNorm.conjugation_eq_host

/--
info: 'RHLean.Geometry.NativeDyadicAdelicNorm.theta_eq_integralHalfRoot' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeDyadicAdelicNorm.theta_eq_integralHalfRoot

/--
info: 'RHLean.Geometry.NativeDyadicAdelicNorm.alpha_beta_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeDyadicAdelicNorm.alpha_beta_norm

/--
info: 'RHLean.Geometry.NativeDyadicAdelicNorm.not_both' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeDyadicAdelicNorm.not_both

/--
info: 'RHLean.Geometry.NativeDyadicAdelicNorm.local_solution' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeDyadicAdelicNorm.local_solution

/--
info: 'RHLean.Geometry.NativeDyadicAdelicNorm.finite_primes_over_d' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeDyadicAdelicNorm.finite_primes_over_d

/--
info: 'RHLean.Geometry.NativeDyadicAdelicNorm.adele_norm_equation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeDyadicAdelicNorm.adele_norm_equation

/--
info: 'RHLean.Geometry.NativeDyadicAdelicNorm.normMinusOne_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeDyadicAdelicNorm.normMinusOne_spec

/--
info: 'RHLean.Geometry.NativeDyadicAdelicNorm.normMinusOne_isUnit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeDyadicAdelicNorm.normMinusOne_isUnit

/--
info: 'RHLean.Geometry.NativeDyadicAdelicNorm.exists_adelic_neg_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeDyadicAdelicNorm.exists_adelic_neg_one

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.prescribedBaseSpace' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.prescribedBaseSpace

/--
info: 'RHLean.Geometry.NativeDyadicAdelicIsometry.dSpace_gram_map' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeDyadicAdelicIsometry.dSpace_gram_map

/--
info: 'RHLean.Geometry.NativeDyadicAdelicIsometry.diagonalChange' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeDyadicAdelicIsometry.diagonalChange

/--
info: 'RHLean.Geometry.NativeDyadicAdelicIsometry.diagonalChange_val' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeDyadicAdelicIsometry.diagonalChange_val

/--
info: 'RHLean.Geometry.NativeDyadicAdelicIsometry.diagonalChange_inv_val' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeDyadicAdelicIsometry.diagonalChange_inv_val

/--
info: 'RHLean.Geometry.NativeDyadicAdelicIsometry.diagonalChange_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeDyadicAdelicIsometry.diagonalChange_congr

/--
info: 'RHLean.Geometry.NativeDyadicAdelicIsometry.baseSpace_congr_prescribed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeDyadicAdelicIsometry.baseSpace_congr_prescribed

/--
info: 'RHLean.Geometry.NativeDyadicAdelicIsometry.baseSpace_isometric_prescribed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeDyadicAdelicIsometry.baseSpace_isometric_prescribed

/--
info: 'RHLean.Geometry.NativePolarizationComplexCoordinates.trace_eq_sum_psi' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativePolarizationComplexCoordinates.trace_eq_sum_psi

/--
info: 'RHLean.Geometry.NativePolarizationComplexCoordinates.trace_restrict_complex' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativePolarizationComplexCoordinates.trace_restrict_complex

/--
info: 'RHLean.Geometry.NativePolarizationComplexCoordinates.diagonalJ_term_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativePolarizationComplexCoordinates.diagonalJ_term_pos

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.twistedTraceForm_realFormula' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.twistedTraceForm_realFormula

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.twistedComplexStructure_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.twistedComplexStructure_sq

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.twistedComplexStructure_isometry' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.twistedComplexStructure_isometry

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.twistedComplexStructure_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.twistedComplexStructure_pos

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.prescribedComplexStructure_properties' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.prescribedComplexStructure_properties

/--
info: 'RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_prescribed_embedding_conj' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_prescribed_embedding_conj

/--
info: 'RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_exists_prescribedDomain' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_exists_prescribedDomain

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.unram_at' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.unram_at

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.isCMUnram' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.isCMUnram

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.cmData' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.cmData

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.cmData_sig_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.cmData_sig_apply

/--
info: 'RHLean.Analysis.AlpogeThin.nativeDyadicHostCMData' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeDyadicHostCMData

/--
info: 'RHLean.Analysis.AlpogeThin.nativeDyadicHostCMData_sig' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeDyadicHostCMData_sig

/--
info: 'RHLean.Analysis.AlpogeThin.nativeDyadicHostCMData_sigR' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeDyadicHostCMData_sigR

/--
info: 'RHLean.Geometry.NativePolarizationIntegralForm.intForm_eq_of_cast' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativePolarizationIntegralForm.intForm_eq_of_cast

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.xi_eq_source_top' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.xi_eq_source_top

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.coefficientIdeal_eq_source_top' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.coefficientIdeal_eq_source_top

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.prescribedRationalTraceForm_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.prescribedRationalTraceForm_integral

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.prescribedIntForm_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.prescribedIntForm_eq

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.prescribedGeometricDomain' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.prescribedGeometricDomain

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.prescribedSign_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.prescribedSign_eq_one

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.prescribedSignedTraceForm_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.prescribedSignedTraceForm_eq

/--
info: 'RHLean.Analysis.AlpogeThin.nativeDyadicGeometricHost_rootFilter' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeDyadicGeometricHost_rootFilter

/--
info: 'RHLean.Analysis.AlpogeThin.nativeDyadicGeometricHost_bar_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeDyadicGeometricHost_bar_eq

/--
info: 'RHLean.Analysis.AlpogeThin.nativeDyadicPrescribedGeometricDatum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeDyadicPrescribedGeometricDatum

/--
info: 'RHLean.Analysis.AlpogeThin.nativeDyadicPrescribedGeometricDatum_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeDyadicPrescribedGeometricDatum_spec

/--
info: 'RHLean.Analysis.AlpogeThin.nativeDyadicHost_exists_prescribedGeometricData' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeDyadicHost_exists_prescribedGeometricData

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRawHostRayNorm.isNormOne_iff_halfRootCoordinates' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRawHostRayNorm.isNormOne_iff_halfRootCoordinates

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRawHostRayNorm.element_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRawHostRayNorm.element_norm

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRawHostRayNorm.element_mem_K' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRawHostRayNorm.element_mem_K

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRawHostRayNorm.element_sub_one_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRawHostRayNorm.element_sub_one_mem

/--
info: 'RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_rayHalfRoot' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_rayHalfRoot

/--
info: 'RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_exists_rayNormElement' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_exists_rayNormElement

/--
info: 'RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_exists_rayNormElement_of_coordinates' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_exists_rayNormElement_of_coordinates

/--
info: 'RHLean.Geometry.NativeGeometricPeriods.exists_herm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeGeometricPeriods.exists_herm

/--
info: 'RHLean.Geometry.NativeGeometricPeriods.periodOfRealEquiv_isPeriod' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativeGeometricPeriods.periodOfRealEquiv_isPeriod

/--
info: 'RHLean.Geometry.NativePeriodCoordinates.coordinates_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativePeriodCoordinates.coordinates_mul

/--
info: 'RHLean.Geometry.NativePeriodCoordinates.coordinates_diagonalJ' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativePeriodCoordinates.coordinates_diagonalJ

/--
info: 'RHLean.Geometry.NativePeriodCoordinates.typeFn_card_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativePeriodCoordinates.typeFn_card_of_mem

/--
info: 'RHLean.Geometry.NativePeriodCoordinates.typeFn_card_of_not_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Geometry.NativePeriodCoordinates.typeFn_card_of_not_mem

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.twistedPeriodRealEquiv_complexStructure' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.twistedPeriodRealEquiv_complexStructure

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.prescribedPeriodType_isTypeFn' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.prescribedPeriodType_isTypeFn

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.prescribedPeriod_isPeriod' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.prescribedPeriod_isPeriod

/--
info: 'RHLean.Analysis.AlpogeThin.nativeDyadicPrescribedGeometricDatum_isPeriod' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeDyadicPrescribedGeometricDatum_isPeriod

/--
info: 'RHLean.Analysis.AlpogeThin.nativeDyadicHost_exists_prescribedPeriods' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.nativeDyadicHost_exists_prescribedPeriods

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRay.RayCl.exists_class_residue_embedding' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRay.RayCl.exists_class_residue_embedding

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRay.RayCl.exists_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRay.RayCl.exists_inv

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRay.rayData' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRay.rayData

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRay.RayData.card_le_classNumber_mul_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRay.RayData.card_le_classNumber_mul_sq

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRay.RayData.cls_span' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRay.RayData.cls_span

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRay.RayConv.sum_lamIdeal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRay.RayConv.sum_lamIdeal

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRay.aRay_mul_log' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRay.aRay_mul_log

/--
info: 'RHLean.Analysis.AlpogeThin.NativeRay.lamRay_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Analysis.AlpogeThin.NativeRay.lamRay_nonneg
