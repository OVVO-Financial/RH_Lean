import RHLean.Geometry.NativeCMPeriodComparison
import RHLean.Geometry.NativeCMSerreEquationPoints
import RHLean.Geometry.NativeCMAllPlaceEigenlineDegree
import RHLean.Geometry.NativeCMIsogenyDerivativeNorm
import RHLean.Geometry.NativeCMWeierstrassOriginSymmetry
import RHLean.Geometry.NativeCMWeierstrassOriginSections
import RHLean.Geometry.NativeCMWeierstrassTranslationScheme
import RHLean.Geometry.NativeCMSerreSchemeEigenline
import RHLean.Geometry.NativeCMWeierstrassAnalyticTangent
import RHLean.Geometry.NativeCMArithmeticPeriod
import RHLean.Geometry.NativeMeasuredComponentNorm
import RHLean.Geometry.NativeThetaCuspTensorVacua
import RHLean.Geometry.NativeThetaCuspSeriesInjective
import RHLean.Geometry.NativeThetaCuspHeisenberg
import Lean.Util.CollectAxioms

/-!
# Native CM and measured-degree supplier audit

These roots retain the original projective module, actual integral seed
scheme, periods, tensor points, pure-block signs, ranks and measured masses.
They do not assert a represented polarized Serre scheme, the arithmetic
Lie-to-class-group mean comparison, the global cusp family, or the complete
signed-source inequality.
-/

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let roots : Array Name := #[
    ``RHLean.Geometry.NativeCM.finrank_int_eq_mul_of_finite,
    ``RHLean.Geometry.NativeCM.isDedekindDomain_OK,
    ``RHLean.Geometry.NativeCM.existsUnique_coord,
    ``RHLean.Geometry.NativeCM.OK_isDedekindDomain_and_projective,
    ``RHLean.Geometry.NativeCM.orderIntegerRingEquiv_inclusion,
    ``RHLean.Geometry.NativeCM.orderIntegerRingEquiv_generator,
    ``RHLean.Analysis.AlpogeThin.nativeDyadicCMOrderEquiv_inclusion,
    ``RHLean.Analysis.AlpogeThin.nativeDyadicCMOrderEquiv_generator,
    ``RHLean.Geometry.NativeCMPeriodComparison.volume_mul_det_eq_one_of_unimodular,
    ``RHLean.Geometry.NativeCMPeriodComparison.isPeriod_covolume_mul_det_eq_one,
    ``RHLean.Analysis.AlpogeThin.nativeDyadicPrescribedPeriod_exists_exact_covolume,
    ``RHLean.Geometry.NativeCM.EllipticSeed.constructed_polarized_seed,
    ``RHLean.Geometry.NativeCM.EllipticSeed.lattice_eq_span_upperPeriod,
    ``RHLean.Geometry.NativeCM.EllipticSeed.periodPair_lattice,
    ``RHLean.Geometry.NativeCM.EllipticSeed.isIntegral_modularJ_upperPeriod,
    ``RHLean.Geometry.NativeCM.Weierstrass.exists_integral_equation_for_seed,
    ``RHLean.Geometry.NativeCM.Weierstrass.exists_integral_equation_with_exact_period_invariants,
    ``RHLean.Geometry.NativeCM.Weierstrass.exists_integral_point_uniformization,
    ``RHLean.Geometry.NativeCM.EllipticSeed.equationExponential_coordinates,
    ``RHLean.Geometry.NativeCM.EllipticSeed.equationCMAction_quadratic,
    ``RHLean.Geometry.NativeCM.SchemeTheory.WeierstrassLie.integral_tangent_coordinate,
    ``RHLean.Geometry.NativeCM.SchemeTheory.schemeExponential_kernel,
    ``RHLean.Geometry.NativeCM.SchemeTheory.exists_integral_group_scheme_seed,
    ``RHLean.Geometry.NativeCM.WeierstrassTangent.originZ_hasDerivAt,
    ``RHLean.Geometry.NativeCM.WeierstrassTangent.originW_hasDerivAt,
    ``RHLean.Geometry.NativeCM.WeierstrassTangent.scaled_origin_firstJet_eq_integralVector,
    ``RHLean.Geometry.NativeCM.WeierstrassTangent.actual_exponential_origin_coordinates,
    ``RHLean.Geometry.NativeCM.WeierstrassTangent.exists_integral_group_scheme_seed_with_exact_tangent,
    ``RHLean.Geometry.NativeCM.PeriodArithmetic.KroneckerLimit.summable_and_abs_tsum_sub_integral_le,
    ``RHLean.Geometry.NativeCM.PeriodArithmetic.tendsto_realEisenstein_sub_pole,
    ``RHLean.Geometry.NativeCM.PeriodArithmetic.dedekindZeta_eq_mul_LFunction,
    ``RHLean.Geometry.NativeCM.PeriodArithmetic.chowla_selberg_lattice,
    ``RHLean.Geometry.NativeCM.quadraticField_discr,
    ``RHLean.Geometry.NativeCM.seedPeriod_eq_image_one,
    ``RHLean.Geometry.NativeCM.exact_metric_scale_log,
    ``RHLean.Geometry.NativeCM.exists_idealClassPeriods_with_seed,
    ``RHLean.Geometry.NativeCM.exists_kForm,
    ``RHLean.Geometry.NativeCM.kLin_dual_frame,
    ``RHLean.Geometry.NativeCM.kLin_diagonal,
    ``RHLean.Geometry.NativeCM.TraceFrame.proj_incl,
    ``RHLean.Geometry.NativeCM.TraceFrame.matrix_mul_self,
    ``RHLean.Geometry.NativeCM.TraceFrame.tensor_proj_incl,
    ``RHLean.Geometry.NativeCM.TraceFrame.tensorIdempotent_comp_self,
    ``RHLean.Geometry.NativeCM.TraceFrame.tensorEquivFixed,
    ``RHLean.Geometry.NativeCM.complex_fibre_rank,
    ``RHLean.Geometry.NativeCM.datum_complex_fibre_rank,
    ``RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.coefficientSerreFixedEquiv_tmul,
    ``RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.coefficient_serre_rank,
    ``RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.coefficient_complex_fibre_rank,
    ``RHLean.Analysis.AlpogeThin.nativeDyadicHost_exists_coefficientSerreConstruction,
    ``RHLean.Geometry.NativeCM.embed_eq_of_inPsi,
    ``RHLean.Geometry.NativeCM.EllipticSeed.serreExponential_ker,
    ``RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.pureSerrePeriod_bijective,
    ``RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.pureSerreExponential_ker,
    ``RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.purePeriodQuotientEquiv,
    ``RHLean.Analysis.AlpogeThin.nativeDyadicHost_exists_serrePeriods,
    ``RHLean.Analysis.AlpogeThin.nativeDyadic_seedOrientation,
    ``RHLean.Analysis.AlpogeThin.nativeDyadic_coefficientSerreMetric_im,
    ``RHLean.Analysis.AlpogeThin.nativeDyadic_coefficientSerreMetric,
    ``RHLean.Analysis.AlpogeThin.nativeDyadicHost_exists_mixedSerrePeriods,
    ``RHLean.Geometry.NativeCM.EllipticSeed.equationTensorEquiv_smul,
    ``RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.exists_prescribedEquationExponential,
    ``RHLean.Analysis.AlpogeThin.nativeDyadicHost_exists_serreEquationPoints,
    ``RHLean.Geometry.NativeCM.SerreEigenlattice.single_mem_span_iff_of_pairing,
    ``RHLean.Geometry.NativeCM.SerreEigenlattice.relative_trace_root,
    ``RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.coefficient_kLin_sum,
    ``RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.integralEvaluation_injective,
    ``RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.integralEvaluation_range,
    ``RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.eigenCoordinate_range,
    ``RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.eigenCoordinateEquiv,
    ``RHLean.Analysis.AlpogeThin.nativeDyadicHost_exists_integralSerreEigenlattice,
    ``RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.coefficientDifferent_eq_conjHalf,
    ``RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.coefficientDifferent_degree_correction,
    ``RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.coefficientDifferent_baseChange_logNorm,
    ``RHLean.Geometry.NativeCM.LineDegree.degree_baseNorm,
    ``RHLean.Geometry.NativeCM.LineDegree.lineNorm_hasGram,
    ``RHLean.Geometry.NativeCM.LineDegree.degree_lineNorm,
    ``RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.coefficientDifferent_line_degree,
    ``RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.coefficientDifferent_extended_line_degree,
    ``RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.eigenCoordinate_line_degree,
    ``RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.twistedBlockSplit_trace,
    ``RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.twice_coefficient_trace_halfRoot_eq_sum_sq,
    ``RHLean.Analysis.AlpogeThin.nativeDyadicHalfRoot_pureBlockPositivity,
    ``RHLean.Geometry.NativeMeasuredComponentDegree.degree_scale,
    ``RHLean.Geometry.NativeMeasuredComponentDegree.OrthogonalSum.rkK_deg_iSup,
    ``RHLean.Geometry.NativeMeasuredComponentDegree.Restriction.restrict_deg,
    ``RHLean.Geometry.NativeMeasuredComponentNorm.degree_eq_componentDegree_sub_mass,
    ``RHLean.Geometry.NativeMeasuredComponentNorm.rank_degree_iSup_of_measured_supports,
    ``RHLean.Geometry.NativeMeasuredComponentNorm.rank_degree_iSup_with_measured_masses,
    ``RHLean.Geometry.NativeTheta.Cusp.haar_eq_haarAt,
    ``RHLean.Geometry.NativeTheta.Cusp.ip_self_nonneg_and_bounds,
    ``RHLean.Geometry.NativeTheta.Cusp.Vac.vacuum,
    ``RHLean.Geometry.NativeTheta.Cusp.isSB_algebra_haar_linear,
    ``RHLean.Geometry.NativeTheta.Cusp.heisS_laws,
    ``RHLean.Geometry.NativeTheta.Cusp.NativeVacuum.coordinates_pairing,
    ``RHLean.Geometry.NativeTheta.Cusp.NativeVacuum.coordinates_selfDual,
    ``RHLean.Geometry.NativeTheta.Cusp.NativeVacuum.exists_native_vacuum,
    ``RHLean.Geometry.NativeTheta.Cusp.RationalCoordinates.coord_integral,
    ``RHLean.Geometry.NativeTheta.Cusp.RationalCoordinates.coord_pairing,
    ``RHLean.Geometry.NativeTheta.Cusp.RationalCoordinates.action_adjoint,
    ``RHLean.Geometry.NativeTheta.Cusp.RationalCoordinates.commonPhase_integral,
    ``RHLean.Geometry.NativeTheta.Cusp.RationalCoordinates.commonPhase_add_of_integral,
    ``RHLean.Geometry.NativeTheta.Cusp.SplitLevel.five_prime_ne_conj,
    ``RHLean.Geometry.NativeTheta.Cusp.SplitLevel.exists_five_split_level,
    ``RHLean.Geometry.NativeTheta.Cusp.SplitLevel.exists_five_split_level_generators,
    ``RHLean.Geometry.NativeCM.SchemeTheory.WeierstrassCurve.originOpen_sup_coordOpen_two,
    ``RHLean.Geometry.NativeCM.SchemeTheory.WeierstrassCurve.originLB_isLB,
    ``RHLean.Geometry.NativeCM.SchemeTheory.WeierstrassCurve.nonzeroLocus_originSec,
    ``RHLean.Geometry.NativeCM.AllPlaceTangentPeriod.placeExponential_exact_tangent,
    ``RHLean.Geometry.NativeCM.AllPlaceTangentPeriod.placeExponential_ker,
    ``RHLean.Geometry.NativeCM.AllPlaceTangentPeriod.discriminant_scale,
    ``RHLean.Geometry.NativeCM.AllPlaceTangentPeriod.neg_log_placeProfile,
    ``RHLean.Geometry.NativeCM.AllPlaceTangentPeriod.embeddingProfile_conjugate,
    ``RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.eigenCoordinate_actualPeriod_degree,
    ``RHLean.Geometry.NativeCM.IsogenyDerivativeNorm.exists_span_singleton_eq_map_of_integral,
    ``RHLean.Geometry.NativeCM.IsogenyDerivativeNorm.sum_log_norm_embedding_eq_finrank_mul_log_absNorm,
    ``RHLean.Geometry.NativeTheta.Cusp.Ambient.equiv_pairing,
    ``RHLean.Geometry.NativeTheta.Cusp.Ambient.equiv_action,
    ``RHLean.Geometry.NativeTheta.Cusp.ShiftedLattice.exists_five_shifted_selfDual,
    ``RHLean.Geometry.NativeTheta.Cusp.ShiftedPhase.prescribed_commonPhase,
    ``RHLean.Geometry.NativeTheta.Cusp.ShiftedPhase.phase_add,
    ``RHLean.Geometry.NativeTheta.Cusp.ShiftedPhase.phase_sq,
    ``RHLean.Geometry.NativeCM.EllipticSeed.rescaledPeriods_g₂_eq_invariant,
    ``RHLean.Geometry.NativeCM.EllipticSeed.rescaledPeriods_g₃_eq_invariant,
    ``RHLean.Geometry.NativeCM.EllipticSeed.rescaledCMAction_equationCMAction,
    ``RHLean.Geometry.NativeCM.Weierstrass.exists_integral_seed_with_rational_cm_action,
    ``RHLean.Geometry.NativeTheta.Cusp.FiniteOverlap.Good.proj,
    ``RHLean.Geometry.NativeTheta.Cusp.FiniteOverlap.Good.overlap,
    ``RHLean.Geometry.NativeTheta.Cusp.ShiftedVacua.good_lattice,
    ``RHLean.Geometry.NativeTheta.Cusp.ShiftedVacua.exists_native_shifted_vacua,
    ``RHLean.Geometry.NativeCM.SchemeTheory.WeierstrassCurve.isRegularSec_originSec,
    ``RHLean.Geometry.NativeCM.SchemeTheory.WeierstrassCurve.eq_comp_zero_iff,
    ``RHLean.Geometry.NativeCM.SchemeTheory.WeierstrassCurve.originLB_rigidified,
    ``RHLean.Geometry.NativeCM.SchemeTheory.WeierstrassCurve.originLB_inversion_isomorphic,
    ``RHLean.Geometry.NativeCM.SchemeTheory.WeierstrassCurve.existsUnique_eq_const_mul_originSec,
    ``RHLean.Geometry.NativeCM.Weierstrass.rescaled_model_defined_over_same_field,
    ``RHLean.Geometry.NativeCM.Weierstrass.normalized_change_defined_over_same_field,
    ``RHLean.Geometry.NativeCM.EllipticSeed.normalizedEquationPointEquiv_eq,
    ``RHLean.Geometry.NativeCM.SchemeTheory.WeierstrassCurve.translationIso,
    ``RHLean.Geometry.NativeCM.SchemeTheory.WeierstrassCurve.translationOverIso,
    ``RHLean.Geometry.NativeCM.Weierstrass.normalized_seed_scheme_comparison,
    ``RHLean.Geometry.NativeCM.SerreScheme.Pts.isLinearHom_homOfNat,
    ``RHLean.Geometry.NativeCM.TraceFrame.schemeIdempotent_comp_self,
    ``RHLean.Geometry.NativeCM.TraceFrame.schemeIsTensor,
    ``RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.coefficientSerreSchemeTensor,
    ``RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.coefficientSerreSchemeFullAction_tmul,
    ``RHLean.Geometry.NativeCM.SchemeTheory.epsScale_add_comp,
    ``RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.coefficientSerreScheme_exists_integralLie,
    ``RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.coefficientLieEigenCoordinateEquiv,
    ``RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.coefficientLieEigenCoordinate_actualPeriod_degree,
    ``RHLean.Geometry.NativeTheta.Cusp.AuxiliaryLattices.exists_dual_family,
    ``RHLean.Geometry.NativeTheta.Cusp.TensorLattices.tens_selfDual,
    ``RHLean.Geometry.NativeTheta.Cusp.TensorLattices.phase_semichar,
    ``RHLean.Geometry.NativeTheta.Cusp.TensorLattices.tens_relative_indices,
    ``RHLean.Geometry.NativeTheta.Cusp.TensorVacua.exists_native_tensor_vacua,
    ``RHLean.Geometry.NativeTheta.Cusp.SiegelSum.summable_norm_thetaTerm,
    ``RHLean.Geometry.NativeTheta.Cusp.eq_of_thS_eq]
  let env ← getEnv
  for root in roots do
    unless env.contains root do
      throwError "Missing native CM supplier: {root}"
    let axioms ← liftCoreM (Lean.collectAxioms root)
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Forbidden terminal axiom {ax} in {root}"
    logInfo m!"NATIVE_CM_AXIOM_OK {root}: {axioms}"
