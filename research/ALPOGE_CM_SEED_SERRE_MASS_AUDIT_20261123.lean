import RHLean.Geometry.NativeCMQuadraticOrder
import RHLean.Geometry.NativeCMPeriodComparison
import RHLean.Geometry.NativeCMEllipticPolarization
import RHLean.Geometry.NativeCMHermitianForm
import RHLean.Geometry.NativeCMSerreTensor
import RHLean.Geometry.NativeCMSerrePeriods
import RHLean.Geometry.NativeCMSerrePolarization
import RHLean.Geometry.NativeCMWeierstrassSeedComparison
import RHLean.Geometry.NativeCMPureBlockPositivity
import RHLean.Geometry.NativeMeasuredComponentNorm
import RHLean.Geometry.NativeThetaCuspNativeVacuum
import Lean.Util.CollectAxioms

/-!
# Native CM and measured-degree supplier audit

These roots retain the original projective module, periods, tensor points,
pure-block signs, ranks and measured masses. They do not assert algebraic
representability, the arithmetic Chowla--Selberg period, the global cusp
family, or the complete signed-source inequality.
-/

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let roots : Array Name := #[
    ``RHLean.Geometry.NativeCM.finrank_int_eq_mul_of_finite,
    ``RHLean.Geometry.NativeCM.isDedekindDomain_OK,
    ``RHLean.Geometry.NativeCM.existsUnique_coord,
    ``RHLean.Geometry.NativeCM.OK_isDedekindDomain_and_projective,
    ``RHLean.Geometry.NativeCMPeriodComparison.volume_mul_det_eq_one_of_unimodular,
    ``RHLean.Geometry.NativeCMPeriodComparison.isPeriod_covolume_mul_det_eq_one,
    ``RHLean.Analysis.AlpogeThin.nativeDyadicPrescribedPeriod_exists_exact_covolume,
    ``RHLean.Geometry.NativeCM.EllipticSeed.constructed_polarized_seed,
    ``RHLean.Geometry.NativeCM.EllipticSeed.lattice_eq_span_upperPeriod,
    ``RHLean.Geometry.NativeCM.EllipticSeed.periodPair_lattice,
    ``RHLean.Geometry.NativeCM.EllipticSeed.isIntegral_modularJ_upperPeriod,
    ``RHLean.Geometry.NativeCM.Weierstrass.exists_integral_equation_for_seed,
    ``RHLean.Geometry.NativeCM.Weierstrass.exists_integral_equation_with_exact_period_invariants,
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
    ``RHLean.Geometry.NativeTheta.Cusp.NativeVacuum.coordinates_pairing,
    ``RHLean.Geometry.NativeTheta.Cusp.NativeVacuum.coordinates_selfDual,
    ``RHLean.Geometry.NativeTheta.Cusp.NativeVacuum.exists_native_vacuum]
  let env ← getEnv
  for root in roots do
    unless env.contains root do
      throwError "Missing native CM supplier: {root}"
    let axioms ← liftCoreM (Lean.collectAxioms root)
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Forbidden terminal axiom {ax} in {root}"
    logInfo m!"NATIVE_CM_AXIOM_OK {root}: {axioms}"
