import RHLean.Geometry.NativeCMQuadraticOrder
import RHLean.Geometry.NativeCMPeriodComparison
import Lean.Util.CollectAxioms

/-!
# Native CM construction: exact dependency and terminal-axiom audit

The audited declarations construct the actual quadratic order and preserve
the finite projective native module under restriction of scalars. Further
period, tensor and measured-degree suppliers are added as they are built.
No global cusp family, arithmetic CM degree or universal bound is assumed
to have been constructed by these finite algebraic conclusions.
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
    ``RHLean.Analysis.AlpogeThin.nativeDyadicPrescribedPeriod_exists_exact_covolume]
  let env ← getEnv
  for root in roots do
    unless env.contains root do
      throwError "Missing native CM supplier: {root}"
    let axioms ← liftCoreM (Lean.collectAxioms root)
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Forbidden terminal axiom {ax} in {root}"
    logInfo m!"NATIVE_CM_AXIOM_OK {root}: {axioms}"
