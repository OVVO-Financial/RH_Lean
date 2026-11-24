import RHLean.Analysis.AlpogeNativeQuadraticRecovery
import RHLean.Geometry.NativeSquareReducedRankRealization

/-! Actual finite curvature and cost inequalities. Neither assumes the
critical Gz bound. The application to RH still requires the actual
compatible family, including the missing complete signed excess. -/

#check RHLean.Analysis.alpogeNative_mul_log_tangent_debt
#check RHLean.Analysis.alpogeNativePrincipalPrimeSum_tangent_lower
#check RHLean.Analysis.alpogeNativeGzArithmetic_tangent_lower
#check RHLean.Analysis.alpogeNativeGzArithmetic_le_mean_add_quadratic
#check RHLean.Analysis.alpogeNativeGzArithmetic_le_mean_add_variance
#check RHLean.Analysis.alpogeNativeNormalizedCosts_le_jointRatios
#check RHLean.Analysis.alpogeNativeGzArithmetic_le_of_centeredJointRatios
#check RHLean.Analysis.AlpogeThin.nativeSquareReduced_chain_size
#check RHLean.Analysis.AlpogeThin.nativeSquareHost_exists_lattice_theta_reduced

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let roots : Array Name := #[``RHLean.Analysis.alpogeNative_mul_log_tangent_debt,
    ``RHLean.Analysis.alpogeNativePrincipalPrimeSum_tangent_lower,
    ``RHLean.Analysis.alpogeNativeGzArithmetic_tangent_lower,
    ``RHLean.Analysis.alpogeNativeGzArithmetic_le_mean_add_quadratic,
    ``RHLean.Analysis.alpogeNativeGzArithmetic_le_mean_add_variance,
    ``RHLean.Analysis.alpogeNativeNormalizedCosts_le_jointRatios,
    ``RHLean.Analysis.alpogeNativeGzArithmetic_le_of_centeredJointRatios,
    ``RHLean.Analysis.AlpogeThin.nativeSquareReduced_chain_size,
    ``RHLean.Analysis.AlpogeThin.nativeSquareHost_exists_lattice_theta_reduced]
  let env ← getEnv
  for root in roots do
    unless env.contains root do
      throwError "Missing native declaration: {root}"
    let axioms ← liftCoreM (Lean.collectAxioms root)
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unapproved terminal axiom for {root}: {ax}"
    logInfo m!"PASS native quadratic recovery {root}: {axioms}"
