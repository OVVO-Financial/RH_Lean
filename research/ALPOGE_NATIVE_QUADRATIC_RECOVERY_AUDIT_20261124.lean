import RHLean.Analysis.AlpogeNativeQuadraticRecovery

/-! Actual finite curvature and cost inequalities. Neither assumes the
critical Gz bound. The application to RH still requires the actual
compatible family, including the missing complete signed excess. -/

#check RHLean.Analysis.alpogeNative_mul_log_tangent_debt
#check RHLean.Analysis.alpogeNativePrincipalPrimeSum_tangent_lower
#check RHLean.Analysis.alpogeNativeGzArithmetic_tangent_lower
#check RHLean.Analysis.alpogeNativeGzArithmetic_le_mean_add_quadratic
#check RHLean.Analysis.alpogeNativeGzArithmetic_le_mean_add_variance
#check RHLean.Analysis.alpogeNativeNormalizedCosts_le_jointRatios

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let roots : Array Name := #[``RHLean.Analysis.alpogeNative_mul_log_tangent_debt,
    ``RHLean.Analysis.alpogeNativePrincipalPrimeSum_tangent_lower,
    ``RHLean.Analysis.alpogeNativeGzArithmetic_tangent_lower,
    ``RHLean.Analysis.alpogeNativeGzArithmetic_le_mean_add_quadratic,
    ``RHLean.Analysis.alpogeNativeGzArithmetic_le_mean_add_variance,
    ``RHLean.Analysis.alpogeNativeNormalizedCosts_le_jointRatios]
  let env ← getEnv
  for root in roots do
    unless env.contains root do
      throwError "Missing native declaration: {root}"
    let axioms ← liftCoreM (Lean.collectAxioms root)
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unapproved terminal axiom for {root}: {ax}"
    logInfo m!"PASS native quadratic recovery {root}: {axioms}"
