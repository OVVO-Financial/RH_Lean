import RHLean.Analysis.AlpogeNativeSignedSlopeComparison
import RHLean.Analysis.AlpogeNativeLocalGainSource
import RHLean.Geometry.NativeOneSidedIsogenyNorm

/-!
# Native physical supplier reductions: terminal-axiom audit

The norm inequalities assume reverse derivative integrality on a specified
ideal, not a norm or period bound. The physical comparison assumes the
stated mean losses and the other geometric inputs. This audit verifies the
logical dependencies of those implications; it does not construct their
physical premises or certify the open critical signed-source bound.
-/

#check RHLean.Geometry.NativeOneSidedIsogenyNorm.abs_norm_le_absNorm_of_reverse_integral
#check RHLean.Geometry.NativeOneSidedIsogenyNorm.abs_norm_le_absNorm_pow_of_reverse_integral
#check RHLean.Geometry.NativeOneSidedIsogenyNorm.sum_log_norm_embedding_le_finrank_mul_log_absNorm_of_reverse_integral
#check RHLean.Geometry.NativeOneSidedIsogenyNorm.quadratic_period_row_correction_nonpos
#check RHLean.Analysis.AlpogeNativeSignedSlope.physicalTopExcess_le_errorTerm_of_meanLoss
#check RHLean.Analysis.AlpogeNativeSignedSlope.physicalTopExcess_div_le_normalizedGeometricCosts_of_meanLoss
#check RHLean.Analysis.AlpogeThin.nativeDyadicLocalActivePowers_card_le_log
#check RHLean.Analysis.AlpogeThin.nativeDyadicLocalExcludedSource_eq_lowCentralRemainder
#check RHLean.Analysis.AlpogeThin.nativeDyadicDe_re_le_localRetainedSource

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let roots : Array Name := #[
    ``RHLean.Geometry.NativeOneSidedIsogenyNorm.abs_norm_le_absNorm_of_reverse_integral,
    ``RHLean.Geometry.NativeOneSidedIsogenyNorm.abs_norm_le_absNorm_pow_of_reverse_integral,
    ``RHLean.Geometry.NativeOneSidedIsogenyNorm.sum_log_norm_embedding_le_finrank_mul_log_absNorm_of_reverse_integral,
    ``RHLean.Geometry.NativeOneSidedIsogenyNorm.quadratic_period_row_correction_nonpos,
    ``RHLean.Analysis.AlpogeNativeSignedSlope.physicalTopExcess_le_errorTerm_of_meanLoss,
    ``RHLean.Analysis.AlpogeNativeSignedSlope.physicalTopExcess_div_le_normalizedGeometricCosts_of_meanLoss,
    ``RHLean.Analysis.AlpogeThin.nativeDyadicLocalActivePowers_card_le_log,
    ``RHLean.Analysis.AlpogeThin.nativeDyadicLocalExcludedSource_eq_lowCentralRemainder,
    ``RHLean.Analysis.AlpogeThin.nativeDyadicDe_re_le_localRetainedSource]
  let env ← getEnv
  for root in roots do
    unless env.contains root do
      throwError "Missing native declaration: {root}"
    let axioms ← liftCoreM (Lean.collectAxioms root)
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unapproved terminal axiom for {root}: {ax}"
    logInfo m!"PASS native physical supplier reduction {root}: {axioms}"
