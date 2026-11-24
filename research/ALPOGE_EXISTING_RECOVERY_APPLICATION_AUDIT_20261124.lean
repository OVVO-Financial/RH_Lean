import RHLean.Analysis.AlpogeThin.NativeExistingRecoveryPayment
import Lean.Util.CollectAxioms

/-! Application of the actual upstream recovery/compatibility results.
The physical family must still supply the exceptional sets, their operator
ties, global degree and the remaining quantitative hypotheses. -/

#check RHLean.Geometry.NativeServedPrimeLength.allButLE_restrict
#check RHLean.Geometry.NativeServedPrimeLength.allButLE_inverse_shift
#check RHLean.Geometry.NativeServedPrimeLength.fractionIntersection_saturated
#check RHLean.Geometry.NativeServedPrimeLength.lengthFromAllBut_of_sandwich
#check RHLean.Analysis.AlpogeThin.nativeConstructedDyadicSignedSlopePayment_of_meanLoss
#check RHLean.Analysis.AlpogeThin.nativeOriginalHeightWindow
#check RHLean.Geometry.AlpogeSignedSlope.Formalism.LFunctionChainParameters.WeightedSlopeBounds.nativeDIV_of_period_lower

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let roots : Array Name := #[``RHLean.Geometry.NativeServedPrimeLength.allButLE_restrict,
    ``RHLean.Geometry.NativeServedPrimeLength.allButLE_inverse_shift,
    ``RHLean.Geometry.NativeServedPrimeLength.fractionIntersection_saturated,
    ``RHLean.Geometry.NativeServedPrimeLength.lengthFromAllBut_of_sandwich,
    ``RHLean.Analysis.AlpogeThin.nativeConstructedDyadicSignedSlopePayment_of_meanLoss,
    ``RHLean.Analysis.AlpogeThin.nativeOriginalHeightWindow,
    ``RHLean.Geometry.AlpogeSignedSlope.Formalism.LFunctionChainParameters.WeightedSlopeBounds.nativeDIV_of_period_lower]
  let env ← getEnv
  for root in roots do
    unless env.contains root do
      throwError "Missing native declaration: {root}"
    let axs ← liftCoreM (Lean.collectAxioms root)
    for ax in axs do
      unless allowed.contains ax do
        throwError "Unapproved terminal axiom for {root}: {ax}"
    logInfo m!"PASS native existing recovery application {root}: {axs}"
