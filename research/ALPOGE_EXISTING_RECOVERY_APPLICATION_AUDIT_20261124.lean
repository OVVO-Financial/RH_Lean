import RHLean.Analysis.AlpogeThin.NativeExistingRecoveryPayment
import RHLean.Geometry.NativeThetaFactorialDigitReadout
import RHLean.Geometry.NativeJointEvaluationRecovery
import RHLean.Analysis.AlpogeNativeThickFreezing
import Lean.Util.CollectAxioms

/-! Application of the actual upstream recovery/compatibility results.
The physical family must still supply the exceptional sets, their operator
ties, global degree and the remaining quantitative hypotheses. -/

#check RHLean.Geometry.NativeJointEvaluationRecovery.smith_mem_of_primitive_tests
#check RHLean.Geometry.NativeJointEvaluationRecovery.recovery_of_primitive_tests
#check RHLean.Geometry.NativeTheta.ExponentDigits.factorialDigitUnit_sum_readout_precision
#check RHLean.Geometry.NativeJointEvaluationRecovery.recovery_of_congruent_primitive_tests
#check RHLean.Analysis.alpogeNativeSignedWidthSource_upper_width_le
#check RHLean.Analysis.alpogeNativePhysicalSubgroupTopExcess_upper_width_le
#check RHLean.Analysis.alpogeNativePhysicalSubgroupTopExcess_logGrid_le
#check RHLean.Geometry.NativeServedPrimeLength.allButLE_restrict
#check RHLean.Geometry.NativeServedPrimeLength.allButLE_inverse_shift
#check RHLean.Geometry.NativeServedPrimeLength.fractionIntersection_saturated
#check RHLean.Geometry.NativeServedPrimeLength.lengthFromAllBut_of_sandwich
#check RHLean.Analysis.AlpogeThin.nativeConstructedDyadicSignedSlopePayment_of_meanLoss
#check RHLean.Analysis.AlpogeThin.nativeOriginalHeightWindow
#check RHLean.Analysis.AlpogeThin.nativeSquareClock_integerHeights_eq
#check RHLean.Analysis.AlpogeThin.nativeSquareClock_ceilHeight_eventually
#check RHLean.Geometry.AlpogeSignedSlope.Formalism.LFunctionChainParameters.WeightedSlopeBounds.nativeDIV_of_period_lower

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let roots : Array Name := #[``RHLean.Geometry.NativeJointEvaluationRecovery.smith_mem_of_primitive_tests,
    ``RHLean.Geometry.NativeJointEvaluationRecovery.recovery_of_primitive_tests,
    ``RHLean.Geometry.NativeTheta.ExponentDigits.factorialDigitUnit_sum_readout_precision,
    ``RHLean.Geometry.NativeJointEvaluationRecovery.recovery_of_congruent_primitive_tests,
    ``RHLean.Analysis.alpogeNativeSignedWidthSource_upper_width_le,
    ``RHLean.Analysis.alpogeNativePhysicalSubgroupTopExcess_upper_width_le,
    ``RHLean.Analysis.alpogeNativePhysicalSubgroupTopExcess_logGrid_le,
    ``RHLean.Geometry.NativeServedPrimeLength.allButLE_restrict,
    ``RHLean.Geometry.NativeServedPrimeLength.allButLE_inverse_shift,
    ``RHLean.Geometry.NativeServedPrimeLength.fractionIntersection_saturated,
    ``RHLean.Geometry.NativeServedPrimeLength.lengthFromAllBut_of_sandwich,
    ``RHLean.Analysis.AlpogeThin.nativeConstructedDyadicSignedSlopePayment_of_meanLoss,
    ``RHLean.Analysis.AlpogeThin.nativeOriginalHeightWindow,
    ``RHLean.Analysis.AlpogeThin.nativeSquareClock_integerHeights_eq,
    ``RHLean.Analysis.AlpogeThin.nativeSquareClock_ceilHeight_eventually,
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
