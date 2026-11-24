import RHLean.Analysis.AlpogeNativeSquareCandidateCapacity
import RHLean.Analysis.AlpogeNativeSquareMultiplicity
import RHLean.Geometry.NativeSquareCapacityPeriod
import «research.NATIVE_SQUARE_WEIGHTED_RECOVERY_20261123»

/-!
# Native square recovery and completed-capacity audit

The source identity, two-channel recovery, exact cost, and scalar size
realization are audited independently. None of these roots is a proof of the
open complete source bound. In particular, the explicit implication about
candidate removal retains that inequality as its stated right-hand side.
-/

#check RHLean.Analysis.nativeAlpogeGz_eq_candidateCapacity_sub_removal
#check RHLean.Analysis.nativeAlpogeGz_eq_squarePrefixCapacity_sub_removal
#check RHLean.Analysis.nativeAlpogeGz_le_iff_candidateRemoval
#check RHLean.Analysis.nativeSquareProperPowerCapacity_linear_lower
#check RHLean.Analysis.nativeSquareWeightedRecovery
#check RHLean.Analysis.nativeSquareWeightedRecovery_energy
#check RHLean.Analysis.nativeSquarePrimeWeight_full_energy_equality
#check RHLean.Analysis.alpogeNativeRestSize_of_squareClock
#check RHLean.Analysis.alpogeNativeSquareMultiplicity_pageN_eventually
#check RHLean.Analysis.AlpogeNativeSignedSlope.physicalTopExcess_div_le_errorTerm_of_period_lower

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let roots : Array Name := #[
    ``RHLean.Analysis.nativeAlpogeGz_eq_candidateCapacity_sub_removal,
    ``RHLean.Analysis.nativeAlpogeGz_eq_squarePrefixCapacity_sub_removal,
    ``RHLean.Analysis.nativeAlpogeGz_le_iff_candidateRemoval,
    ``RHLean.Analysis.nativeSquareCandidateCapacity_change_eq_removal_change,
    ``RHLean.Analysis.nativeSquarePrefixCandidates_full_eq_primes,
    ``RHLean.Analysis.nativeSquareProperPowerCapacity_linear_lower,
    ``RHLean.Analysis.nativeSquareWeightedRecovery,
    ``RHLean.Analysis.nativeSquareWeightedRecovery_energy,
    ``RHLean.Analysis.nativeSquarePrimeWeight_full_energy_equality,
    ``RHLean.Geometry.nativeSquareRecoveryNumerator_mul_matrix,
    ``RHLean.Geometry.nativeSquareRecoveryMatrix_no_integral_left_inverse,
    ``RHLean.Analysis.AlpogeNativeRestSize.source_scale_le_host_sq,
    ``RHLean.Analysis.alpogeNativeSquareMultiplicity_bounds,
    ``RHLean.Analysis.alpogeNativeSquareMultiplicity_lattice_sizes,
    ``RHLean.Analysis.alpogeNativeRestSize_of_squareClock,
    ``RHLean.Analysis.alpogeNativeSquareMultiplicity_pageN_of_largeX,
    ``RHLean.Analysis.alpogeNativeSquareMultiplicity_pageN_eventually,
    ``RHLean.Geometry.AlpogeSignedSlope.Formalism.LFunctionChainParameters.WeightedSlopeBounds.nativeDivisorDebt_of_period_lower,
    ``RHLean.Geometry.AlpogeSignedSlope.Formalism.LFunctionChainParameters.WeightedSlopeBounds.nativeGa_bound_of_divisorDebt,
    ``RHLean.Geometry.AlpogeSignedSlope.Formalism.LFunctionChainParameters.WeightedSlopeBounds.nativeMean_bound_of_divisorDebt,
    ``RHLean.Geometry.AlpogeSignedSlope.Formalism.LFunctionChainParameters.WeightedSlopeBounds.nativeMean_bound_of_period_lower,
    ``RHLean.Analysis.alpogeNativePeriodDebt_div_projectionDivisor,
    ``RHLean.Analysis.AlpogeNativeSignedSlope.physicalTopExcess_div_le_errorTerm_of_period_lower]
  let env ← getEnv
  for root in roots do
    unless env.contains root do
      throwError "Missing native square declaration: {root}"
    let axioms ← liftCoreM (Lean.collectAxioms root)
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unapproved terminal axiom for {root}: {ax}"
    logInfo m!"PASS native square recovery and cost {root}: {axioms}"
