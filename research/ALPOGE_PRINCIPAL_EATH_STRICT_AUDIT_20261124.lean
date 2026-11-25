import RHLean.Analysis.AlpogeThin.NativePrincipalEAtH
import RHLean.Analysis.AlpogeThin.NativeConstructedDyadicGzPayment
import RHLean.Analysis.AlpogeNativeBoundHandoff
import RHLean.Geometry.NativeSquareCapacityPeriod
import RHLean.Geometry.NativeSummandCovolume
import RHLean.Geometry.NativeCore33HostDegree
import RHLean.Analysis.AlpogeThin.NativeDyadicHigherOddTail
import RHLean.Analysis.AlpogeThin.NativeDyadicPrimePowerIncidence
import RHLean.Analysis.AlpogeThin.NativeSquareDefectSelection
import RHLean.Geometry.NativeJointEvaluationRecovery
import RHLean.Geometry.NativeThetaIntegralGrid
import RHLean.Analysis.AlpogeThin.NativeDyadicInertPrimeRange
import RHLean.Analysis.AlpogeThin.NativeDyadicRamifiedWindow
import RHLean.Geometry.NativeFrobeniusHasse
import RHLean.Geometry.NativeHostIntegralJetRows
import RHLean.Geometry.NativeThetaExponentDigits
import RHLean.Geometry.NativeThetaIntegralJets
import Lean.Util.CollectAxioms

/-!
This checks actual declarations, including opaque proof terms, for the
absolute exclusion. It is not a claim that the remaining signed cost
is paid. Renamed or definitionally erased vacuous witnesses require
independent semantic review in addition to this name-based hard gate.
-/
open Lean Elab Command

private partial def strictClosure (env : Environment) (todo : List Name)
    (seen : NameSet := {}) : NameSet :=
  match todo with
  | [] => seen
  | n :: rest =>
    if seen.contains n then strictClosure env rest seen else
      let deps := match env.find? n with
        | none => []
        | some info => info.type.getUsedConstants.toList ++
            ((info.value? (allowOpaque := true)).map
              (fun e => e.getUsedConstants.toList)).getD []
      strictClosure env (deps ++ rest) (seen.insert n)

run_cmd do
  let env ← getEnv
  let roots : Array Name := #[
    `RHLean.Geometry.NativeCore33.primeOrder_le_degree,
    `RHLean.Geometry.NativeCore33.primePower_eq_one,
    `RHLean.Geometry.NativeCore33.local_unipotent_primePower,
    `RHLean.Geometry.NativeCore33.local_unipotent_eq_one,
    `RHLean.Analysis.AlpogeThin.nativeCore33_primeOrder_le,
    `RHLean.Analysis.AlpogeThin.nativeCore33_localStabilizer_eq_one,
    `RHLean.Analysis.AlpogeThin.nativeDyadic_trivialCharacter_signs,
    `RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_principalTwist,
    `RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_EAtH,
    `RHLean.Analysis.AlpogeThin.nativePrincipalEAtH_windows,
    `RHLean.Analysis.AlpogeThin.squareClock_height_mem_pairWindow,
    `RHLean.Analysis.AlpogeThin.nativePrincipalEAtH_squareClock_of_pair,
    `RHLean.Analysis.AlpogeThin.nativeConstructedDyadicGzPayment,
    `RHLean.Geometry.NativeSummandCovolume.normalized_lcv_le_of_gram_bounds,
    `RHLean.Geometry.NativeJointEvaluationRecovery.exists_decoder_of_frame_congruence,
    `RHLean.Geometry.NativeTheta.IntegralJets.recover_monomial_family,
    `RHLean.Geometry.NativeTheta.IntegralJets.formalGroupHasse_recovers_family,
    `RHLean.Geometry.NativeTheta.minorMonomial_dividedJet,
    `RHLean.Geometry.NativeTheta.ExponentDigits.card_digitIndex,
    `RHLean.Geometry.NativeTheta.ExponentDigits.card_digitFiber,
    `RHLean.Geometry.NativeTheta.ExponentDigits.factorial_digit_unit,
    `RHLean.Geometry.NativeFrobeniusHasse.det_ordinary_progression,
    `RHLean.Analysis.nativeDyadic_frobPeriod_rigid,
    `RHLean.Analysis.nativeDyadic_returning_hasse_det_isUnit,
    `RHLean.Geometry.NativeTheta.Paired.isIntegral_coeff_hermitianJet_of_unimodular,
    `RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.prescribedLattice_row_integral_iff,
    `RHLean.Analysis.AlpogeThin.nativeDyadicDPrimeASK_normalized_le_of_winPair,
    `RHLean.Analysis.AlpogeThin.nativeDyadicInertPrime_exponent_lt_of_winPair,
    `RHLean.Geometry.NativeJointEvaluationRecovery.recovery_iff_blockImage,
    `RHLean.Geometry.NativeJointEvaluationRecovery.exists_decoder_of_frame_minors,
    `RHLean.Geometry.NativeTheta.Paired.exists_coordProd_grid_addVal_le_factorial,
    `RHLean.Geometry.NativeTheta.eval_minorCombination,
    `RHLean.Geometry.NativeSummandCovolume.normalized_lcv_le_of_recovered_residues,
    `RHLean.Geometry.NativeSummandCovolume.joint_residues_of_comaximal,
    `RHLean.Geometry.NativeSummandCovolume.card_idealPower_residue_grid,
    `RHLean.Analysis.AlpogeThin.nativeDyadicFrobenius_exp_lt_order_of_short_power,
    `RHLean.Analysis.AlpogeThin.nativeDyadicLocalExcludedSource_eq_order_sum,
    `RHLean.Analysis.nativeDyadic_colourKernel_eq_incidence,
    `RHLean.Analysis.nativeDyadic_consecutive_colourIncidence_minor,
    `RHLean.Analysis.nativeDyadic_colourNormalization_coprime,
    `RHLean.Analysis.nativeDyadic_competing_dvd_of_colour_return,
    `RHLean.Analysis.AlpogeThin.nativeDyadicOddClassASK_re_eq_tail_add_complement,
    `RHLean.Analysis.AlpogeThin.nativeDyadicHigherOddTail_normalized_le,
    `RHLean.Analysis.AlpogeThin.squareClock_defectSelection_total,
    `RHLean.Geometry.AlpogeSignedSlope.Formalism.LFunctionChainParameters.WeightedSlopeBounds.NativeCoupledCount.mono,
    `RHLean.Geometry.AlpogeSignedSlope.Formalism.LFunctionChainParameters.WeightedSlopeBounds.nativeRelativeDegreeCount_le,
    `RHLean.Geometry.AlpogeSignedSlope.Formalism.LFunctionChainParameters.WeightedSlopeBounds.nativeGa_bound_of_coupled_period,
    `RHLean.Geometry.AlpogeSignedSlope.Formalism.LFunctionChainParameters.WeightedSlopeBounds.nativeMean_bound_of_coupled_period,
    `RHLean.Analysis.AlpogeNativeSignedSlope.physicalTopExcess_div_le_errorTerm_of_coupled_period,
    `RHLean.Analysis.AlpogeNativeSignedSlope.physicalTopExcess_div_le_errorTerm_of_ordered_periods,
    `RHLean.Analysis.AlpogeNativeBoundHandoff.riemannHypothesis_of_smallEpsilonWindowBound]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for root in roots do
    unless env.contains root do
      throwError "Missing actual principal source root: {root}"
    let axs ← liftCoreM (Lean.collectAxioms root)
    for a in axs do
      unless allowed.contains a do
        throwError "Forbidden axiom: {root} depends on {a}"
    let names := strictClosure env [root]
    for n in names.toList do
      let s := n.toString.toLower.replace "_" ""
      if (s.splitOn "geocl").length > 1 ||
          (s.splitOn "anygeometry").length > 1 then
        throwError "ABSOLUTE PROHIBITION: {root} depends on {n}"
    logInfo m!"PASS strict principal source dependency gate: {root}; axioms={axs}; dependencies={names.toList.length}"
