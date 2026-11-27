import «research.NativeWheelFitProjector»
import «research.NativeRankOneEulerRepayment»
import «research.NativeMeasuredCutGram»
import «research.NativeSignedWidthSweep»
import RHLean.Analysis.AlpogeThin.NativePrincipalEAtH
import RHLean.Analysis.AlpogeThin.NativeConstructedDyadicGzPayment
import RHLean.Analysis.AlpogeThin.NativeExistingRecoveryPayment
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
import RHLean.Geometry.NativeThetaFactorialDigitReadout
import RHLean.Geometry.NativeThetaHasseDigitRecovery
import RHLean.Geometry.NativeThetaInvariantPrincipalSymbol
import RHLean.Analysis.AlpogeThin.NativeDyadicGridFactorialBudget
import RHLean.Analysis.AlpogeThin.NativePrimeExponentAncestry
import RHLean.Analysis.AlpogeNativeProperPowerCentering
import RHLean.Analysis.AlpogeThin.NativeDyadicColourImage
import RHLean.Analysis.AlpogeThin.NativeDyadicReturnBudget
import RHLean.Analysis.AlpogeThin.NativeDyadicShiftedWidthRows
import RHLean.Analysis.AlpogeThin.NativeDyadicUnramifiedPrefix
import RHLean.Analysis.AlpogeThin.NativePrimeTowerCentering
import RHLean.Analysis.AlpogeThin.NativeSignedPrimeExponentAncestor
import RHLean.Geometry.NativePrimeExponentJet
import RHLean.Geometry.NativeThetaPeriodEvaluation
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
    `RHLean.Geometry.NativeTheta.ExponentDigits.factorialDigitUnit_pow_dvd_sub_totalReadout,
    `RHLean.Geometry.NativeTheta.HasseDigits.choose_prod_eq_bounded_hasse_sum,
    `RHLean.Geometry.NativeTheta.HasseDigits.recover_bounded_hasse_digits,
    `RHLean.Geometry.NativeTheta.InvariantPrincipalSymbol.formalColumnJet_principal,
    `RHLean.Geometry.NativeTheta.InvariantLeadingJets.formalColumnJet_zero_of_extra_factor,
    `RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.prescribedLattice_weighted_herm_local,
    `RHLean.Geometry.NativeTheta.adaptedEdge_pairing_same_cutoff,
    `RHLean.Analysis.AlpogeThin.nativeDyadicInertPrime_exists_grid_unit_of_winPair,
    `RHLean.Analysis.AlpogeThin.PrimeExponent.part_mul_complement,
    `RHLean.Analysis.AlpogeThin.PrimeExponent.mass_le_rpow,
    `RHLean.Analysis.AlpogeThin.PrimeExponent.ancestor_clock,
    `RHLean.Geometry.NativePrimeExponentJet.factorization_recovery,
    `RHLean.Geometry.NativePrimeExponentJet.factorization_signed_entry,
    `RHLean.Analysis.nativeHighFirstPrimeCenter_error,
    `RHLean.Analysis.nativeHighFirstPrimeCenter_real_comparison,
    `RHLean.Analysis.nativeProperPowerCenter_square_error,
    `RHLean.Analysis.AlpogeThin.nativeDyadicPageN_unramifiedPrefix_minor,
    `RHLean.Analysis.AlpogeThin.nativeDyadicPageN_small_bases_before_return_full_cutoff,
    `RHLean.Analysis.nativeDyadic_partnerColourImage,
    `RHLean.Analysis.alpogeNativePartner_add_two_no_separation,
    `RHLean.Analysis.AlpogeThin.nativeDyadicLocalSourceAtom_scaled_shift_difference,
    `RHLean.Analysis.AlpogeThin.nativeDyadic_signedAncestor_all_primes,
    `RHLean.Analysis.nativePrimeTower_finite_payment,
    `RHLean.Geometry.NativeTheta.AppellHumbert.period_value_two_minor,
    `RHLean.Geometry.NativeTheta.ExponentDigits.card_digitIndex,
    `RHLean.Geometry.NativeTheta.ExponentDigits.card_digitFiber,
    `RHLean.Geometry.NativeTheta.ExponentDigits.factorial_digit_unit,
    `RHLean.Geometry.NativeFrobeniusHasse.det_ordinary_progression,
    `RHLean.Analysis.nativeDyadic_frobPeriod_rigid,
    `RHLean.Analysis.nativeDyadic_frob_characters_eq_of_nilpotent_ratio,
    `RHLean.Analysis.nativeDyadic_returning_hasse_det_isUnit,
    `RHLean.Geometry.NativeTheta.Paired.isIntegral_coeff_hermitianJet_of_unimodular,
    `RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.prescribedLattice_row_integral_iff,
    `RHLean.Analysis.AlpogeThin.nativeDyadicDPrimeASK_normalized_le_of_winPair,
    `RHLean.Analysis.AlpogeThin.nativeDyadicInertPrime_exponent_lt_of_winPair,
    `RHLean.Analysis.AlpogeThin.nativeDyadicInertPrime_odd_mask_card_le,
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
  let pricedRoots : Array Name := #[
    ``RHLean.Analysis.nativeProperPower_clippedMass_le,
    ``RHLean.Analysis.alpogeNativeFirstPrimeWidthASK_error,
    ``RHLean.Analysis.alpogeNativeFirstPrimeWidth_normalized_error,
    ``RHLean.Analysis.AlpogeThin.nativeLedger_anyCutoff_le_thick_add_thin,
    ``RHLean.Analysis.AlpogeThin.nativeLedger_thickTail_cut,
    ``RHLean.Analysis.AlpogeThin.nativeLedger_roundedWidth_cap_eventually,
    ``RHLean.Analysis.alpogeNativePartner_even_offset_iff,
    ``RHLean.Analysis.AlpogeThin.nativeLedger_firstPrimeWidth_price_le,
    ``RHLean.Analysis.AlpogeThin.nativeLedger_firstPrimeWidth_on_dyadicFrame,
    ``RHLean.Analysis.alpogeNativeFirstPrimeWidthASK_eq_linear_sub_saving,
    ``RHLean.Analysis.alpogeNativeThinFirstPrime_saving_le,
    ``RHLean.Analysis.AlpogeThin.nativeLedger_pairGood_roundedASK_le_thick,
    ``RHLean.Analysis.alpogeNativeTwistedSharp_le_forward,
    ``RHLean.Analysis.AlpogeThin.nativeLedger_pairGood_sharp_twist,
    ``RHLean.Analysis.AlpogeThin.nativeLedger_highPrime_thick_thirdCut_zero,
    ``RHLean.Analysis.AlpogeThin.nativeLedger_restoreMeasuredThick_le,
    ``RHLean.Analysis.AlpogeThin.nativeDyadic_activeShift_residues_in_window,
    ``RHLean.Analysis.AlpogeThin.nativeDyadic_activeShift_joint_injective_heights,
    ``RHLean.Analysis.AlpogeThin.nativeDyadic_normalizedHeightShift_chain_norm,
    ``RHLean.Analysis.AlpogeThin.nativeDyadic_normalizedHeightShift_clearing_minor,
    ``RHLean.Analysis.AlpogeThin.nativeDyadic_normalizedHeightShift_chain_denominator,
    ``RHLean.Analysis.AlpogeThin.nativeDyadic_firstPrime_sameWidth_matching,
    ``RHLean.Analysis.AlpogeThin.nativeDyadic_sameWidth_firstPrime_signed,
    ``RHLean.Analysis.AlpogeThin.nativeDyadic_sameWidth_firstPrime_weighted_gain,
    ``RHLean.Analysis.AlpogeThin.nativeDyadic_firstPrime_paired_unit_price,
    ``RHLean.Analysis.AlpogeThin.nativeDyadic_firstPrime_matching_kernel_det,
    ``RHLean.Analysis.AlpogeThin.nativeDyadic_firstPrime_depth_surjective,
    ``RHLean.Analysis.AlpogeThin.nativeDyadic_matchedRead_joint_index,
    ``RHLean.Analysis.AlpogeThin.nativeDyadic_firstPrime_measured_logIndex_price,
    ``RHLean.Analysis.AlpogeThin.nativeDyadic_firstPrime_factorial_depth,
    ``RHLean.Analysis.AlpogeThin.nativeDyadic_firstPrime_wheel_product,
    ``RHLean.Analysis.AlpogeThin.nativeDyadic_firstPrime_wheel_depth,
    ``RHLean.Analysis.AlpogeThin.nativeDyadic_firstPrime_wheel_block_coprime,
    ``RHLean.Analysis.AlpogeThin.nativeDyadic_firstPrime_wheel_block_dual,
    ``RHLean.Analysis.AlpogeThin.nativeDyadic_firstPrime_wheel_block_gram,
    ``RHLean.Analysis.AlpogeThin.nativeDyadic_firstPrime_wheel_short_completion,
    ``RHLean.Analysis.AlpogeThin.nativeDyadic_firstPrime_wheel_dual_gram,
    ``RHLean.Analysis.AlpogeThin.nativeDyadic_firstPrime_wheel_block_supplied,
    ``RHLean.Analysis.AlpogeThin.RankOne.slots_le,
    ``RHLean.Analysis.AlpogeThin.RankOne.gcd_admission,
    ``RHLean.Analysis.AlpogeThin.RankOne.chartRead_eq,
    ``RHLean.Analysis.AlpogeThin.RankOne.chartDepth_le,
    ``RHLean.Analysis.AlpogeThin.RankOne.exists_chart,
    ``RHLean.Analysis.AlpogeThin.RankOne.jet_read_norm,
    ``RHLean.Analysis.AlpogeThin.RankOne.common_jet,
    ``RHLean.Analysis.AlpogeThin.RankOne.forced_sum_eq_nominal_ask,
    ``RHLean.Analysis.AlpogeThin.RankOne.interval_jet_norm_ge_one,
    ``RHLean.Analysis.AlpogeThin.RankOne.primitive_line_denominator,
    ``RHLean.Analysis.AlpogeThin.RankOne.measured_line_denominator,
    ``RHLean.Analysis.AlpogeThin.RankOne.split_prime_clearing,
    ``RHLean.Analysis.AlpogeThin.RankOne.nominal_ceil_norm_ge_half,
    ``RHLean.Analysis.AlpogeThin.RankOne.nominal_jet,
    ``RHLean.Analysis.AlpogeThin.RankOne.dyadic_nominal_jet,
    ``RHLean.Analysis.AlpogeThin.RankOne.derivative_pair,
    ``RHLean.Analysis.AlpogeThin.RankOne.derivativeProjection_spec,
    ``RHLean.Analysis.AlpogeThin.RankOne.projected_test_pair,
    ``RHLean.Analysis.AlpogeThin.RankOne.rational_derivative_height,
    ``RHLean.Analysis.AlpogeThin.RankOne.dyadic_derivative_height,
    ``RHLean.Analysis.AlpogeThin.RankOne.dyadic_metric_padic,
    ``RHLean.Analysis.AlpogeThin.RankOne.classTest_bounds,
    ``RHLean.Analysis.AlpogeThin.RankOne.exists_classTest_ge,
    ``RHLean.Analysis.AlpogeThin.RankOne.common_jet_twisted_read,
    ``RHLean.Analysis.AlpogeThin.WheelFit.dyadic_all_channels,
    ``RHLean.Analysis.AlpogeThin.WheelFit.zero_depth_le,
    ``RHLean.Analysis.AlpogeThin.WheelFit.nominal_signed_witness,
    ``RHLean.Analysis.AlpogeThin.WheelFit.outside_wheel_price,
    ``RHLean.Analysis.AlpogeThin.WheelFit.wheel_depths,
    ``RHLean.Analysis.AlpogeThin.WheelFit.row_det,
    ``RHLean.Analysis.AlpogeThin.WheelFit.exact_row_price,
    ``RHLean.Analysis.AlpogeThin.WheelFit.joint_budget_iff,
    ``RHLean.Analysis.AlpogeThin.WheelFit.character_coordinates,
    ``RHLean.Analysis.AlpogeThin.WheelFit.lattice_budget_iff,
    ``RHLean.Analysis.AlpogeThin.WheelFit.finite_row_budget,
    ``RHLean.Analysis.AlpogeThin.WheelFit.rowLCM_local,
    ``RHLean.Analysis.AlpogeThin.WheelFit.sharp_joint_place,
    ``RHLean.Analysis.AlpogeThin.WheelFit.sharp_joint_total,
    ``RHLean.Analysis.AlpogeThin.WheelFit.native_fit_budget,
    ``RHLean.Analysis.AlpogeThin.WheelFit.common_native_allowance,
    ``RHLean.Analysis.AlpogeThin.WheelFit.singletonOrders_injective,
    ``RHLean.Analysis.AlpogeThin.WheelFit.common_read,
    ``RHLean.Analysis.AlpogeThin.WheelFit.exact_projector_price,
    ``RHLean.Analysis.AlpogeThin.WidthSweep.log_interval_cost,
    ``RHLean.Analysis.AlpogeThin.WidthSweep.firstPrime_endpoint_phase,
    ``RHLean.Analysis.AlpogeThin.WidthSweep.signed_row_eq,
    ``RHLean.Analysis.AlpogeThin.WidthSweep.two_cutoff_eq,
    ``RHLean.Analysis.AlpogeThin.WidthSweep.frozen_top_excess_eq,
    ``RHLean.Analysis.AlpogeThin.WidthSweep.pairGood_row_le,
    ``RHLean.Analysis.AlpogeThin.WidthSweep.pairGood_frozen_top_le,
    ``RHLean.Analysis.AlpogeThin.WidthSweep.frozen_colour_mass,
    ``RHLean.Analysis.AlpogeThin.WidthSweep.frozen_log_sum,
    ``RHLean.Analysis.AlpogeThin.MeasuredCut.gram_det,
    ``RHLean.Analysis.AlpogeThin.MeasuredCut.admission_bounds,
    ``RHLean.Analysis.AlpogeThin.MeasuredCut.wheel_factor_le,
    ``RHLean.Analysis.AlpogeThin.MeasuredCut.firstPrime_fibre,
    ``RHLean.Analysis.AlpogeThin.nativeLedger_high_wheel_normalized_price,
    ``RHLean.Analysis.AlpogeThin.nativeSquareClock_injectiveHeights_log_eventually,
    ``RHLean.Analysis.AlpogeThin.nativeLedger_thickTail_mass,
    ``RHLean.Analysis.AlpogeThin.nativeLedger_thickFirst_saving_census,
    ``RHLean.Analysis.AlpogeThin.nativeLedger_ramifiedFirst_saving_le,
    ``RHLean.Analysis.AlpogeThin.nativeLedger_winPair_discriminant_growth,
    ``RHLean.Analysis.AlpogeThin.nativeDyadic_sharedWidth_laterReads_le,
    ``RHLean.Analysis.AlpogeThin.nativeLedger_realHeight_mem_pairWindow]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for root in roots ++ pricedRoots do
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
      if pricedRoots.contains root then
        if let some info := env.find? n then
          if info.type.getForallBody.isConstOf `RiemannHypothesis then
            throwError "A native quantitative estimate depends on a terminal RH proof: {root} via {n}"
    logInfo m!"PASS strict principal source dependency gate: {root}; axioms={axs}; dependencies={names.toList.length}"
