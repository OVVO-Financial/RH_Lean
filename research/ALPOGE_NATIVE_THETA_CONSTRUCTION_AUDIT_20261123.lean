import RHLean.Geometry.NativeThetaChartAgreement
import RHLean.Geometry.NativeThetaFaithfullyFlatDescent
import RHLean.Geometry.NativeThetaFiniteFlatCover
import RHLean.Geometry.NativeThetaOrbitTorsion
import RHLean.Geometry.NativeThetaOrbitLattice
import RHLean.Geometry.NativeThetaSectionRealization
import RHLean.Geometry.NativeThetaPeriodTorsion
import RHLean.Geometry.NativeThetaTriangularFrame
import RHLean.Analysis.AlpogeThin.NativeDyadicHostPrimePowerWeights
import RHLean.Analysis.AlpogeThin.NativeDyadicFixedAuxiliaryLevel
import RHLean.Geometry.NativeThetaPeriodFreeness
import RHLean.Geometry.NativeThetaPeriodIndexFreeness
import RHLean.Geometry.NativeThetaSectionWeight
import RHLean.Geometry.NativeThetaLocalChartAgreement
import RHLean.Geometry.NativeServedPrimeLength
import Lean.Util.CollectAxioms

/-!
# Native theta construction suppliers: exact types and terminal axioms

These declarations reconstruct concrete supplying proofs. They do not assert
that the polarized moduli object, its section-separation theorem, or the
complete signed arithmetic gain has already been constructed.

The audit fails on any terminal axiom outside the three permitted standard
axioms. The actual source declarations, normalizer and scheme morphism remain
visible in the checked theorem types.
-/

#check RHLean.Geometry.NativeTheta.JetEvaluation.map_rawShortValue_eq_of_permuted_odd_phases
#check RHLean.Geometry.NativeTheta.Descent.existsUnique_preimage_of_faithfullyFlat
#check RHLean.Geometry.NativeTheta.FiniteFlatCover.exists_fintype_lifts
#check RHLean.Geometry.NativeThetaOrbitTorsion.finite_order_unipotent_eq_id
#check RHLean.Geometry.NativeTheta.SectionRealization.rule_isNatural
#check RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.twistedLattice_integer_level_card
#check RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.prescribedPeriodTorsion_card
#check RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.prescribedPeriod_primary_fixed
#check RHLean.Geometry.NativeTheta.RowTriangular.eval₂_triangular_of_mem_HHa
#check RHLean.Analysis.AlpogeThin.nativeDyadicHost_fullASK_eq_oddClassSums_add_dCorrection
#check RHLean.Analysis.AlpogeThin.nativeDyadicHost_De_eq_oddClassSums_add_dCorrection_sub_MAIN
#check RHLean.Analysis.AlpogeThin.nativeDyadicDPrimeASK_normalized_le
#check RHLean.Geometry.NativeThetaOrbitTorsion.finite_order_unipotent_eq_id_of_index
#check RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.prescribedPeriod_finite_order_congruent_five_eq_id
#check RHLean.Analysis.AlpogeThin.nativeDyadicFixedLevelFive_inertia
#check RHLean.Geometry.NativeTheta.FormalCalculus.dof_comm_law
#check RHLean.Geometry.NativeTheta.JetFrame.shortValueOfFormalGerms_triangular
#check RHLean.Geometry.NativeTheta.SectionRealization.value_triangular
#check RHLean.Geometry.NativeTheta.SectionRealization.existsUnique_value_of_local_phases
#check RHLean.Geometry.NativeTheta.SectionRealization.valueOfLocalPhases_triangular
#check RHLean.Geometry.NativeServedPrimeLength.lengthFromAllBut_saturated

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let roots : Array Name := #[
    ``RHLean.Geometry.NativeTheta.ChartAgreement.exists_enumeration_translate_equiv,
    ``RHLean.Geometry.NativeTheta.ChartAgreement.phase_product_eq_one_of_pairing,
    ``RHLean.Geometry.NativeTheta.JetEvaluation.map_rawShortValue,
    ``RHLean.Geometry.NativeTheta.JetEvaluation.map_rawShortValue_eq_of_permuted_odd_phases,
    ``RHLean.Geometry.NativeTheta.Descent.faithfullyFlat_of_geometric_points,
    ``RHLean.Geometry.NativeTheta.Descent.exists_faithfullyFlat_pushout,
    ``RHLean.Geometry.NativeTheta.Descent.existsUnique_preimage_of_faithfullyFlat,
    ``RHLean.Geometry.NativeTheta.FiniteFlatCover.exists_lift,
    ``RHLean.Geometry.NativeTheta.FiniteFlatCover.exists_fintype_lifts,
    ``RHLean.Geometry.NativeThetaOrbitTorsion.FiniteOrderUnipotent.nil_index,
    ``RHLean.Geometry.NativeThetaOrbitTorsion.finite_order_unipotent_eq_id,
    ``RHLean.Geometry.NativeThetaOrbitTorsion.natCard_quot_maximal_smul_top_eq,
    ``RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.twistedLattice_residue_card,
    ``RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.twistedLattice_integer_level_card,
    ``RHLean.Geometry.NativeTheta.SectionRealization.existsUnique_value,
    ``RHLean.Geometry.NativeTheta.SectionRealization.valueLinear,
    ``RHLean.Geometry.NativeTheta.SectionRealization.map_eq_of_chart_values,
    ``RHLean.Geometry.NativeTheta.SectionRealization.rule_isNatural,
    ``RHLean.Geometry.NativeTheta.SectionRealization.ruleLinear,
    ``RHLean.Geometry.NativeThetaPeriodTorsion.latticeQuotientEquivTorsion,
    ``RHLean.Geometry.NativeThetaPeriodTorsion.primary_divisible,
    ``RHLean.Geometry.NativeThetaPeriodTorsion.finite_order_unipotent_primary_eq_id,
    ``RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.prescribedPeriodMap_injective,
    ``RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.prescribedPeriodTorsion_card,
    ``RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.prescribedPeriod_primary_fixed,
    ``RHLean.Geometry.NativeTheta.RowTriangular.eval₂_triangular_of_mem_HHa,
    ``RHLean.Analysis.AlpogeThin.nativeDyadicHostPrimePowerWeight_unramified,
    ``RHLean.Analysis.AlpogeThin.nativeDyadicHostPrimePowerWeight_typeI,
    ``RHLean.Analysis.AlpogeThin.nativeDyadicHostPrimePowerWeight_d,
    ``RHLean.Analysis.AlpogeThin.nativeDyadicHost_fullASK_eq_oddClassSums_add_dCorrection,
    ``RHLean.Analysis.AlpogeThin.nativeDyadicHost_De_eq_oddClassSums_add_dCorrection_sub_MAIN,
    ``RHLean.Analysis.AlpogeThin.nativeDyadicDPrimeASK_norm_le,
    ``RHLean.Analysis.AlpogeThin.nativeDyadicDPrimeASK_normalized_le,
    ``RHLean.Geometry.NativeThetaOrbitTorsion.finite_order_unipotent_eq_id_of_index,
    ``RHLean.Geometry.NativeThetaPeriodTorsion.eq_zero_of_mem_all_power_ranges,
    ``RHLean.Geometry.NativeThetaPeriodTorsion.latticeAction_eq_id_of_primary_fixed,
    ``RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.prescribedPeriodMap_span,
    ``RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.prescribedPeriod_finite_order_unipotent_eq_id,
    ``RHLean.Geometry.NativeThetaPeriodTorsion.finite_order_unipotent_primary_eq_id_of_index,
    ``RHLean.Geometry.NativeThetaPeriodTorsion.finite_order_congruent_periodAction_eq_id,
    ``RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.prescribedPeriod_finite_order_unipotent_eq_id_of_index,
    ``RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.prescribedPeriod_finite_order_congruent_five_eq_id,
    ``RHLean.Analysis.AlpogeThin.nativeDyadicFixedLevelFive_not_dvd_conductor,
    ``RHLean.Analysis.AlpogeThin.nativeDyadicFixedLevelFive_coprime_conductor,
    ``RHLean.Analysis.AlpogeThin.nativeDyadicFixedLevelFive_inertia,
    ``RHLean.Geometry.NativeTheta.FormalCalculus.pderiv_subst,
    ``RHLean.Geometry.NativeTheta.FormalCalculus.jac_F,
    ``RHLean.Geometry.NativeTheta.FormalCalculus.dof_comm_law,
    ``RHLean.Geometry.NativeTheta.JetFrame.columnJet_triangular,
    ``RHLean.Geometry.NativeTheta.JetFrame.shortValueOfFormalGerms_triangular,
    ``RHLean.Geometry.NativeTheta.SectionRealization.value_triangular,
    ``RHLean.Geometry.NativeTheta.SectionRealization.eq_of_maximal_localizations,
    ``RHLean.Geometry.NativeTheta.SectionRealization.LocalPhaseTransport.value_eq,
    ``RHLean.Geometry.NativeTheta.SectionRealization.existsUnique_value_of_local_phases,
    ``RHLean.Geometry.NativeTheta.SectionRealization.map_eq_of_local_chart_values,
    ``RHLean.Geometry.NativeTheta.SectionRealization.valueOfLocalPhases_triangular,
    ``RHLean.Geometry.NativeServedPrimeLength.allButLE_zero_iff,
    ``RHLean.Geometry.NativeServedPrimeLength.CyclicSpanLengthLemmas.lengthPart2,
    ``RHLean.Geometry.NativeServedPrimeLength.ln_length_pow,
    ``RHLean.Geometry.NativeServedPrimeLength.length_quot_span_eq_addVal,
    ``RHLean.Geometry.NativeServedPrimeLength.lengthFromAllBut,
    ``RHLean.Geometry.NativeServedPrimeLength.lengthFromAllBut_saturated]
  let env ← getEnv
  for root in roots do
    unless env.contains root do
      throwError "Missing native declaration: {root}"
    let axioms ← liftCoreM (Lean.collectAxioms root)
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unapproved terminal axiom for {root}: {ax}"
    logInfo m!"PASS native theta supplier {root}: {axioms}"
