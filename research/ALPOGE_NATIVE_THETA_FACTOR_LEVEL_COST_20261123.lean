import RHLean.Geometry.NativeThetaAppellHumbert
import RHLean.Geometry.NativeThetaFullLevelCost
import Lean.Util.CollectAxioms

/-!
# Constructed native theta factor and actual full-level marking cost

The first endpoint uses the actual prescribed inverse-half-different lattice,
period map and positive Hermitian form. It constructs the canonical phase,
automorphy cocycle and invariant Gaussian fiber metric. It does not assume
their transformation laws.

The second endpoint counts coefficient-linear markings of that same lattice
modulo the rational integer five. The field degree occurs once. The finite
quotient is identified with the already constructed period torsion.

These are supplying constructions, not a proof of the global cusp spanning,
measured Petersson comparison or complete universal signed-source bound.
-/

#check RHLean.Analysis.AlpogeThin.nativeDyadicPrescribedPeriod_exists_thetaFactor
#check RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.prescribedPeriod_fullLevel_marking_exists
#check RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.prescribedLattice_fullLevelFive_log_le
#check RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.twistedLattice_fourthLevelGroup_card_le

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let roots : Array Name := #[
    ``RHLean.Geometry.NativeTheta.AppellHumbert.weight_add_bar,
    ``RHLean.Geometry.NativeTheta.AppellHumbert.form_skew,
    ``RHLean.Geometry.NativeTheta.AppellHumbert.quadraticRefinement_add,
    ``RHLean.Geometry.NativeTheta.AppellHumbert.phase_eq_one_or_neg_one,
    ``RHLean.Geometry.NativeTheta.AppellHumbert.norm_phase,
    ``RHLean.Geometry.NativeTheta.AppellHumbert.phase_ne_zero,
    ``RHLean.Geometry.NativeTheta.AppellHumbert.phase_sq,
    ``RHLean.Geometry.NativeTheta.AppellHumbert.intSign_eq_exp,
    ``RHLean.Geometry.NativeTheta.AppellHumbert.phase_add,
    ``RHLean.Geometry.NativeTheta.AppellHumbert.phase_two_smul,
    ``RHLean.Geometry.NativeTheta.AppellHumbert.hermForm_swap,
    ``RHLean.Geometry.NativeTheta.AppellHumbert.factor_ne_zero,
    ``RHLean.Geometry.NativeTheta.AppellHumbert.factor_add,
    ``RHLean.Geometry.NativeTheta.AppellHumbert.norm_factor,
    ``RHLean.Geometry.NativeTheta.AppellHumbert.fiberNormSq_translate,
    ``RHLean.Analysis.AlpogeThin.nativeDyadicPrescribedPeriod_exists_thetaFactor,
    ``RHLean.Geometry.NativeThetaFullLevelCost.finrank_fibre,
    ``RHLean.Geometry.NativeThetaFullLevelCost.nonempty_equiv_mod,
    ``RHLean.Geometry.NativeThetaFullLevelCost.nonempty_aut_equiv,
    ``RHLean.Geometry.NativeThetaFullLevelCost.finite_quotient_aut,
    ``RHLean.Geometry.NativeThetaFullLevelCost.natCard_quotient_aut_le,
    ``RHLean.Geometry.NativeThetaFullLevelCost.rationalLevel_toAddSubgroup,
    ``RHLean.Geometry.NativeThetaFullLevelCost.levelQuotientEquivTorsion,
    ``RHLean.Geometry.NativeThetaFullLevelCost.natCard_integer_quotient,
    ``RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.twistedLattice_fullLevelGroup_finite,
    ``RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.twistedLattice_fullLevelGroup_card_le,
    ``RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.twistedLattice_fullLevelGroup_log_le,
    ``RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.prescribedLattice_fullLevelFive_log_le,
    ``RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.twistedLattice_fourthLevelGroup_card_le,
    ``RHLean.Analysis.AlpogeThin.NativeRawHostPolarization.prescribedPeriod_fullLevel_marking_exists]
  let env ← getEnv
  for root in roots do
    unless env.contains root do
      throwError "Missing constructed native declaration: {root}"
    let axioms ← liftCoreM (Lean.collectAxioms root)
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unapproved terminal axiom for {root}: {ax}"
    logInfo m!"PASS native theta factor / level cost {root}: {axioms}"
