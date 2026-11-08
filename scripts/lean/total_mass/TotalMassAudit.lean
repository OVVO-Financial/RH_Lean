import Lean
import Lean.Util.CollectAxioms

/-!
Read-only terminal audit for the total-slot-mass LOW return.

The compiled endpoint must retain the new nominal energy, its original
normalization, the moving tuple mass, all complete LOW consumers, the actual
native moments, anchored HIGH, and the original signal comparison in its live
proof-value closure.  Importing an old strict-gap endpoint is not sufficient.
The public quantified types are checked separately by the expected-type audit.
This program does not generate or certify any proof.
-/

open Lean

namespace TotalMassAudit

def shouldExpand (n : Name) : Bool :=
  (`OAI).isPrefixOf n || (`RHLean).isPrefixOf n || (`_private).isPrefixOf n

partial def reduceAdmin : Expr → Expr
  | .letE _ _ value body _ => reduceAdmin (body.instantiate1 value)
  | .app fn arg =>
    let f := reduceAdmin fn
    match f with
    | .lam _ _ body _ => reduceAdmin (body.instantiate1 arg)
    | _ => .app f (reduceAdmin arg)
  | .lam n t b bi => .lam n (reduceAdmin t) (reduceAdmin b) bi
  | .forallE n t b bi => .forallE n (reduceAdmin t) (reduceAdmin b) bi
  | .mdata _ b => reduceAdmin b
  | .proj n i b => .proj n i (reduceAdmin b)
  | other => other

def reduceBeforeCollecting (n : Name) : Bool :=
  (`OAI.SevenEighths.RHLeanNativeSevenEighthsReplay).isPrefixOf n ||
    (`OAI.SevenEighths.RHLeanActualSlotMin).isPrefixOf n ||
    n.toString.endsWith "_total_mass"

partial def closure (env : Environment) (pending : List Name)
    (seen : NameSet := {}) : NameSet :=
  match pending with
  | [] => seen
  | n :: rest =>
    if seen.contains n then closure env rest seen
    else
      let seen' := seen.insert n
      let refs := if shouldExpand n then
        match env.find? n with
        | none => []
        | some info => match info.value? (allowOpaque := true) with
          | none => []
          | some value =>
            let live := if reduceBeforeCollecting n then reduceAdmin value else value
            live.getUsedConstants.toList
        else []
      closure env (refs ++ rest) seen'

def rootHecke : Name :=
  `OAI.SevenEighths.RHLeanActualSlotMin.native_beta_le_true_physical_slot_minimum_total_mass

def rootMertens : Name :=
  `RHLean.Analysis.native_mertens_true_physical_slot_minimum_total_mass

def rootFixed : Name :=
  `RHLean.Analysis.native_mertens_fixed_true_physical_slot_minimum_total_mass

def rootPairs : Name :=
  `RHLean.Analysis.native_signed_pair_true_physical_slot_minimum_total_mass

/-- Exact declared consumers that must occur in the new Hecke proof value. -/
def needed : Array Name := #[
  `OAI.SevenEighths.RHLeanActualSlotMin.sourceWithExactSlotMinimum,
  `OAI.SevenEighths.RHLeanActualSlotMin.recalibrated_sigma_eq_true_minimum_quarter,
  `OAI.SevenEighths.RHLeanFullPhysicalTilt.slotCalibratedHighDataLowFirst,
  `OAI.SevenEighths.RHLeanFullPhysicalTilt.slotCalibratedHighDataLowFirst_reserves,
  `OAI.SevenEighths.RHLeanNativeSevenEighthsReplay.native_beta_le_total_mass_boundary,
  `OAI.SevenEighths.RHLeanNativeSevenEighthsReplay.native_fixed_total_mass_probe_bounds,
  `OAI.SevenEighths.ProbeFinalAssembly.SourceData.tiltedProbe_low_total_mass,
  `OAI.SevenEighths.ProbePhysical.low_selected_nominal_energy_total_mass,
  `OAI.SevenEighths.ProbePhysical.low_selected_physical_energy_tilted,
  `OAI.SevenEighths.InverseReflectedPhase.low_original_completed_energy_tilted,
  `OAI.SevenEighths.ProbePhysical.low_physical_inverse_normalized_total_mass,
  `OAI.SevenEighths.ProbePhysical.low_inverse_sqrt_normalized_tilted,
  `OAI.SevenEighths.ProbePhysical.low_central_compensated_tuple_total_mass,
  `OAI.SevenEighths.ProbePhysical.lowUnselectedMass_moving_power_bound,
  `OAI.SevenEighths.ProbePhysical.lowUnselectedWeight_norm_identity,
  `OAI.SevenEighths.ProbePhysical.low_central_gaussian_dyad_total_mass,
  `OAI.SevenEighths.ProbePhysical.low_central_gaussian_dyads_total_mass,
  `OAI.SevenEighths.ProbePhysical.low_all_gaussian_dyads_total_mass,
  `OAI.SevenEighths.ProbePhysical.low_remote_gaussian_dyads_tilted,
  `OAI.SevenEighths.ProbePhysical.compensatedPhysicalProbe_low_total_mass,
  `OAI.SevenEighths.ProbePhysical.original_ray_compensatedPhysicalProbe_low_total_mass,
  `OAI.SevenEighths.ProbePhysical.original_ray_compensatedPhysicalProbe_low_loss_total_mass,
  `OAI.SevenEighths.ProbePhysical.original_normalized_compensatedPhysicalProbe_low_total_mass,
  `OAI.SevenEighths.ProbeHighRowFamily.actual_ray_normalizer_inverse,
  `OAI.SevenEighths.RHLeanNativeSevenEighthsReplay.native_beta_le_seven_eighths,
  `OAI.SevenEighths.RHLeanNativeSevenEighthsReplay.native_uniform_fixed_source_moments,
  `OAI.SevenEighths.RHLeanNativeSevenEighthsReplay.native_source_moments_all_heights,
  `OAI.SevenEighths.RHLeanNativeSevenEighthsReplay.nns_terminal_certificate,
  `OAI.SevenEighths.ProbeFinalAssembly.fixed_tilted_high_bound_anchored,
  `OAI.SevenEighths.ProbeFinalAssembly.actual_high_probe_from_raw_moments_tilted_anchored,
  `OAI.SevenEighths.ProbeHighRowFamily.small_physical_dyads_sum_anchored,
  `OAI.SevenEighths.ProbeHighRowFamily.actual_nonfloor_probe_transport_tilted_anchored,
  `OAI.SevenEighths.ProbePrincipalNormalized.actual_ray_principal_comparison_tilted_anchored,
  `OAI.SevenEighths.ProbePrincipalRemainderBounds.source_remainders_strict_saving_tilted_anchored,
  `OAI.SevenEighths.HeckeSignal.nonzero_of_probe_bounds_variable_boundary
]

/-- Only the previously proved non-strict 7/8 bound is the paid upper baseline. -/
def forbidden : Array Name := #[
  `OAI.SevenEighths.RHLeanNativeSevenEighthsReplay.native_beta_lt_seven_eighths,
  `OAI.SevenEighths.RHLeanNativeSevenEighthsReplay.native_uniform_positive_gap,
  `OAI.SevenEighths.RHLeanNativeSevenEighthsReplay.native_beta_le_slot_calibrated_boundary_low_first,
  `OAI.SevenEighths.RHLeanNativeSevenEighthsReplay.native_beta_le_constructed_slot_tilt_low_first,
  `OAI.SevenEighths.RHLeanActualSlotMin.native_beta_le_true_physical_slot_minimum,
  `RHLean.Analysis.native_mertens_growth_exponent_lt_seven_eighths,
  `RHLean.Analysis.native_mertens_uniform_strict_gap
]

def nativeNeeded : Array Name := #[
  `RHLean.Analysis.native_mertens_growth_at_hecke_beta,
  `RHLean.Analysis.native_zeta_rightmost_le_hecke_beta,
  `RHLean.Analysis.native_zeta_zero_re_le_hecke_beta,
  `OAI.SevenEighths.HeckeDirichlet.LFunction_eq_dirichlet_product
]

end TotalMassAudit

open TotalMassAudit in
def main (_args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let env ← importModules
    #[{ module := Name.mkSimple "research.oai_434.VF919TotalMassEndpoint" }]
    Options.empty 1024 (loadExts := true)
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for root in #[rootHecke, rootMertens, rootFixed, rootPairs] do
    let axioms ← (Lean.collectAxioms root : CoreM (Array Name)).toIO'
      { fileName := "<total-mass-axioms>", fileMap := default } { env := env }
    for ax in axioms do
      unless allowed.contains ax do
        throw (IO.userError s!"Unapproved axiom for {root}: {ax}")
    let reached := closure env [root]
    if root == rootHecke then
      for required in needed do
        unless reached.contains required do
          throw (IO.userError s!"Missing live total-mass analytic dependency: {required}")
    else
      unless reached.contains rootHecke do
        throw (IO.userError s!"Native terminal omitted the new Hecke endpoint: {root}")
      for required in nativeNeeded do
        unless reached.contains required do
          throw (IO.userError s!"Missing live native transfer for {root}: {required}")
    if root == rootPairs then
      unless reached.contains `RHLean.Analysis.vf919_mertens_sq_eq_signedPair do
        throw (IO.userError "Signed terminal omitted the exact squarefree-diagonal identity")
    for blocked in forbidden do
      if reached.contains blocked then
        throw (IO.userError s!"Old strict-gap shortcut used by {root}: {blocked}")
    IO.println s!"PASS total-mass endpoint {root}: {axioms}, closure={reached.size}"
  return 0
