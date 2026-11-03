import Lean
import Lean.Util.CollectAxioms

/-! Read-only audit of the true physical-slot minimum proof.  The actual
zero-detector, LOW/HIGH and native NNS moment values must remain live. -/
open Lean

namespace ActualSlotMinAudit

def shouldExpand (n : Name) : Bool :=
  (`OAI).isPrefixOf n || (`RHLean).isPrefixOf n ||
    (`_private).isPrefixOf n

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
            let live := if
              (`OAI.SevenEighths.RHLeanNativeSevenEighthsReplay).isPrefixOf n
              then reduceAdmin value else value
            live.getUsedConstants.toList
        else []
      closure env (refs ++ rest) seen'

def rootHecke : Name :=
  `OAI.SevenEighths.RHLeanActualSlotMin.native_beta_le_true_physical_slot_minimum

def rootMertens : Name :=
  `RHLean.Analysis.native_mertens_true_physical_slot_minimum

def rootPairs : Name :=
  `RHLean.Analysis.native_signed_pair_true_physical_slot_minimum

def needed : Array Name := #[
  `OAI.SevenEighths.RHLeanActualSlotMin.sourceWithExactSlotMinimum,
  `OAI.SevenEighths.RHLeanActualSlotMin.recalibrated_tilt_eq_true_minimum,
  `OAI.SevenEighths.RHLeanNativeSevenEighthsReplay.native_beta_le_slot_calibrated_boundary_low_first,
  `OAI.SevenEighths.RHLeanFullPhysicalTilt.slotCalibratedHighDataLowFirst,
  `OAI.SevenEighths.RHLeanFullPhysicalTilt.slotCalibratedHighDataLowFirst_reserves,
  `OAI.SevenEighths.RHLeanNativeSevenEighthsReplay.native_uniform_fixed_source_moments,
  `OAI.SevenEighths.RHLeanFullPhysicalTilt.low_at_slot_tilt_low_first,
  `OAI.SevenEighths.ProbeFinalAssembly.fixed_tilted_high_bound_anchored,
  `OAI.SevenEighths.HeckeSignal.nonzero_of_probe_bounds_variable_boundary
]

def forbidden : Array Name := #[
  `OAI.SevenEighths.RHLeanNativeSevenEighthsReplay.native_beta_lt_seven_eighths,
  `OAI.SevenEighths.RHLeanNativeSevenEighthsReplay.native_uniform_positive_gap,
  `RHLean.Analysis.native_mertens_growth_exponent_lt_seven_eighths
]

end ActualSlotMinAudit

open ActualSlotMinAudit in
def main (_args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let env ← importModules
    #[{ module := Name.mkSimple "research.oai_434.VF919ActualSlotMinRetighten" }]
    Options.empty 1024 (loadExts := true)
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for root in #[rootHecke, rootMertens, rootPairs] do
    let axioms ← (Lean.collectAxioms root : CoreM (Array Name)).toIO'
      { fileName := "<actual-min-axioms>", fileMap := default } { env := env }
    for ax in axioms do
      unless allowed.contains ax do
        throw (IO.userError s!"Unapproved axiom for {root}: {ax}")
    let reached := closure env [root]
    for required in needed do
      if root == rootHecke then
        unless reached.contains required do
          throw (IO.userError s!"Missing live signed analytic dependency: {required}")
    for blocked in forbidden do
      if reached.contains blocked then
        throw (IO.userError s!"Terminal strict-gap shortcut used: {blocked}")
    IO.println s!"PASS actual-source minimum {root}: {axioms}, closure={reached.size}"
  return 0
