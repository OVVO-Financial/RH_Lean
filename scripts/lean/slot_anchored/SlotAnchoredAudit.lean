import Lean
import Lean.Util.CollectAxioms

/-! Runtime audit of the LOW-first endpoint. Requires compiled proof modules.
This auditing program is neither an axiom nor a proof-generating oracle. -/
open Lean
namespace SlotAnchoredAudit

def dottedName (s : String) : Name :=
  (s.splitOn ".").foldl (fun n p => Name.str n p) Name.anonymous

def shouldExpand (n : Name) : Bool :=
  (`OAI).isPrefixOf n || (`RHLean).isPrefixOf n || (`_private).isPrefixOf n

partial def reduceAdmin : Expr -> Expr
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
            let live := if (`OAI.SevenEighths.RHLeanNativeSevenEighthsReplay).isPrefixOf n
              then reduceAdmin value else value
            live.getUsedConstants.toList
        else []
      closure env (refs ++ rest) seen'

def required : Array Name := #[
 `OAI.SevenEighths.RHLeanNativeSevenEighthsReplay.native_beta_le_slot_calibrated_boundary_low_first,
 `OAI.SevenEighths.RHLeanNativeSevenEighthsReplay.native_fixed_slot_anchored_probe_bounds_low_first,
 `OAI.SevenEighths.RHLeanNativeSevenEighthsReplay.native_uniform_fixed_source_moments,
 `OAI.SevenEighths.RHLeanNativeSevenEighthsReplay.native_source_moments_all_heights,
 `OAI.SevenEighths.RHLeanNativeSevenEighthsReplay.nns_terminal_certificate,
 `OAI.SevenEighths.RHLeanFullPhysicalTilt.exists_slot_calibrated_data_low_first,
 `OAI.SevenEighths.RHLeanFullPhysicalTilt.low_at_slot_tilt_low_first,
 `OAI.SevenEighths.InverseReflectedPhase.low_original_completed_energy_tilted,
 `OAI.SevenEighths.ProbeFinalAssembly.fixed_tilted_high_bound_anchored,
 `OAI.SevenEighths.ProbeFinalAssembly.actual_high_probe_from_raw_moments_tilted_anchored,
 `OAI.SevenEighths.ProbeHighRowFamily.small_physical_dyads_sum_anchored,
 `OAI.SevenEighths.ProbeHighRowFamily.actual_nonfloor_probe_transport_tilted_anchored,
 `OAI.SevenEighths.ProbePrincipalNormalized.actual_ray_principal_comparison_tilted_anchored,
 `OAI.SevenEighths.ProbePrincipalRemainderBounds.source_remainders_strict_saving_tilted_anchored,
 `OAI.SevenEighths.HeckeSignal.nonzero_of_probe_bounds_variable_boundary
]

def forbidden : Array Name := #[
 `OAI.SevenEighths.RHLeanNativeSevenEighthsReplay.native_beta_lt_seven_eighths,
 `OAI.SevenEighths.RHLeanNativeSevenEighthsReplay.native_uniform_positive_gap,
 `RHLean.Analysis.native_mertens_growth_exponent_lt_seven_eighths,
 `RHLean.Analysis.native_mertens_uniform_strict_gap
]

def expectedType (mertens : Bool) : String :=
  let head := "Exists (fun D : _root_.OAI.SevenEighths.Parameters.HighData ((1 : _root_.Real)/1000000) => And (0 < ((((7 : _root_.Real)/8)*D.rmin)/24)) "
  if mertens then
    head ++ "(_root_.RHLean.Analysis.MertensExponent.MertensGrowthAtMost ((7 : _root_.Real)/8-((((7 : _root_.Real)/8)*D.rmin)/24))))"
  else
    head ++ "(LE.le _root_.OAI.SevenEighths.HeckeZeroSupremum.beta ((7 : _root_.Real)/8-((((7 : _root_.Real)/8)*D.rmin)/24))))"

def checkType (n : Name) (mertens : Bool) : CoreM Unit := do
  let check : Elab.Term.TermElabM Unit := do
    let stx <- match Parser.runParserCategory (<- getEnv) `term (expectedType mertens) with
      | .ok stx => pure stx
      | .error msg => throwError "Expected type did not parse: {msg}"
    let expected <- Elab.Term.elabTermAndSynthesize stx (some (mkSort .zero))
    let info <- getConstInfo n
    unless <- Meta.isDefEq info.type expected do
      throwError "Wrong endpoint type: {info.type}"
  (check.run' { errToSorry := false }).run'
end SlotAnchoredAudit

open SlotAnchoredAudit in
def main (args : List String) : IO UInt32 := do
  let mertens := args.head?.getD "hecke" == "mertens"
  let root := if mertens then `RHLean.Analysis.native_mertens_constructed_slot_tilt_low_first
    else `OAI.SevenEighths.RHLeanNativeSevenEighthsReplay.native_beta_le_constructed_slot_tilt_low_first
  initSearchPath (<- findSysroot)
  unsafe enableInitializersExecution
  let env <- importModules #[{ module := Name.mkSimple "research.oai_434.VF919LowFirstSlotAnchoredEndpoint" }]
    Options.empty 1024 (loadExts := true)
  (checkType root mertens).toIO'
    { fileName := "<slot-endpoint-audit>", fileMap := default } { env := env }
  let axioms <- (Lean.collectAxioms root : CoreM (Array Name)).toIO'
    { fileName := "<slot-axiom-audit>", fileMap := default } { env := env }
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for a in axioms do
    unless allowed.contains a do throw (IO.userError s!"Unapproved axiom: {a}")
  let reached := closure env [root]
  for n in required do
    unless reached.contains n do throw (IO.userError s!"Missing live dependency: {n}")
  for n in forbidden do
    if reached.contains n then throw (IO.userError s!"Old strict-gap shortcut used: {n}")
  IO.println s!"PASS exact quantified type and standard axioms: {root}"
  IO.println s!"Axioms: {axioms}; live value dependencies: {reached.size}"
  return 0
