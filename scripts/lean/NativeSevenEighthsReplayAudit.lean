import Lean
import Lean.Util.CollectAxioms

/-!
Compile the replay to an olean first, then run under
the same combined native/OAI LEAN_PATH:

lean --run scripts/lean/NativeSevenEighthsReplayAudit.lean \
  research.oai_434.VF919NativeSevenEighthsReplay \
  OAI.SevenEighths.RHLeanNativeSevenEighthsReplay.native_beta_le_seven_eighths

This checks live elaborated proof-value reachability. It deliberately ignores
mere import membership and declaration type references. Administrative beta
and zeta reduction removes unused "have" sidecars in the new replay before
collecting refs; unchanged upstream values are traversed without expansion.
A reachability audit complements, rather than replaces, endpoint type checks
and the terminal axiom whitelist.
-/

open Lean

namespace RHLeanReplayDependencyAudit

def dottedName (s : String) : Name :=
  (s.splitOn ".").foldl (fun n p => Name.str n p) Name.anonymous

def shouldExpand (name : Name) : Bool :=
  (`OAI).isPrefixOf name || (`RHLean).isPrefixOf name || (`_private).isPrefixOf name

partial def administrativeReduce : Expr → Expr
  | .letE _ _ value body _ => administrativeReduce (body.instantiate1 value)
  | .app fn arg =>
    let fn' := administrativeReduce fn
    match fn' with
    | .lam _ _ body _ => administrativeReduce (body.instantiate1 arg)
    | _ => .app fn' (administrativeReduce arg)
  | .lam name type body bi =>
    .lam name (administrativeReduce type) (administrativeReduce body) bi
  | .forallE name type body bi =>
    .forallE name (administrativeReduce type) (administrativeReduce body) bi
  | .mdata _ body => administrativeReduce body
  | .proj structName index body =>
    .proj structName index (administrativeReduce body)
  | other => other

partial def valueClosure (env : Environment) (pending : List Name)
    (seen : NameSet := {}) : NameSet :=
  match pending with
  | [] => seen
  | name :: rest =>
    if seen.contains name then
      valueClosure env rest seen
    else
      let seen' := seen.insert name
      let refs := if shouldExpand name then
        match env.find? name with
        | none => []
        -- Lean's default omits theorem and opaque bodies; those are exactly
        -- the proof values this audit must inspect.
        | some info => match info.value? (allowOpaque := true) with
          | none => []
          | some value =>
            let live := if (`OAI.SevenEighths.RHLeanNativeSevenEighthsReplay).isPrefixOf name
              then administrativeReduce value else value
            live.getUsedConstants.toList
        else []
      valueClosure env (refs ++ rest) seen'

def required : Array Name := #[
  `OAI.SevenEighths.RHLeanNativeSevenEighthsReplay.native_source_moments_all_heights,
  `OAI.SevenEighths.RHLeanNativeSevenEighthsReplay.native_detector_bands_for_fixed_data,
  `OAI.SevenEighths.RHLeanNativeSevenEighthsReplay.native_source_moments,
  `OAI.SevenEighths.RHLeanNativeSevenEighthsReplay.native_fine_moments_of_certified,
  `OAI.SevenEighths.RHLeanNativeSevenEighthsReplay.nns_certified_bands,
  `OAI.SevenEighths.RHLeanNativeSevenEighthsReplay.nns_terminal_certificate,
  `OAI.SevenEighths.CenteredMomentEnergyCappedWidthInduction.certified_floor,
  `OAI.SevenEighths.CenteredMomentEnergyCappedAnalyticSuccessor.actual_successor,
  `OAI.SevenEighths.ProbeDetectorPlainMarkedFineField.source_batch_plain_marked_fine_sharper_signed_NNS
]

def requiredStrict : Array Name := #[
  `OAI.SevenEighths.RHLeanNativeSevenEighthsReplay.native_fixed_tilted_probe_bounds,
  `OAI.SevenEighths.RHLeanNativeSevenEighthsReplay.native_uniform_fixed_source_moments,
  `OAI.SevenEighths.ProbeFinalAssembly.SourceData.fixed_tiltedProbe_low,
  `OAI.SevenEighths.ProbePhysical.original_normalized_compensatedPhysicalProbe_low_tilted,
  `OAI.SevenEighths.InverseReflectedPhase.low_original_completed_energy_tilted,
  `OAI.SevenEighths.ProbeFinalAssembly.fixed_tilted_high_bound,
  `OAI.SevenEighths.ProbeFinalAssembly.actual_high_probe_from_raw_moments_tilted,
  `OAI.SevenEighths.ProbeFinalAssembly.actual_nonfloor_rows_saving_tilted,
  `OAI.SevenEighths.ProbeHighRowFamily.actual_nonfloor_probe_transport_tilted,
  `OAI.SevenEighths.ProbePrincipalNormalized.actual_ray_principal_comparison_tilted,
  `OAI.SevenEighths.HeckeSignal.nonzero_of_probe_bounds_variable_boundary
]

def requiredMertens : Array Name := #[
  `OAI.SevenEighths.RHLeanNativeSevenEighthsReplay.native_beta_lt_seven_eighths,
  `RHLean.Analysis.native_zeta_rightmost_le_hecke_beta,
  `OAI.SevenEighths.HeckeDirichlet.LFunction_eq_dirichlet_product,
  `RHLean.Analysis.MertensExponent.growthExponent_eq_rightmost
]

def forbidden : Array Name := #[
  `OAI.SevenEighths.CenteredMomentEnergyCertifiedExistence.terminal_certificate,
  `OAI.SevenEighths.CenteredMomentEnergyCertifiedExistence.certified_bands,
  `OAI.SevenEighths.ProbeFinalAssemblyCertifiedBands.source_moments,
  `OAI.SevenEighths.ProbeFinalAssemblyCertifiedBands.fine_moments_of_certified,
  `OAI.SevenEighths.ProbeFinalAssemblyCertifiedBands.chosen_moments_of_certified,
  `OAI.SevenEighths.ProbeDetectorPlainMarkedFineField.source_batch_plain_marked_fine
]

def forbiddenPrefixes : Array Name := #[
  `OAI.SevenEighths.ProbeFinalAssemblyUnconditional
]

def checkEndpointType (terminalName : Name) : CoreM Unit := do
  let check : Elab.Term.TermElabM Unit := do
    -- Parse in the loaded environment: quotations created while this script
    -- imports only Lean would attach macro scopes to later-loaded names.
    let expectedSource := if terminalName == `RHLean.Analysis.native_mertens_growth_exponent_lt_seven_eighths
      then "_root_.RHLean.Analysis.MertensExponent.mertensGrowthExponent < (7 / 8 : _root_.Real)"
      else if terminalName ==
        `OAI.SevenEighths.RHLeanNativeSevenEighthsReplay.native_beta_lt_seven_eighths
      then "_root_.OAI.SevenEighths.HeckeZeroSupremum.beta < (7 / 8 : _root_.Real)"
      else "_root_.OAI.SevenEighths.HeckeZeroSupremum.beta ≤ (7 / 8 : _root_.Real)"
    let expectedSyntax ← match Parser.runParserCategory (← getEnv) `term expectedSource with
      | .ok stx => pure stx
      | .error message => throwError "Expected endpoint type did not parse: {message}"
    let expected ← Elab.Term.elabTermAndSynthesize expectedSyntax (some (mkSort .zero))
    let info ← getConstInfo terminalName
    unless ← Meta.isDefEq info.type expected do
      throwError "Unexpected terminal type: {info.type}"
  (check.run' { errToSorry := false }).run'

end RHLeanReplayDependencyAudit

open RHLeanReplayDependencyAudit in
def main (args : List String) : IO UInt32 := do
  let moduleArg := args.head?.getD "research.oai_434.VF919NativeSevenEighthsReplay"
  let terminalArg := (args.drop 1).head?.getD
    "OAI.SevenEighths.RHLeanNativeSevenEighthsReplay.native_beta_le_seven_eighths"
  -- Existing research imports use one escaped atomic name with embedded dots.
  let moduleName := Name.mkSimple moduleArg
  let terminalName := dottedName terminalArg
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let env ← importModules #[{ module := moduleName }] Options.empty 1024 (loadExts := true)
  if (env.find? terminalName).isNone then
    throw (IO.userError s!"Missing terminal declaration {terminalName}")
  (checkEndpointType terminalName).toIO'
    { fileName := "<endpoint-audit>", fileMap := default } { env := env }
  IO.println s!"Exact unconditional terminal type checked: {terminalName}"
  let axioms ← (Lean.collectAxioms terminalName : CoreM (Array Name)).toIO'
    { fileName := "<axiom-audit>", fileMap := default } { env := env }
  let allowedAxioms : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in axioms do
    if !allowedAxioms.contains name then
      throw (IO.userError s!"Nonstandard terminal axiom: {name}")
  IO.println s!"Standard terminal axioms: {axioms}"
  let reached := valueClosure env [terminalName]
  IO.println s!"Traversed {reached.size} live value dependencies from {terminalName}"
  let requiredHere := if terminalName == `RHLean.Analysis.native_mertens_growth_exponent_lt_seven_eighths
    then required ++ requiredStrict ++ requiredMertens
    else if terminalName ==
      `OAI.SevenEighths.RHLeanNativeSevenEighthsReplay.native_beta_lt_seven_eighths
    then required ++ requiredStrict else required
  for name in requiredHere do
    if !reached.contains name then
      throw (IO.userError s!"Required live proof dependency missing: {name}")
    IO.println s!"Required live proof dependency: {name}"
  for name in forbidden do
    if reached.contains name then
      throw (IO.userError s!"Forbidden original terminal shortcut: {name}")
  -- Use the imported environment's constant names rather than relying on
  -- a particular NameSet iterator API.
  for moduleData in env.header.moduleData do
    for name in moduleData.constNames do
      if reached.contains name && forbiddenPrefixes.any (fun p => p.isPrefixOf name) then
        throw (IO.userError s!"Forbidden original terminal namespace: {name}")
  IO.println s!"PASS: {terminalName}; {reached.size} live value dependencies"
  return 0


