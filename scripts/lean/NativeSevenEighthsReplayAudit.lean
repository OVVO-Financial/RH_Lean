import Lean

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
  `OAI.SevenEighths.RHLeanNativeSevenEighthsReplay.native_source_moments,
  `OAI.SevenEighths.RHLeanNativeSevenEighthsReplay.native_fine_moments_of_certified,
  `OAI.SevenEighths.RHLeanNativeSevenEighthsReplay.nns_certified_bands,
  `OAI.SevenEighths.RHLeanNativeSevenEighthsReplay.nns_terminal_certificate,
  `OAI.SevenEighths.CenteredMomentEnergyCappedWidthInduction.certified_floor,
  `OAI.SevenEighths.CenteredMomentEnergyCappedAnalyticSuccessor.actual_successor,
  `OAI.SevenEighths.ProbeDetectorPlainMarkedFineField.source_batch_plain_marked_fine_sharper_signed_NNS
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
  let env ← importModules #[{ module := moduleName }] Options.empty 1024
  if (env.find? terminalName).isNone then
    throw (IO.userError s!"Missing terminal declaration {terminalName}")
  let reached := valueClosure env [terminalName]
  IO.println s!"Traversed {reached.size} live value dependencies from {terminalName}"
  for name in required do
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

