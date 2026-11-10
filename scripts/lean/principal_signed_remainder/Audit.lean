import Lean
import Lean.Util.CollectAxioms

open Lean

namespace PrincipalSignedAudit

partial def closure (env : Environment) (pending : List Name)
    (seen : NameSet := {}) : NameSet :=
  match pending with
  | [] => seen
  | n :: rest =>
    if seen.contains n then closure env rest seen
    else
      let refs := if (`OAI).isPrefixOf n || (`_private).isPrefixOf n then
        match env.find? n with
        | none => []
        | some info => match info.value? (allowOpaque := true) with
          | none => []
          | some value => value.getUsedConstants.toList
        else []
      closure env (refs ++ rest) (seen.insert n)

def root : Name := `OAI.SevenEighths.PrincipalSlotEstimate.principal_slot_signed_error

def roots : Array Name := #[
  root,
  `OAI.SevenEighths.PrincipalSlotEstimate.actual_principal_slot_signed_error,
  `OAI.SevenEighths.PrincipalSlotEstimate.weighted_principal_slot_signed_error,
  `OAI.SevenEighths.PrincipalSlotEstimate.weighted_principal_slot_signed_relative_error
]

end PrincipalSignedAudit

open PrincipalSignedAudit in
def main (_args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let env ← importModules
    #[{ module := Name.mkSimple "research.oai_434.VF919PrincipalSignedRemainder" }]
    Options.empty 1024 (loadExts := true)
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for theoremName in roots do
    let axioms ← (Lean.collectAxioms theoremName : CoreM (Array Name)).toIO'
      { fileName := "<principal-signed-axioms>", fileMap := default } { env := env }
    for ax in axioms do
      unless allowed.contains ax do
        throw (IO.userError s!"Unapproved axiom for {theoremName}: {ax}")
    let reached := closure env [theoremName]
    for required in #[root,
        `OAI.SevenEighths.PrincipalSlotEstimate.principal_K_signed,
        `OAI.SevenEighths.PrincipalSlotEstimate.principal_slot_eq_raw,
        `OAI.SevenEighths.PrincipalSlotEstimate.principal_coord_cancellation,
        `OAI.SevenEighths.ProbeEuler.coordR_norm_le] do
      unless reached.contains required do
        throw (IO.userError s!"Missing original-source proof dependency: {required}")
    if theoremName.toString.endsWith "actual_principal_slot_signed_error" then
      for required in #[`OAI.SevenEighths.PrincipalSlotEstimate.actual_target_norm,
          `OAI.SevenEighths.ProbeEuler.actualAPhase_norm_le_one] do
        unless reached.contains required do
          throw (IO.userError s!"Missing genuine coefficient adapter: {required}")
    IO.println s!"PASS principal-signed {theoremName}: {axioms}, closure={reached.size}"
  return 0
