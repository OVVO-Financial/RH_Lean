import Lean
import Lean.Util.CollectAxioms

open Lean

namespace PrincipalResponseInversionAudit

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

def roots : Array Name := #[
  `OAI.SevenEighths.PrincipalResponseInversion.weighted_dilation,
  `OAI.SevenEighths.PrincipalResponseInversion.applyTerms_norm_le,
  `OAI.SevenEighths.PrincipalResponseInversion.weighted_prefix_bddAbove,
  `OAI.SevenEighths.PrincipalResponseInversion.power_bound_of_response,
  `OAI.SevenEighths.PrincipalResponseInversion.signal_small_argument_bound,
  `OAI.SevenEighths.PrincipalResponseInversion.signal_power_bound_of_eventual_response,
  `OAI.SevenEighths.PrincipalResponseInversion.principal_response_eventually_contracts,
  `OAI.SevenEighths.PrincipalResponseInversion.signal_power_bound_of_principal_response]

end PrincipalResponseInversionAudit

open PrincipalResponseInversionAudit in
def main (_args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let env ← importModules
    #[{ module := Name.mkSimple "research.oai_434.VF919PrincipalResponseInversion" }]
    Options.empty 1024 (loadExts := true)
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for root in roots do
    let axioms ← (Lean.collectAxioms root : CoreM (Array Name)).toIO'
      { fileName := "<principal-response-inversion-axioms>", fileMap := default } { env := env }
    for ax in axioms do
      unless allowed.contains ax do
        throw (IO.userError s!"Unapproved axiom for {root}: {ax}")
    let reached := closure env [root]
    let required := if root.toString.endsWith "signal_power_bound_of_principal_response" then #[
      `OAI.SevenEighths.PrincipalResponseInversion.power_bound_of_response,
      `OAI.SevenEighths.PrincipalResponseInversion.weighted_prefix_bddAbove,
      `OAI.SevenEighths.PrincipalResponseInversion.weighted_dilation,
      `OAI.SevenEighths.HeckeSignal.signal_bound_at_zero,
      `OAI.SevenEighths.HeckeSignal.signal_continuousOn,
      `OAI.SevenEighths.PrincipalSlotEstimate.principal_product_response_terms_mass,
      `OAI.SevenEighths.PrincipalSlotEstimate.principal_product_response_delays,
      `OAI.SevenEighths.PrincipalSlotEstimate.principal_response_mass_majorant_tendsto]
      else if root.toString.endsWith "signal_power_bound_of_eventual_response" then #[
      `OAI.SevenEighths.PrincipalResponseInversion.power_bound_of_response,
      `OAI.SevenEighths.PrincipalResponseInversion.weighted_prefix_bddAbove,
      `OAI.SevenEighths.HeckeSignal.signal_bound_at_zero,
      `OAI.SevenEighths.HeckeSignal.signal_continuousOn]
      else if root.toString.endsWith "power_bound_of_response" then #[
      `OAI.SevenEighths.PrincipalResponseInversion.weighted_prefix_bddAbove,
      `OAI.SevenEighths.PrincipalResponseInversion.applyTerms_norm_le]
      else #[]
    for dependency in required do
      unless reached.contains dependency do
        throw (IO.userError s!"Missing original-source dependency in {root}: {dependency}")
    IO.println s!"PASS principal-response-inversion {root}: {axioms}, closure={reached.size}"
  return 0

