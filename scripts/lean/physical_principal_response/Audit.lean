import Lean
import Lean.Util.CollectAxioms

open Lean

namespace PhysicalPrincipalResponseAudit

partial def closure (env : Environment) (pending : List Name)
    (seen : NameSet := {}) : NameSet :=
  match pending with
  | [] => seen
  | n :: rest =>
    if seen.contains n then closure env rest seen
    else
      let refs := if (`OAI).isPrefixOf n || (`RHLean).isPrefixOf n || (`_private).isPrefixOf n then
        match env.find? n with
        | none => []
        | some info => match info.value? (allowOpaque := true) with
          | none => []
          | some value => value.getUsedConstants.toList
        else []
      closure env (refs ++ rest) (seen.insert n)

def roots : Array Name := #[
  `OAI.SevenEighths.PhysicalPrincipalResponse.eventually_power_lower,
  `OAI.SevenEighths.PhysicalPrincipalResponse.actual_window_all_delay_error,
  `OAI.SevenEighths.PhysicalPrincipalResponse.actual_ray_principal_response]

end PhysicalPrincipalResponseAudit

open PhysicalPrincipalResponseAudit in
def main (_args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let env ← importModules
    #[{ module := Name.mkSimple "research.oai_434.VF919PhysicalPrincipalResponse" }]
    Options.empty 1024 (loadExts := true)
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for root in roots do
    unless env.contains root do
      throw (IO.userError s!"Missing public declaration: {root}")
    let axioms ← (Lean.collectAxioms root : CoreM (Array Name)).toIO'
      { fileName := "<physical-principal-response-axioms>", fileMap := default } { env := env }
    for ax in axioms do
      unless allowed.contains ax do
        throw (IO.userError s!"Unapproved axiom for {root}: {ax}")
    let reached := closure env [root]
    let required := if root.toString.endsWith "actual_ray_principal_response" then #[
      `OAI.SevenEighths.PhysicalPrincipalResponse.eventually_power_lower,
      `OAI.SevenEighths.PhysicalPrincipalResponse.actual_window_all_delay_error,
      `OAI.SevenEighths.ProbePrincipalPhysical.physical_principal_residue_remainder_tilted_anchored,
      `OAI.SevenEighths.ProbePrincipalResidueActual.actual_window_residue,
      `OAI.SevenEighths.PrincipalAllDelayReturn.normalized_source_all_delay_error,
      `OAI.SevenEighths.ProbeRaySlots.power_ray_mass_and_normalizer,
      `OAI.SevenEighths.ProbePrincipalNormalizer.sourceResidueConstant_ne_zero,
      `OAI.SevenEighths.RHLeanNativeSevenEighthsReplay.native_beta_le_seven_eighths]
      else if root.toString.endsWith "actual_window_all_delay_error" then #[
      `OAI.SevenEighths.ProbePrincipalResidueActual.actual_window_residue,
      `OAI.SevenEighths.PrincipalAllDelayReturn.normalized_source_all_delay_error,
      `OAI.SevenEighths.PrincipalSignalComparison.idealCoeff_norm_one_of_coprime]
      else #[]
    for dependency in required do
      unless reached.contains dependency do
        throw (IO.userError s!"Missing original-source dependency in {root}: {dependency}")
    IO.println s!"PASS physical-principal-response {root}: {axioms}, closure={reached.size}"
  return 0
