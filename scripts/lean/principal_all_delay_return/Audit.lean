import Lean
import Lean.Util.CollectAxioms

open Lean

namespace PrincipalAllDelayAudit

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
  `OAI.SevenEighths.PrincipalAllDelayReturn.slotResidueC_shift_right,
  `OAI.SevenEighths.PrincipalAllDelayReturn.gaussian_atom_dilation,
  `OAI.SevenEighths.PrincipalAllDelayReturn.finite_response_contour,
  `OAI.SevenEighths.PrincipalAllDelayReturn.slotResidueC_all_delay_error,
  `OAI.SevenEighths.PrincipalAllDelayReturn.normalized_source_all_delay_error,
  `OAI.SevenEighths.PrincipalAllDelayReturn.source_correction_all_delay_error]

end PrincipalAllDelayAudit

open PrincipalAllDelayAudit in
def main (_args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let env ← importModules
    #[{ module := Name.mkSimple "research.oai_434.VF919PrincipalAllDelayReturn" }]
    Options.empty 1024 (loadExts := true)
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for root in roots do
    let axioms ← (Lean.collectAxioms root : CoreM (Array Name)).toIO'
      { fileName := "<principal-all-delay-axioms>", fileMap := default } { env := env }
    for ax in axioms do
      unless allowed.contains ax do
        throw (IO.userError s!"Unapproved axiom for {root}: {ax}")
    let reached := closure env [root]
    let required := if root.toString.endsWith "all_delay_error" then #[
      `OAI.SevenEighths.PrincipalAllDelayReturn.slotResidueC_shift_right,
      `OAI.SevenEighths.PrincipalAllDelayReturn.gaussian_atom_dilation,
      `OAI.SevenEighths.PrincipalSignalComparison.raw_inverse_ae_reciprocal,
      `OAI.SevenEighths.PrincipalSlotEstimate.weighted_principal_product_partial_power,
      `OAI.SevenEighths.PrincipalSlotEstimate.principal_product_response_terms_eval,
      `OAI.SevenEighths.HeckeSignal.signal_eq_contour,
      `OAI.SevenEighths.HeckeSignal.quotient_bound,
      `OAI.SevenEighths.Continuation.vertical_integral_eq_of_polynomial_gaussian_bound]
      else if root.toString.endsWith "finite_response_contour" then #[
      `OAI.SevenEighths.PrincipalAllDelayReturn.gaussian_atom_dilation,
      `OAI.SevenEighths.HeckeSignal.signal_eq_contour]
      else #[]
    for dependency in required do
      unless reached.contains dependency do
        throw (IO.userError s!"Missing original-source dependency in {root}: {dependency}")
    if root.toString.endsWith "normalized_source_all_delay_error" then
      unless reached.contains
          `OAI.SevenEighths.PrincipalSignalComparison.normalized_source_double_residue_variable_x do
        throw (IO.userError "Missing original physical normalization")
    if root.toString.endsWith "source_correction_all_delay_error" then
      for dependency in #[
          `OAI.SevenEighths.PrincipalSignalComparison.sourceCorrection_differentiable,
          `OAI.SevenEighths.PrincipalSignalComparison.sourceCorrection_bound] do
        unless reached.contains dependency do
          throw (IO.userError s!"Missing actual correction supplier: {dependency}")
    IO.println s!"PASS principal-all-delay {root}: {axioms}, closure={reached.size}"
  return 0
