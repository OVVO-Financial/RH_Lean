import Lean
import Lean.Util.CollectAxioms

open Lean

namespace WindowErrorClosureAudit

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
      let refs := if (`OAI).isPrefixOf n || (`RHLean).isPrefixOf n ||
          (`_private).isPrefixOf n then
        match env.find? n with
        | none => []
        | some info => match info.value? (allowOpaque := true) with
          | none => []
          | some value =>
            let live := if (`OAI.SevenEighths.RHLeanWindowSaturated).isPrefixOf n ||
                (`RHLean.Analysis).isPrefixOf n then reduceAdmin value else value
            live.getUsedConstants.toList
        else []
      closure env (refs ++ rest) (seen.insert n)

def rootHecke : Name :=
  `OAI.SevenEighths.RHLeanWindowSaturated.native_beta_le_window_error_closed_of_fine

def roots : Array Name := #[
  rootHecke,
  `OAI.SevenEighths.RHLeanWindowSaturated.native_beta_le_near_uniform_window_error_closed,
  `RHLean.Analysis.native_mertens_window_error_closed_of_fine,
  `RHLean.Analysis.native_mertens_fixed_window_error_closed_of_fine,
  `RHLean.Analysis.native_mertens_near_uniform_window_error_closed
]

def needed : Array Name := #[
  `OAI.SevenEighths.RHLeanWindowSaturated.withSmallerError,
  `OAI.SevenEighths.RHLeanWindowSaturated.withSmallerError_minimum,
  `OAI.SevenEighths.RHLeanWindowSaturated.native_beta_le_window_saturated_minimum_of_fine,
  `OAI.SevenEighths.ProbeFinalAssembly.exists_source_data,
  `OAI.SevenEighths.Parameters.exists_fixed_source,
  `OAI.SevenEighths.ProbeFinalAssembly.source_count_parameters,
  `OAI.SevenEighths.RHLeanNativeSevenEighthsReplay.native_beta_le_total_mass_boundary,
  `OAI.SevenEighths.RHLeanNativeSevenEighthsReplay.native_fixed_total_mass_probe_bounds,
  `OAI.SevenEighths.ProbeFinalAssembly.fixed_tilted_high_bound_anchored,
  `OAI.SevenEighths.HeckeSignal.nonzero_of_probe_bounds_variable_boundary
]

end WindowErrorClosureAudit

open WindowErrorClosureAudit in
def main (_args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let env ← importModules
    #[{ module := Name.mkSimple "research.oai_434.VF919WindowErrorClosure" }]
    Options.empty 1024 (loadExts := true)
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for root in roots do
    let axioms ← (Lean.collectAxioms root : CoreM (Array Name)).toIO'
      { fileName := "<window-error-closure-axioms>", fileMap := default } { env := env }
    for ax in axioms do
      unless allowed.contains ax do
        throw (IO.userError s!"Unapproved axiom for {root}: {ax}")
    let reached := closure env [root]
    unless reached.contains rootHecke do
      throw (IO.userError s!"Missing closed Hecke boundary in {root}")
    for required in needed do
      unless reached.contains required do
        throw (IO.userError s!"Missing live source dependency in {root}: {required}")
    if root.toString.endsWith "near_uniform_window_error_closed" then
      unless reached.contains `OAI.SevenEighths.Parameters.exists_near_uniform_high_data_fine do
        throw (IO.userError s!"Missing original fixed fine source in {root}")
    if (`RHLean.Analysis).isPrefixOf root then
      for required in #[`RHLean.Analysis.native_mertens_growth_at_hecke_beta,
          `RHLean.Analysis.native_zeta_rightmost_le_hecke_beta,
          `OAI.SevenEighths.HeckeDirichlet.LFunction_eq_dirichlet_product] do
        unless reached.contains required do
          throw (IO.userError s!"Missing native arithmetic transfer in {root}: {required}")
    IO.println s!"PASS window-error-closure {root}: {axioms}, closure={reached.size}"
  return 0
