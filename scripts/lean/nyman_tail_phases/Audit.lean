import Lean
import Lean.Util.CollectAxioms
open Lean

private partial def closure (env : Environment) (queue : List Name) (seen : NameSet := {}) : NameSet :=
  match queue with
  | [] => seen
  | n :: rest =>
    if seen.contains n then closure env rest seen else
      let deps := if (`RHLean).isPrefixOf n || (`_private).isPrefixOf n then
        match env.find? n with
        | none => []
        | some info => info.type.getUsedConstants.toList ++
            ((info.value? (allowOpaque := true)).map (fun x => x.getUsedConstants.toList)).getD []
        else []
      closure env (deps ++ rest) (seen.insert n)

def main (_ : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let env ← importModules #[{ module := Name.mkSimple "research.NYMAN_TAIL_PHASES" }]
    Options.empty 1024 (loadExts := true)
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let base := `RHLean.Analysis
  let roots := #[(`nyman_cutoff_primitive_periodic, #[`nyman_period_residual_energy, `nymanResidue]),
    (`nyman_tail_abel, #[`nyman_cutoff_primitive_periodic, `nymanWeight, `nymanCovariance, `nymanPeriodBias]),
    (`nyman_tail_two_phases, #[`nyman_tail_abel, `nymanPhysicalTail, `nymanResidual]),
    (`nyman_two_moment_tail_phases, #[`nyman_tail_two_phases, `nyman_period_residual_energy, `nymanResidue])]
  for (leaf, required) in roots do
    let root := base ++ leaf
    unless env.contains root do throw (IO.userError s!"missing public theorem: {root}")
    let ax ← (Lean.collectAxioms root : CoreM (Array Name)).toIO'
      { fileName := "tail-phase-audit", fileMap := default } { env := env }
    for a in ax do
      unless allowed.contains a do throw (IO.userError s!"unapproved dependency: {root} {a}")
    let names := closure env [root]
    for d in required do
      unless names.contains (base ++ d) do throw (IO.userError s!"missing source edge: {root} {d}")
    IO.println s!"TAIL_AUDIT {root} axioms={ax} dependencies={names.toList.length}"
  return 0
