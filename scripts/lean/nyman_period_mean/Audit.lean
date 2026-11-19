import Lean
import Lean.Util.CollectAxioms

open Lean

private partial def closure (env : Environment) (queue : List Name) (seen : NameSet := {}) : NameSet :=
  match queue with
  | [] => seen
  | n :: todo =>
    if seen.contains n then closure env todo seen else
    let refs := if (`RHLean).isPrefixOf n || (`_private).isPrefixOf n then
      match env.find? n with
      | none => []
      | some info => info.type.getUsedConstants.toList ++
          ((info.value? (allowOpaque := true)).map (fun x => x.getUsedConstants.toList)).getD []
      else []
    closure env (refs ++ todo) (seen.insert n)

def main (_ : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let env ← importModules #[{ module := Name.mkSimple "research.NYMAN_PERIOD_MEAN" }]
    Options.empty 1024 (loadExts := true)
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let base := `RHLean.Analysis
  let roots := #[(`nyman_period_cell_sum, #[`nymanCellFluct]),
    (`nyman_period_cell_pair, #[`nymanCellFluct]),
    (`nyman_period_residual_energy, #[`nymanResidual, `nymanResidue, `nymanCovariance,
      `nymanPeriodBias, `nyman_period_cell_sum, `nyman_period_cell_pair]),
    (`nyman_period_mean_eq_covariance_iff, #[`nyman_period_residual_energy, `nymanResidual,
      `nymanCovariance, `nymanPeriodBias])]
  for (leaf, required) in roots do
    let root := base ++ leaf
    unless env.contains root do throw (IO.userError s!"missing export: {root}")
    let axs ← (Lean.collectAxioms root : CoreM (Array Name)).toIO'
      { fileName := "nyman-period-audit", fileMap := default } { env := env }
    for ax in axs do
      unless allowed.contains ax do throw (IO.userError s!"unapproved axiom: {root} {ax}")
    let visited := closure env [root]
    for dep in required do
      unless visited.contains (base ++ dep) do throw (IO.userError s!"missing source {root} {dep}")
    IO.println s!"PERIOD_AUDIT {root} axioms={axs} dependencies={visited.toList.length}"
  return 0
