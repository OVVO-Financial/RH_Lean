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
  let env ← importModules #[{ module := Name.mkSimple "research.NYMAN_RIDGE_PROFILES" }]
    Options.empty 1024 (loadExts := true)
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let base := `RHLean.Analysis
  let roots := #[(`nyman_ridge_gap, #[`nymanRidgeS]),
    (`nyman_ridge_residue_floor, #[`nymanResidue_eq_div_sub_floor, `nymanBandCount]),
    (`nyman_ridge_first_layer, #[`nymanBandCount]), (`nyman_ridge_first_double, #[`nymanBandCount]),
    (`nyman_ridge_moments, #[`nyman_two_band_moment_solver, `nyman_ridge_gap,
      `nyman_flat_reciprocal_moment, `nymanFlatKernel_one, `nymanRidgeRepair]),
    (`nyman_ridge_residual_profiles, #[`nymanResidual, `nymanFlatCoefficient, `nymanFlatMoment,
      `nymanRidgeRepair, `nymanRidgeG, `nymanResidue]),
    (`nyman_ridge_floor_profiles, #[`nyman_ridge_residue_floor, `nyman_ridge_gap, `nymanBandCount])]
  for (leaf, required) in roots do
    let root := base ++ leaf
    unless env.contains root do throw (IO.userError s!"missing public theorem: {root}")
    let ax ← (Lean.collectAxioms root : CoreM (Array Name)).toIO'
      { fileName := "ridge-audit", fileMap := default } { env := env }
    for a in ax do
      unless allowed.contains a do throw (IO.userError s!"unapproved axiom: {root} {a}")
    let names := closure env [root]
    for d in required do
      unless names.contains (base ++ d) do throw (IO.userError s!"missing source edge: {root} {d}")
    IO.println s!"RIDGE_AUDIT {root} axioms={ax} dependencies={names.toList.length}"
  return 0
