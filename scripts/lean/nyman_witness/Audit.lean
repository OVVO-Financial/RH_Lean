import Lean
import Lean.Util.CollectAxioms
open Lean

private partial def visit (env : Environment) (todo : List Name) (seen : NameSet := {}) : NameSet :=
  match todo with
  | [] => seen
  | n :: ns =>
    if seen.contains n then visit env ns seen else
      let deps := if (`RHLean).isPrefixOf n || (`_private).isPrefixOf n then
        match env.find? n with
        | none => []
        | some c => c.type.getUsedConstants.toList ++
            ((c.value? (allowOpaque := true)).map (fun e => e.getUsedConstants.toList)).getD []
        else []
      visit env (deps ++ ns) (seen.insert n)

def main (_ : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let env ← importModules #[{ module := Name.mkSimple "research.NYMAN_WITNESS_RANK" }]
    Options.empty 1024 (loadExts := true)
  let base := `RHLean.Analysis
  let roots := #[(`nyman_witness_reciprocal, #[`padicValRat]),
    (`nyman_witness_amplitudes_of_prime, #[base ++ `nyman_witness_reciprocal,
      base ++ `nymanFlatKernel_eq_original, base ++ `nyman_ridge_gap, `ArithmeticFunction.moebius_apply_prime]),
    (`nyman_witness_amplitudes, #[`Nat.bertrand, base ++ `nyman_witness_amplitudes_of_prime]),
    (`nyman_witness_first_clip, #[base ++ `nyman_ridge_first_double, base ++ `nyman_witness_amplitudes,
      base ++ `nyman_ridge_residual_profiles]),
    (`nyman_witness_clip_plateau, #[base ++ `nyman_ridge_floor_profiles, base ++ `nymanBandCount]),
    (`nyman_witness_clip_energy, #[base ++ `nyman_witness_clip_plateau, base ++ `nymanWeight]),
    (`nyman_witness_clip_cost, #[base ++ `nyman_witness_clip_energy, base ++ `nyman_witness_amplitudes]),
    (`nyman_witness_relation_coordinate, #[base ++ `nymanFlatKernel_eq_original,
      `ArithmeticFunction.moebius_apply_prime, `padicValRat]),
    (`nyman_witness_error_counts, #[base ++ `nyman_ridge_floor_profiles, base ++ `nyman_ridge_residual_profiles]),
    (`nyman_witness_two_amplitudes, #[base ++ `nyman_witness_relation_coordinate, base ++ `nyman_ridge_gap]),
    (`nyman_witness_clip_fibres, #[base ++ `nyman_witness_two_amplitudes, base ++ `nyman_witness_error_counts]),
    (`nyman_witness_clip_zero_iff, #[base ++ `nyman_witness_clip_fibres,
      base ++ `nyman_ridge_first_layer, base ++ `nyman_ridge_first_double])]
  for (leaf, required) in roots do
    let n := base ++ leaf
    unless env.contains n do throw (IO.userError s!"missing public theorem {n}")
    let ax ← (Lean.collectAxioms n : CoreM (Array Name)).toIO'
      { fileName := "witness-audit", fileMap := default } { env := env }
    for a in ax do
      unless #[`propext, `Classical.choice, `Quot.sound].contains a do throw (IO.userError s!"{n}: {a}")
    let names := visit env [n]
    for d in required do
      unless names.contains d do throw (IO.userError s!"{n}: missing dependency {d}")
    IO.println s!"WITNESS_AUDIT {n} axioms={ax} dependencies={names.toList.length}"
  return 0
