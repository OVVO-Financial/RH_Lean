import Lean
import Lean.Util.CollectAxioms

open Lean

def main (_args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let env ← importModules
    #[{ module := `research.oai_434.VF919ExplicitSquareBlockPacking }]
    Options.empty 1024 (loadExts := true)
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let roots : Array Name := #[
    `RHLean.Proof.groupedSquareBlocks_sum,
    `OAI.SevenEighths.RHLeanNearUniformSlotPacking.native_beta_le_near_uniform_slots,
    `RHLean.Analysis.native_mertens_near_uniform_slots
  ]
  for root in roots do
    let axioms ← (Lean.collectAxioms root : CoreM (Array Name)).toIO'
      { fileName := "<square-block-slot-axioms>", fileMap := default } { env := env }
    for ax in axioms do
      unless allowed.contains ax do
        IO.eprintln s!"DISALLOWED AXIOM {root}: {ax}"
        return 1
    IO.println s!"PASS {root} axioms: {axioms.toList}"
  return 0
