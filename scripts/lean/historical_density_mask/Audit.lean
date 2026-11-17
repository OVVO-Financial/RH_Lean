import Lean
import Lean.Util.CollectAxioms

open Lean

namespace HistoricalDensityMaskAudit

partial def closure (env : Environment) (pending : List Name)
    (seen : NameSet := {}) : NameSet :=
  match pending with
  | [] => seen
  | n :: rest =>
    if seen.contains n then closure env rest seen
    else
      let refs := if (`RHLean).isPrefixOf n || (`_private).isPrefixOf n then
        match env.find? n with
        | none => []
        | some info =>
          let valueRefs := match info.value? (allowOpaque := true) with
            | none => []
            | some value => value.getUsedConstants.toList
          info.type.getUsedConstants.toList ++ valueRefs
        else []
      closure env (refs ++ rest) (seen.insert n)

def roots : Array Name := #[
  `RHLean.Analysis.historicalDensityMask_cost_identity,
  `RHLean.Analysis.historicalDensityMask_cost_lower,
  `RHLean.Analysis.historicalDensityMask_cost_gt_one,
  `RHLean.Analysis.historicalDensityMask_no_contraction,
  `RHLean.Analysis.historicalDensityMask_cost_sharp]

end HistoricalDensityMaskAudit

open HistoricalDensityMaskAudit in
def main (_args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let env ← importModules
    #[{ module := Name.mkSimple "research.HISTORICAL_DENSITY_MASK_OBSTRUCTION" }]
    Options.empty 1024 (loadExts := true)
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for root in roots do
    unless env.contains root do
      throw (IO.userError s!"Missing public declaration: {root}")
    let axioms ← (Lean.collectAxioms root : CoreM (Array Name)).toIO'
      { fileName := "<historical-density-mask-axioms>", fileMap := default } { env := env }
    for ax in axioms do
      unless allowed.contains ax do
        throw (IO.userError s!"Unapproved axiom for {root}: {ax}")
    let reached := closure env [root]
    unless reached.contains `Real.rpow do
      throw (IO.userError s!"Actual real-power weights absent: {root}")
    if root == `RHLean.Analysis.historicalDensityMask_cost_lower ||
        root == `RHLean.Analysis.historicalDensityMask_cost_gt_one ||
        root == `RHLean.Analysis.historicalDensityMask_no_contraction then
      unless reached.contains `RHLean.Analysis.historicalDensityMask_cost_identity do
        throw (IO.userError s!"Exact signed-moment cost identity absent: {root}")
    if root == `RHLean.Analysis.historicalDensityMask_no_contraction then
      unless reached.contains `RHLean.Analysis.historicalDensityMask_cost_gt_one do
        throw (IO.userError "Full mask did not use the tail obstruction")
      unless reached.contains `Finset.sum_erase_add do
        throw (IO.userError "Unit-removal identity absent")
    IO.println s!"PASS historical-density-mask {root}: {axioms}, closure={reached.size}"
  return 0
