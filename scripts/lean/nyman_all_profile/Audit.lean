import Lean
import Lean.Util.CollectAxioms

open Lean

namespace NymanAllProfileAudit

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
  `RHLean.Analysis.nyman_dual_profile_leakage,
  `RHLean.Analysis.nyman_all_profile_coercivity,
  `RHLean.Analysis.nyman_all_profile_restored_lower]

end NymanAllProfileAudit

open NymanAllProfileAudit in
def main (_args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let env ← importModules
    #[{ module := Name.mkSimple "research.NYMAN_ALL_PROFILE_COERCIVITY" }]
    Options.empty 1024 (loadExts := true)
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for root in roots do
    unless env.contains root do
      throw (IO.userError s!"Missing public declaration: {root}")
    let axioms ← (Lean.collectAxioms root : CoreM (Array Name)).toIO'
      { fileName := "<nyman-all-profile-axioms>", fileMap := default } { env := env }
    for ax in axioms do
      unless allowed.contains ax do
        throw (IO.userError s!"Unapproved axiom for {root}: {ax}")
    let reached := closure env [root]
    for dep in #[`RHLean.Analysis.nymanDualProfile, `RHLean.Analysis.nymanCorrectionFloor,
        `RHLean.Analysis.nymanDualPair] do
      unless reached.contains dep do
        throw (IO.userError s!"Original paired source absent: {root}, {dep}")
    for suffix in [".profile_source", ".floor_pair_bounds"] do
      unless reached.toList.any (fun n => n.toString.endsWith suffix) do
        throw (IO.userError s!"Exact floor proof absent: {root}, {suffix}")
    if root != `RHLean.Analysis.nyman_dual_profile_leakage then
      for dep in #[`RHLean.Analysis.nymanDualEnergy, `RHLean.Analysis.nymanDualWindows,
          `RHLean.Analysis.nymanDualSum, `RHLean.Analysis.nyman_dual_profile_leakage] do
        unless reached.contains dep do
          throw (IO.userError s!"All-head source dependency absent: {root}, {dep}")
      for suffix in [".pair_self", ".paired_sample", ".later_zero", ".pair_prefix",
          ".geometric_three", ".geometric_nine"] do
        unless reached.toList.any (fun n => n.toString.endsWith suffix) do
          throw (IO.userError s!"All-head proof dependency absent: {root}, {suffix}")
    if root == `RHLean.Analysis.nyman_all_profile_restored_lower then
      unless reached.contains `RHLean.Analysis.nyman_all_profile_coercivity do
        throw (IO.userError "Restored theorem did not consume the lower bound")
    IO.println s!"PASS nyman-all-profile {root}: {axioms}, closure={reached.size}"
  return 0
