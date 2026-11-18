import Lean
import Lean.Util.CollectAxioms

open Lean

namespace NymanThreeProfileAudit

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
  `RHLean.Analysis.nyman_two_band_profile_source,
  `RHLean.Analysis.nyman_three_profile_coercivity,
  `RHLean.Analysis.nyman_three_profile_restored_lower]

end NymanThreeProfileAudit

open NymanThreeProfileAudit in
def main (_args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let env ← importModules
    #[{ module := Name.mkSimple "research.NYMAN_THREE_PROFILE_COERCIVITY" }]
    Options.empty 1024 (loadExts := true)
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for root in roots do
    unless env.contains root do
      throw (IO.userError s!"Missing public declaration: {root}")
    let axioms ← (Lean.collectAxioms root : CoreM (Array Name)).toIO'
      { fileName := "<nyman-three-profile-axioms>", fileMap := default } { env := env }
    for ax in axioms do
      unless allowed.contains ax do
        throw (IO.userError s!"Unapproved axiom for {root}: {ax}")
    let reached := closure env [root]
    for dep in #[`RHLean.Analysis.nymanTwoBandProfile, `RHLean.Analysis.nymanBandCount] do
      unless reached.contains dep do
        throw (IO.userError s!"Original two-band floor dependency absent: {root}, {dep}")
    if root == `RHLean.Analysis.nyman_two_band_profile_source then
      unless reached.contains `RHLean.Analysis.nymanCorrectionFloor do
        throw (IO.userError "Original correction-floor source bridge absent")
    else
      for dep in #[`RHLean.Analysis.nymanWindowEnergy, `RHLean.Analysis.nymanThreeProfileWindows] do
        unless reached.contains dep do
          throw (IO.userError s!"Complete observation energy absent: {root}, {dep}")
      for suffix in [".profile_self", ".profile_abs_le", ".window_sample", ".recover_coefficient"] do
        unless reached.toList.any (fun n => n.toString.endsWith suffix) do
          throw (IO.userError s!"Triangular proof dependency absent: {root}, {suffix}")
    if root == `RHLean.Analysis.nyman_three_profile_restored_lower then
      unless reached.contains `RHLean.Analysis.nyman_three_profile_coercivity do
        throw (IO.userError "Restored theorem did not consume profile coercivity")
    IO.println s!"PASS nyman-three-profile {root}: {axioms}, closure={reached.size}"
  return 0
