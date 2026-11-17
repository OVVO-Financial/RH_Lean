import Lean
import Lean.Util.CollectAxioms

open Lean

namespace NymanDivisorSignAudit

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
  `RHLean.Analysis.nymanHighDivisorJump_210_profile,
  `RHLean.Analysis.nymanHighDivisorJump_210_opposite_signs,
  `RHLean.Analysis.nyman_210_long_middle_witness,
  `RHLean.Analysis.not_nyman_long_middle_parity_nonnegative,
  `RHLean.Analysis.nymanLogTail_210_opposite_steps,
  `RHLean.Analysis.nyman_flat_210_step_profile,
  `RHLean.Analysis.nyman_flat_210_opposite_steps]

end NymanDivisorSignAudit

open NymanDivisorSignAudit in
def main (_args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let env ← importModules
    #[{ module := Name.mkSimple "research.NYMAN_DIVISOR_JUMP_SIGN_OBSTRUCTION" }]
    Options.empty 1024 (loadExts := true)
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for root in roots do
    unless env.contains root do
      throw (IO.userError s!"Missing public declaration: {root}")
    let axioms ← (Lean.collectAxioms root : CoreM (Array Name)).toIO'
      { fileName := "<nyman-divisor-sign-axioms>", fileMap := default } { env := env }
    for ax in axioms do
      unless allowed.contains ax do
        throw (IO.userError s!"Unapproved axiom for {root}: {ax}")
    let reached := closure env [root]
    if root != `RHLean.Analysis.nyman_210_long_middle_witness then
      unless reached.contains `RHLean.Analysis.nymanHighDivisorJump do
        throw (IO.userError s!"Original divisor source absent: {root}")
    if root == `RHLean.Analysis.nyman_flat_210_step_profile ||
        root == `RHLean.Analysis.nyman_flat_210_opposite_steps then
      for dependency in #[
          `RHLean.Analysis.nyman_flat_complete_return,
          `RHLean.Analysis.nyman_flat_step_before_corrections,
          `RHLean.Analysis.nymanHighDivisorJump_radical,
          `RHLean.Analysis.nymanHighDivisorJump_210_profile] do
        unless reached.contains dependency do
          throw (IO.userError s!"Missing complete-source dependency: {dependency}")
    IO.println s!"PASS nyman-divisor-sign {root}: {axioms}, closure={reached.size}"
  return 0
