import Lean
import Lean.Util.CollectAxioms

open Lean

namespace FixedGcdRowAudit

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
  `RHLean.Proof.eulerFixedGcdRowInt_cast,
  `RHLean.Proof.eulerBilinearInt_cast,
  `RHLean.Proof.eulerFixedGcdRowInt_139_six,
  `RHLean.Proof.eulerBilinearInt_139,
  `RHLean.Proof.mertensSummatory_19320,
  `RHLean.Proof.eulerFixedGcdRow_six_witness,
  `RHLean.Proof.not_pointwise_mertens_le_fixedGcdRow_six,
  `RHLean.Proof.not_pointwise_centered_mertens_le_fixedGcdRow_six]

end FixedGcdRowAudit

open FixedGcdRowAudit in
def main (_args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let env ← importModules
    #[{ module := Name.mkSimple "research.EULER_FIXED_GCD_ROW_OBSTRUCTION" }]
    Options.empty 1024 (loadExts := true)
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for root in roots do
    unless env.contains root do
      throw (IO.userError s!"Missing public declaration: {root}")
    let axioms ← (Lean.collectAxioms root : CoreM (Array Name)).toIO'
      { fileName := "<fixed-gcd-row-axioms>", fileMap := default } { env := env }
    for ax in axioms do
      unless allowed.contains ax do
        throw (IO.userError s!"Unapproved axiom for {root}: {ax}")
    let reached := closure env [root]
    if root == `RHLean.Proof.not_pointwise_mertens_le_fixedGcdRow_six ||
        root == `RHLean.Proof.not_pointwise_centered_mertens_le_fixedGcdRow_six then
      for dependency in #[
          `RHLean.Proof.eulerFixedGcdRowInt_139_six,
          `RHLean.Proof.eulerBilinearInt_139,
          `RHLean.Proof.eulerBilinearInt_cast,
          `RHLean.Proof.eulerSelfDualBilinear_eq_two_mertens_sub_endpoint,
          `RHLean.Proof.mertensSummatory_19320] do
        unless reached.contains dependency do
          throw (IO.userError s!"Missing original-source dependency: {dependency}")
    IO.println s!"PASS fixed-gcd-row {root}: {axioms}, closure={reached.size}"
  return 0
