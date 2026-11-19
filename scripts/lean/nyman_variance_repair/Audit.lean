import Lean
import Lean.Util.CollectAxioms

open Lean

namespace NymanVarianceRepairAudit

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
          let values := match info.value? (allowOpaque := true) with
            | none => []
            | some value => value.getUsedConstants.toList
          info.type.getUsedConstants.toList ++ values
        else []
      closure env (refs ++ rest) (seen.insert n)

def roots : Array Name := #[
  `RHLean.Analysis.nyman_jordan_two_divisor_sum,
  `RHLean.Analysis.nyman_jordan_two_lower,
  `RHLean.Analysis.nyman_covariance_divisor_squares,
  `RHLean.Analysis.nyman_covariance_singleton_lower,
  `RHLean.Analysis.nyman_flat_same_support_repair]

end NymanVarianceRepairAudit

open NymanVarianceRepairAudit in
def main (_args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let env ← importModules #[{ module := Name.mkSimple "research.NYMAN_VARIANCE_REPAIR" }]
    Options.empty 1024 (loadExts := true)
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for root in roots do
    unless env.contains root do
      throw (IO.userError s!"Missing public theorem: {root}")
    let axioms ← (Lean.collectAxioms root : CoreM (Array Name)).toIO'
      { fileName := "<nyman-variance-repair>", fileMap := default } { env := env }
    for ax in axioms do
      unless allowed.contains ax do
        throw (IO.userError s!"Unapproved axiom: {root}, {ax}")
    let reached := closure env [root]
    unless reached.contains `RHLean.Analysis.nymanJordanTwo do
      throw (IO.userError s!"Arithmetic Jordan source absent: {root}")
    if root == `RHLean.Analysis.nyman_covariance_singleton_lower ||
        root == `RHLean.Analysis.nyman_flat_same_support_repair then
      for dep in #[`RHLean.Analysis.nymanCovariance,
          `RHLean.Analysis.nyman_covariance_divisor_squares,
          `RHLean.Analysis.nyman_jordan_two_lower,
          `RHLean.Analysis.nyman_jordan_two_divisor_sum] do
        unless reached.contains dep do
          throw (IO.userError s!"Full quadratic dependency absent: {root}, {dep}")
    if root == `RHLean.Analysis.nyman_flat_same_support_repair then
      for dep in #[`RHLean.Analysis.nymanFlatCoefficient,
          `RHLean.Analysis.nymanFlatKernel_eq_original,
          `ArithmeticFunction.moebius] do
        unless reached.contains dep do
          throw (IO.userError s!"Original taper dependency absent: {dep}")
    IO.println s!"PASS nyman-variance-repair {root}: {axioms}, closure={reached.size}"
  return 0
