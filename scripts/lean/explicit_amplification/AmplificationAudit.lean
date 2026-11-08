import Lean
import Lean.Util.CollectAxioms

/-! Read-only audit of the live proof values of the unconditional terminals. -/

open Lean

namespace ExplicitAmplificationAudit

def shouldExpand (n : Name) : Bool :=
  (`OAI).isPrefixOf n || (`RHLean).isPrefixOf n || (`_private).isPrefixOf n

partial def reduceAdmin : Expr → Expr
  | .letE _ _ value body _ => reduceAdmin (body.instantiate1 value)
  | .app fn arg =>
    let f := reduceAdmin fn
    match f with
    | .lam _ _ body _ => reduceAdmin (body.instantiate1 arg)
    | _ => .app f (reduceAdmin arg)
  | .lam n t b bi => .lam n (reduceAdmin t) (reduceAdmin b) bi
  | .forallE n t b bi => .forallE n (reduceAdmin t) (reduceAdmin b) bi
  | .mdata _ b => reduceAdmin b
  | .proj n i b => .proj n i (reduceAdmin b)
  | other => other

def reduceBeforeCollecting (n : Name) : Bool :=
  (`OAI.SevenEighths.RHLeanActualSlotMin).isPrefixOf n ||
    (`RHLean.Analysis).isPrefixOf n ||
    n.toString.endsWith "_total_mass"

partial def closure (env : Environment) (pending : List Name)
    (seen : NameSet := {}) : NameSet :=
  match pending with
  | [] => seen
  | n :: rest =>
    if seen.contains n then closure env rest seen
    else
      let seen' := seen.insert n
      let refs := if shouldExpand n then
        match env.find? n with
        | none => []
        | some info => match info.value? (allowOpaque := true) with
          | none => []
          | some value =>
            let live := if reduceBeforeCollecting n then reduceAdmin value else value
            live.getUsedConstants.toList
        else []
      closure env (refs ++ rest) seen'

def rootHecke : Name :=
  `OAI.SevenEighths.native_beta_le_explicit_slot_count_total_mass

def nativeRoots : Array Name := #[
  `RHLean.Analysis.native_mertens_explicit_slot_count_total_mass,
  `RHLean.Analysis.native_mertens_fixed_explicit_slot_count_total_mass
]

def ratioRoots : Array Name := #[
  `RHLean.Analysis.native_amplification_explicit_slot_count_total_mass,
  `RHLean.Analysis.native_amplification_fixed_explicit_slot_count_total_mass,
  `RHLean.Analysis.native_amplification_log_fixed_explicit_slot_count_total_mass,
  `RHLean.Analysis.native_amplification_log_explicit_slot_count_total_mass,
  `RHLean.Analysis.native_amplification_limsup_explicit_slot_count_total_mass,
  `RHLean.Analysis.native_amplification_limsup_lt_three_quarters,
  `RHLean.Analysis.native_amplification_eventually_lt_cutoff
]

def finiteSourceNeeded : Array Name := #[
  `OAI.SevenEighths.Parameters.exists_explicit_high_data_fine,
  `OAI.SevenEighths.RHLeanActualSlotMin.native_beta_le_true_physical_slot_minimum_total_mass_of_fine
]

def ratioNeeded : Array Name := #[
  `RHLean.Proof.mertensSummatoryInt_cast,
  `RHLean.Proof.squareRootHistoricalK_one_le,
  `RHLean.Proof.squareRootEndpointAmplification_le_of_mertensPower,
  `RHLean.Proof.squareRootAmplificationMax_le_of_mertensPower
]

end ExplicitAmplificationAudit

open ExplicitAmplificationAudit in
def main (_args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let env ← importModules
    #[{ module := Name.mkSimple "research.oai_434.VF919ExplicitAmplificationBound" }]
    Options.empty 1024 (loadExts := true)
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for root in #[rootHecke] ++ nativeRoots ++ ratioRoots do
    let axioms ← (Lean.collectAxioms root : CoreM (Array Name)).toIO'
      { fileName := "<explicit-amplification-axioms>", fileMap := default } { env := env }
    for ax in axioms do
      unless allowed.contains ax do
        throw (IO.userError s!"Unapproved axiom for {root}: {ax}")
    let reached := closure env [root]
    for required in finiteSourceNeeded do
      unless reached.contains required do
        throw (IO.userError s!"Missing live finite-source dependency for {root}: {required}")
    if root != rootHecke then
      unless reached.contains rootHecke &&
          reached.contains `RHLean.Analysis.native_mertens_growth_at_hecke_beta do
        throw (IO.userError s!"Missing explicit endpoint or native Mertens transfer: {root}")
    if ratioRoots.contains root then
      for required in ratioNeeded do
        unless reached.contains required do
          throw (IO.userError s!"Missing exact historical amplification consumer for {root}: {required}")
    if reached.contains `OAI.SevenEighths.native_beta_le_explicit_slot_count then
      throw (IO.userError s!"Old weaker explicit endpoint used by {root}")
    IO.println s!"PASS explicit amplification terminal {root}: {axioms}, closure={reached.size}"
  return 0
