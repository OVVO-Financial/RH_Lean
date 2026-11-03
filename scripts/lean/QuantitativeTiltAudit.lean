import Lean
import Lean.Util.CollectAxioms

open Lean
namespace QuantitativeTiltAudit

def dottedName (s : String) : Name :=
  (s.splitOn ".").foldl (fun n p => Name.str n p) Name.anonymous

partial def administrativeReduce : Expr → Expr
  | .letE _ _ v b _ => administrativeReduce (b.instantiate1 v)
  | .app f a =>
    let f' := administrativeReduce f
    match f' with
    | .lam _ _ b _ => administrativeReduce (b.instantiate1 a)
    | _ => .app f' (administrativeReduce a)
  | .lam n t b bi => .lam n (administrativeReduce t) (administrativeReduce b) bi
  | .forallE n t b bi => .forallE n (administrativeReduce t) (administrativeReduce b) bi
  | .mdata _ b => administrativeReduce b
  | .proj n i b => .proj n i (administrativeReduce b)
  | e => e

partial def valueClosure (env : Environment) (pending : List Name)
    (seen : NameSet := {}) : NameSet :=
  match pending with
  | [] => seen
  | n :: rest =>
    if seen.contains n then valueClosure env rest seen else
    let refs := if (`OAI).isPrefixOf n || (`RHLean).isPrefixOf n || (`_private).isPrefixOf n then
      match env.find? n with
      | none => []
      | some ci => match ci.value? (allowOpaque := true) with
        | none => []
        | some v =>
          let live := if (`OAI.SevenEighths.RHLeanNativeSevenEighthsReplay).isPrefixOf n
            then administrativeReduce v else v
          live.getUsedConstants.toList
      else []
    valueClosure env (refs ++ rest) (seen.insert n)

def required : Array Name := #[
  `OAI.SevenEighths.RHLeanNativeSevenEighthsReplay.native_quantitative_probe_bounds,
  `OAI.SevenEighths.RHLeanNativeSevenEighthsReplay.native_uniform_fixed_source_moments,
  `OAI.SevenEighths.RHLeanNativeSevenEighthsReplay.native_source_moments_all_heights,
  `OAI.SevenEighths.RHLeanNativeSevenEighthsReplay.nns_certified_bands,
  `OAI.SevenEighths.RHLeanNativeSevenEighthsReplay.nns_terminal_certificate,
  `OAI.SevenEighths.RHLeanFiniteSlotGap.enlarged_source_gain_budgets,
  `OAI.SevenEighths.ProbeFinalAssembly.SourceData.tiltedProbe_low,
  `OAI.SevenEighths.InverseReflectedPhase.low_original_completed_energy_tilted,
  `OAI.SevenEighths.ProbeFinalAssembly.fixed_tilted_high_bound_near_endpoint,
  `OAI.SevenEighths.ProbeFinalAssembly.actual_high_probe_from_raw_moments_tilted_near_endpoint,
  `OAI.SevenEighths.ProbeHighRowFamily.actual_nonfloor_probe_transport_tilted_near_endpoint,
  `OAI.SevenEighths.ProbeHighRowFamily.small_physical_dyads_sum_near_endpoint,
  `OAI.SevenEighths.HeckeSignal.nonzero_of_probe_bounds_variable_boundary
]

def forbidden : Array Name := #[
  `OAI.SevenEighths.RHLeanNativeSevenEighthsReplay.native_beta_lt_seven_eighths,
  `OAI.SevenEighths.RHLeanNativeSevenEighthsReplay.native_uniform_positive_gap,
  `OAI.SevenEighths.ProbeFinalAssembly.fixed_tilted_high_bound
]

def checkType (terminal : Name) (src : String) : CoreM Unit := do
  let check : Elab.Term.TermElabM Unit := do
    let stx ← match Parser.runParserCategory (← getEnv) `term src with
      | .ok s => pure s
      | .error e => throwError "Expected endpoint type failed to parse: {e}"
    let expected ← Elab.Term.elabTermAndSynthesize stx (some (mkSort .zero))
    let info ← getConstInfo terminal
    unless ← Meta.isDefEq info.type expected do
      throwError "Wrong endpoint type: {info.type}"
  (check.run' { errToSorry := false }).run'

end QuantitativeTiltAudit

open QuantitativeTiltAudit in
def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let env ← importModules #[{module := Name.mkSimple "research.oai_434.VF919QuantitativeTilt"}]
    Options.empty 1024 (loadExts := true)
  let endpoints : Array (String × String) := #[
    ("OAI.SevenEighths.RHLeanNativeSevenEighthsReplay.native_quantitative_source_gap",
      "∃ D : _root_.OAI.SevenEighths.Parameters.HighData (1 / 1000000 : _root_.Real), 0 < D.e / 2 ∧ _root_.OAI.SevenEighths.HeckeZeroSupremum.beta ≤ 7 / 8 - D.e / 2"),
    ("RHLean.Analysis.native_mertens_quantitative_source_gap",
      "∃ D : _root_.OAI.SevenEighths.Parameters.HighData (1 / 1000000 : _root_.Real), 0 < D.e / 2 ∧ _root_.RHLean.Analysis.MertensExponent.MertensGrowthAtMost (7 / 8 - D.e / 2)")
  ]
  for (name, expected) in endpoints do
    let terminal := dottedName name
    (checkType terminal expected).toIO'
      {fileName := "<endpoint>", fileMap := default} {env := env}
    let axioms ← (Lean.collectAxioms terminal : CoreM (Array Name)).toIO'
      {fileName := "<axioms>", fileMap := default} {env := env}
    for a in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains a do
        throw (IO.userError s!"Nonstandard axiom: {a}")
    let closure := valueClosure env [terminal]
    for r in required do
      unless closure.contains r do
        throw (IO.userError s!"Missing live strengthened dependency: {r}")
    for f in forbidden do
      if closure.contains f then
        throw (IO.userError s!"Old endpoint shortcut used: {f}")
    IO.println s!"PASS exact source-relative endpoint: {terminal}"
    IO.println s!"Axioms: {axioms}; live declarations: {closure.size}"
    for r in required do IO.println s!"Required: {r}"
  return 0
