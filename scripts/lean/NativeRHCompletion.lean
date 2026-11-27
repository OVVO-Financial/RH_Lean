import RHLean
import Lean.Util.CollectAxioms

/-! Terminal verification for #1214. Import only the production library.
The two definitional checks keep the original arithmetic and binder order
independent of the implementation of the candidate. -/
open Lean Elab Command Meta RHLean.Analysis.AlpogeNativeBoundHandoff
open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace NativeRHCompletionAudit

example : RiemannHypothesis = (∀ (s : ℂ), riemannZeta s = 0 →
    (¬∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 → s.re = 1 / 2) := rfl

example (y : ℝ) : statementOCGz y =
    (∑ n ∈ Finset.Icc 1 ⌊y⌋₊, Λ n * (y / (n : ℝ) - 1)) -
      y * Real.log y + (1 + Real.eulerMascheroniConstant) * y := rfl

example (K ε₁ : ℝ) : SmallEpsilonWindowBound K ε₁ =
    (∀ ε : ℝ, 0 < ε → ε < ε₁ → ∃ C : ℝ, ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧
      ∀ y ∈ Set.Icc Y (Y ^ ((3 : ℝ) / 2)), statementOCGz y ≤ C * y ^ (1 / 2 + K * ε)) := rfl

private def WindowClaim : Prop := ∃ K ε₁ : ℝ, 0 < ε₁ ∧ SmallEpsilonWindowBound K ε₁
private def PositiveWindowClaim : Prop :=
  ∃ K ε₁ : ℝ, 0 < K ∧ 0 < ε₁ ∧ SmallEpsilonWindowBound K ε₁

private theorem fromWindow (h : WindowClaim) : RiemannHypothesis := by
  obtain ⟨_, _, he, bound⟩ := h
  exact riemannHypothesis_of_smallEpsilonWindowBound he bound

private theorem fromPositiveWindow (h : PositiveWindowClaim) : RiemannHypothesis := by
  obtain ⟨_, _, _, he, bound⟩ := h
  exact riemannHypothesis_of_smallEpsilonWindowBound he bound

private def moduleOf (env : Environment) (n : Name) : Option Name := do
  let i ← env.getModuleIdxFor? n
  env.header.moduleNames[i.toNat]?

private def nativeModule (m : Name) : Bool := `RHLean == m || Name.isPrefixOf `RHLean m

private def additionalRefs : ConstantInfo → List Name
  | .inductInfo v => v.all ++ v.ctors
  | .ctorInfo v => [v.induct]
  | .recInfo v => v.all ++ v.rules.flatMap fun r => r.ctor :: r.rhs.getUsedConstants.toList
  | _ => []

private def valueRefs (c : ConstantInfo) : Array Name :=
  (c.value? (allowOpaque := true)).map Expr.getUsedConstants |>.getD #[]

private partial def kernelClosure (env : Environment) (todo : List Name) (seen : NameSet := {}) :
    Except String NameSet := do
  match todo with
  | [] => return seen
  | n :: rest =>
    if seen.contains n then return ← kernelClosure env rest seen
    let some c := env.checked.get.find? n | throw s!"missing kernel declaration {n}"
    let next := c.type.getUsedConstants.toList ++ (valueRefs c).toList ++ additionalRefs c
    kernelClosure env (next ++ rest) (seen.insert n)

private def terminalPredicate (n : Name) : Bool := Id.run do
  let .str _ last := n | return false
  let s := last.toLower.replace "_" ""
  return s.contains "riemannhypothesis" || s == "grh" || s == "generalizedrh" || s == "generalisedrh"

private def returnsEndpoint (env : Environment) (c : ConstantInfo) : MetaM Bool := do
  let body := c.type.getForallBody
  if let some n := body.getAppFn.constName? then
    if terminalPredicate n then return true
    -- Catch reducible endpoint aliases, including aliases with unrelated names.
    if let some (.defnInfo _) := env.find? n then
      if !body.hasLooseBVars then
        return ← withNewMCtxDepth <| isDefEq body (mkConst `RiemannHypothesis)
  return false

private def audit (env : Environment) : CommandElabM Unit := do
  let root := `native_riemannHypothesis
  let handoff := `RHLean.Analysis.AlpogeNativeBoundHandoff.riemannHypothesis_of_smallEpsilonWindowBound
  unless moduleOf env `RiemannHypothesis == some `Mathlib.NumberTheory.LSeries.RiemannZeta do
    throwError "unexpected provenance for Mathlib RiemannHypothesis"
  let some (.thmInfo thm) := env.checked.get.find? root |
    throwError "NATIVE_RH_MISSING: production theorem native_riemannHypothesis is absent"
  unless thm.type == mkConst `RiemannHypothesis && thm.levelParams.isEmpty do
    throwError "NATIVE_RH_TYPE: expected exactly the closed, literal Mathlib RiemannHypothesis"
  let some rootModule := moduleOf env root | throwError "terminal theorem has no imported module"
  unless nativeModule rootModule do throwError "terminal theorem comes from {rootModule}"
  let .ok names := kernelClosure env [root] | throwError "incomplete terminal kernel closure"
  let .ok proofNames := kernelClosure env thm.value.getUsedConstants.toList |
    throwError "incomplete terminal proof body"
  unless proofNames.contains handoff do throwError "terminal proof does not use the #1205 handoff"
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let axs ← liftCoreM (Lean.collectAxioms root)
  for a in axs do
    unless allowed.contains a do throwError "unauthorized axiom {a}"
  let mut windows : Array Name := #[]
  let mut endpoints : Array Name := #[]
  let out ← IO.FS.Handle.mk "native-rh-cone.jsonl" .write
  for n in names.toArray.qsort Name.lt do
    let some c := env.checked.get.find? n | throwError "missing kernel declaration {n}"
    let some m := moduleOf env n | throwError "missing module provenance for {n}"
    let s := n.toString.toLower.replace "_" ""
    if s.contains "anygeometry" || s.contains "geocl" || c.isUnsafe then
      throwError "forbidden supplier {n} in {m}"
    if let .axiomInfo _ := c then
      unless allowed.contains n do throwError "unauthorized kernel axiom {n}"
    let isProof := match c with
      | .thmInfo _ | .opaqueInfo _ | .defnInfo _ | .axiomInfo _ => true
      | _ => false
    if isProof && (← liftTermElabM <| returnsEndpoint env c) then
      endpoints := endpoints.push n
      unless nativeModule m do throwError "imported terminal RH/GRH supplier {n} in {m}"
      if n != root && c.type == mkConst `RiemannHypothesis then
        throwError "closed terminal theorem used to prove {root}: {n}"
    if nativeModule m && proofNames.contains n && c.levelParams.isEmpty && !c.type.isForall then
      if let .thmInfo _ := c then
        let isWindow ← liftTermElabM <| withNewMCtxDepth do
          if ← isDefEq c.type (mkConst ``WindowClaim) then return true
          isDefEq c.type (mkConst ``PositiveWindowClaim)
        if isWindow then windows := windows.push n
    out.putStrLn (Json.compress (Json.mkObj [("name", toJson n.toString), ("module", toJson m.toString),
      ("typeRefs", toJson (c.type.getUsedConstants.map Name.toString)),
      ("valueRefs", toJson ((valueRefs c).map Name.toString)),
      ("kernelRefs", toJson ((additionalRefs c).map Name.toString))]))
  out.flush
  if windows.isEmpty then throwError "missing closed native window supplier in the terminal proof"
  for w in windows do
    let .ok sources := kernelClosure env [w] | throwError "incomplete native window closure"
    for n in endpoints do
      if sources.contains n then throwError "window supplier {w} depends on terminal result {n}"
  -- Kernel-check a second derivation using only the independently located
  -- closed quantitative supplier and the original production consumer.
  let w := windows[0]!
  let some wc := env.checked.get.find? w | throwError "window theorem disappeared"
  let plain ← liftTermElabM <| withNewMCtxDepth <| isDefEq wc.type (mkConst ``WindowClaim)
  let replay := mkApp (mkConst (if plain then ``fromWindow else ``fromPositiveWindow)) (mkConst w)
  liftCoreM <| addDecl (.thmDecl { name := `NativeRHCompletionAudit.replayedHandoff,
    levelParams := [], type := mkConst `RiemannHypothesis, value := replay })
  IO.FS.writeFile "native-rh-module.txt" (rootModule.toString ++ "\n")
  logInfo m!"NATIVE_RH_KERNEL_PASS root={root} module={rootModule} window={windows} axioms={axs} declarations={names.size}"

run_cmd audit (← getEnv)

end NativeRHCompletionAudit
