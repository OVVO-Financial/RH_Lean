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

private theorem positiveWindow (h : WindowClaim) : PositiveWindowClaim := by
  obtain ⟨K, ε₁, he, bound⟩ := h
  refine ⟨max K 1, ε₁, zero_lt_one.trans_le (le_max_right _ _), he, ?_⟩
  intro ε hε he₁
  obtain ⟨C, hc⟩ := bound ε hε he₁
  refine ⟨|C|, fun Y₀ => ?_⟩
  obtain ⟨Y, hY, hw⟩ := hc (max Y₀ 1)
  refine ⟨Y, (le_max_left _ _).trans hY, ?_⟩
  intro y hy
  have hy₁ : 1 ≤ y := (le_max_right _ _).trans (hY.trans hy.1)
  exact (hw y hy).trans (mul_le_mul (le_abs_self C)
    (Real.rpow_le_rpow_of_exponent_le hy₁ (add_le_add le_rfl
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hε.le)))
    (Real.rpow_nonneg (zero_le_one.trans hy₁) _) (abs_nonneg C))

private theorem fromPositiveWindow (h : PositiveWindowClaim) : RiemannHypothesis := by
  obtain ⟨_, _, _, he, bound⟩ := h
  exact riemannHypothesis_of_smallEpsilonWindowBound he bound

private theorem fromWindow (h : WindowClaim) : RiemannHypothesis :=
  fromPositiveWindow (positiveWindow h)

-- Predicate signatures from the pinned compact Statements.lean. Comparing
-- the types also catches an imported terminal proof with a different name.
private def Nonvanishing : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

private def ZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

private def PrimitiveZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ s : ℂ, 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

private def endpointType (t : Expr) : MetaM Bool := do
  if !(← isProp t) then return false
  for target in #[`RiemannHypothesis, ``Nonvanishing, ``ZerosOnLine, ``PrimitiveZerosOnLine] do
    if ← withNewMCtxDepth <| isDefEq t (mkConst target) then return true
  return false

private partial def expandedEndpoint (t : Expr) : MetaM Bool := do
  if ← endpointType t then return true
  if let .forallE n dom body bi := t then
    return ← withLocalDecl n bi dom fun x => expandedEndpoint (body.instantiate1 x)
  return false

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
  let refs := c.type.getUsedConstants
  if refs.contains `riemannZeta || refs.contains `DirichletCharacter.LFunction then
    return ← expandedEndpoint c.type
  if let some n := body.getAppFn.constName? then
    if let some (.defnInfo _) := env.find? n then
      return ← forallTelescope c.type fun _ residual => endpointType residual
  return false

-- Check what the production root imported, including unused declarations.
-- In the dependency cone below we also reject conditional external endings.
private def checkImportedTerminals (env : Environment) : CommandElabM Unit := do
  let compact := #[`New.grh, `riemannHypothesis, `riemannZeta_eq_zero_re,
    `LFunction_ne_zero_of_half_lt_re, `LFunction_eq_zero_re, `LFunction_eq_zero_re_of_isPrimitive]
  let mut checked := 0
  for i in [:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    if nativeModule m then continue
    for n in env.header.moduleData[i]!.constNames do
      let some c := env.checked.get.find? n | continue
      checked := checked + 1
      if compact.contains n || c.type.isConstOf `RiemannHypothesis then
        throwError "production imports terminal declaration {n} from {m}"
      let candidate := match c.type.getAppFn.constName? with
        | some name => match env.find? name with
          | some (.defnInfo pred) => pred.type.getForallBody == mkSort .zero
          | _ => false
        | none =>
          let refs := c.type.getUsedConstants
          refs.contains `riemannZeta || refs.contains `DirichletCharacter.LFunction
      if candidate then
        if ← liftTermElabM <| endpointType c.type then
          throwError "production imports an equivalent terminal declaration {n} from {m}"
  logInfo m!"Checked {checked} imported kernel declarations for external terminal proofs"

private def audit (env : Environment) : CommandElabM Unit := do
  let root := `native_riemannHypothesis
  let handoff := `RHLean.Analysis.AlpogeNativeBoundHandoff.riemannHypothesis_of_smallEpsilonWindowBound
  unless moduleOf env `RiemannHypothesis == some `Mathlib.NumberTheory.LSeries.RiemannZeta do
    throwError "unexpected provenance for Mathlib RiemannHypothesis"
  checkImportedTerminals env
  let some consumer := env.checked.get.find? handoff | throwError "missing production #1205 handoff"
  unless consumer.type.isForall && (← liftTermElabM <| returnsEndpoint env consumer) do
    throwError "unexpected #1205 handoff type"
  let handoffCone ← match kernelClosure env [handoff] with
    | .ok ns => pure ns
    | .error err => throwError "incomplete #1205 kernel closure: {err}"
  unless handoffCone.contains `riemannZeta && handoffCone.contains ``statementOCGz do
    throwError "incomplete #1205 arithmetic and zeta provenance"
  logInfo m!"#1205 conditional handoff audit traversed {handoffCone.size} kernel declarations"
  let some candidate := env.checked.get.find? root |
    throwError "NATIVE_RH_MISSING: production theorem native_riemannHypothesis is absent"
  let .thmInfo thm := candidate | throwError "NATIVE_RH_TYPE: expected a theorem declaration"
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
  let checkedProof : TheoremVal := {
    name := `NativeRHCompletionAudit.replayedHandoff
    levelParams := []
    type := mkConst `RiemannHypothesis
    value := replay
  }
  liftCoreM (addDecl (.thmDecl checkedProof))
  IO.FS.writeFile "native-rh-module.txt" (rootModule.toString ++ "\n")
  logInfo m!"NATIVE_RH_KERNEL_PASS root={root} module={rootModule} window={windows} axioms={axs} declarations={names.size}"

set_option maxHeartbeats 0 in
run_cmd audit (← getEnv)

end NativeRHCompletionAudit
