import «research.ALPOGE_VERIFYTASK_CHALLENGE_20261124»
import RHLean.Geometry.NativeCMInverseIdealClassModels
import RHLean.Analysis.AlpogeThin.NativeExistingRecoveryPayment
import Lean.Util.CollectAxioms

/-!
# VerifyTask application: prove the frozen CM statement on native objects

The first Core 6 conjunct already follows from the native lattice
normalization and modular-J integrality proof. This is an independent
statement check with a real proof of that conjunct, not a new geometry
dependency or a claim that Core 6's formal-group conjunct is closed.
The principal-window checks keep all prime powers and quantifier order.
No terminal RH proof or third-party contestant proof is imported.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open UpperHalfPlane NumberField
open RHLean.VerifyTaskChallenge
open RHLean.Geometry.NativeCM.Weierstrass
open RHLean.Analysis.AlpogeThin

namespace RHLean.VerifyTaskNativeAudit

/-- Compare the actual invariant of the original lattice curve against
the independently specified formula, without choosing the curve or its
height to satisfy the comparison. -/
theorem latticeCurve_j_eq_literal (L : PeriodPair) :
    (latticeCurve L).j = cmJ L := by
  rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ',
    latticeCurve_Δ, latticeCurve_c₄, cmJ]
  ring

/-- The first conjunct of VerifyTask Core 6, proved using the existing
native normalized-lattice and modular-integrality results. -/
theorem cmJ_native : cmJStatement := by
  intro d L _ hmod hCM
  let α : ℂ := (1 + Complex.I * ((Real.sqrt (d : ℝ)) : ℂ)) / 2
  change ∀ z ∈ L.lattice, α * z ∈ L.lattice at hCM
  have hd : 0 < d := by omega
  have hα : ∀ m : ℤ, α ≠ (m : ℂ) := by
    intro m hm
    dsimp only [α] at hm
    have hmul := (div_eq_iff (by norm_num : (2 : ℂ) ≠ 0)).mp hm
    have him := congrArg Complex.im hmul
    have hs : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hd)
    norm_num [Complex.add_im, Complex.mul_im] at him
    linarith
  obtain ⟨a, τ, ha, hp⟩ := exists_lattice_eq_mul_tau L
  have hm (z : ℂ) : a * z ∈ L.lattice ↔
      z ∈ Submodule.span ℤ {(τ : ℂ), 1} := by
    rw [hp, Submodule.mem_span_pair]
    simp only [zsmul_eq_mul, mul_one]
    exact exists₂_congr fun m n =>
      ⟨fun h => mul_left_cancel₀ ha h, fun h => congrArg (a * ·) h⟩
  rw [← latticeCurve_j_eq_literal L, latticeCurve_j ha hp]
  apply isIntegral_modularJ_of_mul_mem hα
  intro z hz
  apply (hm _).mp
  rw [mul_left_comm]
  exact hCM _ ((hm z).mpr hz)

/-- On the actual quadratic order-stable periods, use the existing
native class-model supplier directly; no generic CM reconstruction. -/
example {K : Type} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (σ : K →+* ℂ) (L : PeriodPair)
    (hL : ∀ b : 𝓞 K, ∀ z ∈ L.lattice, σ (b : K) * z ∈ L.lattice) :
    IsIntegral ℤ (cmJ L) := by
  rw [← latticeCurve_j_eq_literal L]
  exact latticeCurve_j_integral_of_order_stable hK σ L hL

/-- The actual cyclic principal sum equals the independently specified
Mathlib arithmetic expression, rather than an assigned surrogate. -/
example (x : ℝ) :
    (Formalism.HC.Level.cyc Formalism.HC.PChar.one).Gm x = literalGz x :=
  nativePrincipalCyclicGm_eq_statementOCGz x

/-- Freeze the full hypothesis of the existing handoff. This is an
anonymous type check of the conditional consumer, not an RH endpoint. -/
example (K eps₁ : ℝ) (hε : 0 < eps₁) :
    principalWindow K eps₁ → _root_.RiemannHypothesis :=
  RHLean.Analysis.AlpogeNativeBoundHandoff.riemannHypothesis_of_smallEpsilonWindowBound hε

end RHLean.VerifyTaskNativeAudit

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let roots : Array Name := #[
    ``RHLean.VerifyTaskNativeAudit.latticeCurve_j_eq_literal,
    ``RHLean.VerifyTaskNativeAudit.cmJ_native,
    ``RHLean.Geometry.NativeCM.Weierstrass.latticeCurve_j_integral_of_order_stable,
    ``RHLean.Analysis.AlpogeThin.nativePrincipalCyclicGm_eq_statementOCGz,
    ``RHLean.Analysis.AlpogeThin.nativeSmallEpsilonWindowBound_of_principalCyclic,
    ``RHLean.Analysis.AlpogeNativeBoundHandoff.riemannHypothesis_of_smallEpsilonWindowBound]
  let env ← getEnv
  for root in roots do
    unless env.contains root do
      throwError "Missing audited declaration: {root}"
    let axs ← liftCoreM (Lean.collectAxioms root)
    for ax in axs do
      unless allowed.contains ax do
        throwError "Unapproved axiom for {root}: {ax}"
    logInfo m!"PASS VerifyTask native statement audit {root}: {axs}"
