import RHLean.Analysis.AlpogeThin.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeSetTwoBounds
import RHLean.Analysis.AlpogeThin.Formalism.GL3MeanSquares.HookFormulaTorsion.TwistIsPrimitiveCharacter
import RHLean.Analysis.AlpogeThin.Formalism.GL3MeanSquares.HookFormulaTorsion.WeightedVonMangoldtSumIdentity

/-!
# Reconstructed same-host thin-source dependency

Mathematical source: Levent Alpöge (with Claude).
Source: src/Development/AutomorphicArithmetic/MeanSquareBounds/TwistPrim.lean.
Pinned source: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/MeanSquareBounds/TwistPrim.lean

This local proof reconstruction adapts the module/namespace boundary to native
RH_Lean. No upstream compiled artifact or terminal RH theorem is imported.
The source archive/mirror states no license; this notice preserves attribution
without assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace RHLean.Analysis.AlpogeThin

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

theorem twist_prim :
    ∀ (f q : ℕ) [NeZero f] (ξ : DirichletCharacter ℂ f), ξ.IsPrimitive → q.Prime → q ≠ 2 → ¬ q ∣ f →
      ∃ ψ : DirichletCharacter ℂ (f * q), ψ.IsPrimitive ∧ ψ ≠ 1 ∧ ∀ n : ℕ, ψ (n : ZMod (f * q)) = ξ (n : ZMod f) * J q n := by
  intro f q _ ξ hξ hq hq2 hqf
  have : Fact q.Prime := ⟨hq⟩
  have hcop : q.Coprime f := (Nat.Prime.coprime_iff_not_dvd hq).mpr hqf
  obtain ⟨hp, hne, -⟩ := Formalism.HermitianLattices.ThinSetIntegral.twist_is_primitive_character.2 f ξ q hξ hq2 hcop
  refine ⟨tw ξ q, hp, hne, fun n => ?_⟩
  rw [Formalism.HermitianLattices.ZeroFreeRegionGL2.twist_evaluation_formula f ξ q n]
  rfl

end QH

end RHLean.Analysis.AlpogeThin
