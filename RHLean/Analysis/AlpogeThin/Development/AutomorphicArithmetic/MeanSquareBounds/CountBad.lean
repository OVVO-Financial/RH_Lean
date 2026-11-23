import RHLean.Analysis.AlpogeThin.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeSetTwoBounds
import RHLean.Analysis.AlpogeThin.Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZAll
import RHLean.Analysis.AlpogeThin.Development.AutomorphicArithmetic.MeanSquareBounds.CountBadCore

/-!
# Reconstructed same-host thin-source dependency

Mathematical source: Levent Alpöge (with Claude).
Source: src/Development/AutomorphicArithmetic/MeanSquareBounds/CountBad.lean.
Pinned source: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/MeanSquareBounds/CountBad.lean

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

theorem count_bad :
    ∃ C : ℝ, ∀ (Q F : ℝ) (B : Finset ℕ), 3 ≤ Q →
      (∀ q ∈ B, q.Prime ∧ F < q ∧ ∃ (f : ℕ) (_ : NeZero (f * q)) (ψ : DirichletCharacter ℂ (f * q)),
        (f : ℝ) ≤ F ∧ ((f * q : ℕ) : ℝ) ≤ Q ∧ ψ.IsPrimitive ∧ ¬ ZeroFreeBox Q ψ) → (B.card : ℝ) ≤ C * Q ^ (1 / 4 : ℝ) := by
  obtain ⟨C, -, hC⟩ := count_bad_core
  refine ⟨C, fun Q F B hQ hB => hC Q F B hQ fun q hq => ?_⟩
  obtain ⟨hp, hF, f, hne, ψ, hf, hN, hψ, hz⟩ := hB q hq
  exact ⟨hp, hF, f * q, f, hne, ψ, rfl, hf, hψ, hN, hz⟩

end QH

end RHLean.Analysis.AlpogeThin
