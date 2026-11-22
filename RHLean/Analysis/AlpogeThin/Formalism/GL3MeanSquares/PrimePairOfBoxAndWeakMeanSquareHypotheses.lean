import Mathlib
import RHLean.Analysis.AlpogeThin.Formalism.GL3MeanSquares.SecondEstimateOfIntervalHypothesis

/-!
# Reconstructed same-host thin-source dependency

Mathematical source: Levent Alpöge (with Claude).
Source: src/Formalism/GL3MeanSquares/PrimePairOfBoxAndWeakMeanSquareHypotheses.lean.
Pinned source: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/GL3MeanSquares/PrimePairOfBoxAndWeakMeanSquareHypotheses.lean

This local proof reconstruction adapts the module/namespace boundary to native
RH_Lean. No upstream compiled artifact or terminal RH theorem is imported.
The source archive/mirror states no license; this notice preserves attribution
without assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace RHLean.Analysis.AlpogeThin

open Finset ArithmeticFunction Classical
open Formalism.HermitianLattices.ZeroFreeRegionGL2

noncomputable section

namespace Formalism.HermitianLattices.WeakMeanSquareEstimates

def MeanSquareHypW (ε C x₀ : ℝ) : Prop :=
  ∀ (x X : ℝ) (m₀ a₀ : ℕ) (κ : ℕ → ℂ), x₀ ≤ x → 8 ∣ m₀ →
    (∀ p : ℕ, p.Prime → p ∣ m₀ → (p : ℝ) ≤ x ^ (ε / 5) ∨ x ^ 400 < (p : ℝ)) → a₀.Coprime m₀ → a₀ % 4 = 3 →
    (1 / 4) * Real.log x ^ 2 * Real.log m₀ ≤ Real.log X → x ^ (ε / 6) ≤ Real.log X →
    Real.log X ≤ x ^ (ε / 5) * Real.log x ^ 2 →
    (∀ n, ‖κ n‖ ≤ 1) → (∀ a b, κ (a * b) = κ a * κ b) →
    X ^ (9 / 10 : ℝ) ≤ ((PPset m₀ a₀ X).card : ℝ) ∧
    (∑ q ∈ PPset m₀ a₀ X,
        ‖∑ n ∈ Icc 1 ⌊x ^ 400⌋₊, ((cN x n : ℝ) : ℂ) * κ n * ((jacobiSym (n : ℤ) q : ℤ) : ℂ)‖ ^ 2) ≤
      C * x * Real.log x * ((PPset m₀ a₀ X).card : ℝ)

def MeanSquareWeaken : Prop :=
  ∀ ε C x₀ : ℝ, MeanSquareHyp ε C x₀ → MeanSquareHypW ε C x₀

def PrimePairOfBoxAndWeakMeanSquareHypotheses : Prop :=
  ∀ ε C₂ C₂' x₂ C₄ x₄ : ℝ, 0 < ε → ε ≤ 1 → 0 < C₂ → 0 < C₄ →
    BoxCountHyp C₂ → BoxTailHyp ε C₂' x₂ → MeanSquareHypW ε C₄ x₄ →
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ExistsSplitGoodPrimePair ε C₂' x

end Formalism.HermitianLattices.WeakMeanSquareEstimates

end RHLean.Analysis.AlpogeThin
