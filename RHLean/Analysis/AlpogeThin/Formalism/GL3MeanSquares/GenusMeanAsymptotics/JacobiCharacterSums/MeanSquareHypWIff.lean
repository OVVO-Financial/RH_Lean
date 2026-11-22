import Mathlib
import RHLean.Analysis.AlpogeThin.Formalism.GL3MeanSquares.SecondEstimateOfIntervalHypothesis
import RHLean.Analysis.AlpogeThin.Formalism.GL3MeanSquares.PrimePairOfBoxAndWeakMeanSquareHypotheses

/-!
# Reconstructed same-host thin-source dependency

Mathematical source: Levent Alpöge (with Claude).
Source: src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MeanSquareHypWIff.lean.
Pinned source: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MeanSquareHypWIff.lean

This local proof reconstruction adapts the module/namespace boundary to native
RH_Lean. No upstream compiled artifact or terminal RH theorem is imported.
The source archive/mirror states no license; this notice preserves attribution
without assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace RHLean.Analysis.AlpogeThin

open Finset Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

open Formalism.HermitianLattices.ZeroFreeRegionGL2

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

def liX (X : ℝ) : ℝ := ∫ t in (2 : ℝ)..X, 1 / Real.log t

def piAP (X : ℝ) (M b : ℕ) : ℕ :=
  ((Icc 1 ⌊X⌋₊).filter (fun p => p.Prime ∧ p % M = b % M)).card

def IsExcPair {M : ℕ} [NeZero M] (χ₁ : DirichletCharacter ℂ M) (β₁ : ℝ) : Prop :=
  χ₁ ^ 2 = 1 ∧ χ₁ ≠ 1 ∧ DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0 ∧
    1 - 1 / (8 * Real.log M) < β₁ ∧ β₁ < 1

def mainAP {M : ℕ} (e : Option (DirichletCharacter ℂ M × ℝ)) (b : ℕ) (X : ℝ) : ℝ :=
  match e with
  | none => liX X / (M.totient : ℝ)
  | some (χ₁, β₁) => (liX X - (χ₁ (b : ZMod M)).re * liX (X ^ β₁)) / (M.totient : ℝ)

def PNTAPRelW : Prop :=
  ∃ c₃ A₀ C₀ : ℝ, 0 < c₃ ∧ ∀ (M : ℕ) [NeZero M], 8 ∣ M →
    ∃ e : Option (DirichletCharacter ℂ M × ℝ),
      (∀ p : DirichletCharacter ℂ M × ℝ, e = some p → IsExcPair p.1 p.2) ∧
      (e = none → ∀ (χ₁ : DirichletCharacter ℂ M) (β₁ : ℝ), ¬ IsExcPair χ₁ β₁) ∧
      ∀ (X : ℝ) (b : ℕ), 2 ≤ X → C₀ * Real.log M * Real.log (Real.log M + 2) ≤ Real.log X → b.Coprime M →
        |(piAP X M b : ℝ) - mainAP e b X| ≤
          A₀ * (Real.exp (-(c₃ * Real.log X / Real.log M)) + Real.exp (-Real.sqrt (c₃ * Real.log X))) *
            mainAP e b X

def soutPart (m₀ N : ℕ) : ℕ :=
  ∏ p ∈ N.primeFactors.filter (fun p => Odd (N.factorization p) ∧ ¬ p ∣ m₀), p

def sP (c : ℕ → ℝ) (N p : ℕ) : ℝ :=
  ∑ n ∈ (Icc 1 N).filter (fun n => IsPrimePow n ∧ n.minFac = p), c n

def RR (c : ℕ → ℝ) (m₀ N : ℕ) : ℝ :=
  ∑ n ∈ (Icc 1 N).filter (fun n => IsPrimePow n ∧ (Even (n.factorization n.minFac) ∨ n.minFac ∣ m₀)), c n

end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

end RHLean.Analysis.AlpogeThin
