import RHLean.Analysis.AlpogeThin.Formalism.ZetaNonvanishingGeneralWeights

/-!
# Reconstructed same-host thin-source dependency

Mathematical source: Levent Alpöge (with Claude).
Source: src/Formalism/ZetaNonvanishingChebyshevWeights.lean.
Pinned source: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/ZetaNonvanishingChebyshevWeights.lean

This local proof reconstruction adapts the module/namespace boundary to native
RH_Lean. No upstream compiled artifact or terminal RH theorem is imported.
The source archive/mirror states no license; this notice preserves attribution
without assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace RHLean.Analysis.AlpogeThin

open Complex Set Real

noncomputable section

namespace Formalism

def chebNode (m : ℕ) (j : Fin m) : ℝ := Real.sin ((2 * ((j : ℕ) + 1 : ℝ) - 1) * π / (4 * m)) ^ 2

def chebyshevWeightedAverage (m : ℕ) (x : ℝ) (f : ℝ → ℝ) : ℝ :=
  wavg (fun j : Fin m => x / chebNode m j) (fun _ => (1 : ℝ) / m) x f

def Gcheb (x : ℝ) : ℝ := (1 / π) * ∫ φ in (0 : ℝ)..π, Real.sin (φ / 2) ^ 2 * Gz (x / Real.sin (φ / 2) ^ 2)

def ZetaLandauCheb : Prop :=
  ∀ s₀ : ℝ, (s₀ = 1 ∨ s₀ = -1) → ∀ θ : ℝ, 0 < θ → θ < 1 →
  (∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → s₀ * Gcheb x ≤ C * x ^ θ) →
  ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0

def ZetaLandauChebEps : Prop :=
  ∀ s₀ : ℝ, (s₀ = 1 ∨ s₀ = -1) → ∀ θ : ℝ, 0 ≤ θ → θ < 1 →
  (∀ ε : ℝ, 0 < ε → ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → s₀ * Gcheb x ≤ C * x ^ (θ + ε)) →
  ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0

def ChebyshevWeightApproximation : Prop :=
  ∃ K : ℝ, ∀ (m : ℕ) (x : ℝ), 0 < m → 1 ≤ x →
    |chebyshevWeightedAverage m x Gz - Gcheb x| ≤ K * x * (1 + Real.log m) / m

def ZetaNonvanishingChebyshevWeights : Prop :=
  ∀ s₀ : ℝ, (s₀ = 1 ∨ s₀ = -1) → ∀ θ : ℝ, 0 ≤ θ → θ < 1 →
  (∀ ε : ℝ, 0 < ε → ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∃ m : ℕ, 0 < m ∧ x ^ (1 - θ - ε) ≤ m ∧ s₀ * chebyshevWeightedAverage m x Gz ≤ C * x ^ (θ + ε)) →
  ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0

end Formalism

end

end RHLean.Analysis.AlpogeThin
