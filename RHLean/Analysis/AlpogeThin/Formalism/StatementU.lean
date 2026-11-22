import RHLean.Analysis.AlpogeThin.Formalism.StatementOC

/-!
# Reconstructed same-host thin-source dependency

Mathematical source: Levent Alpöge (with Claude).
Source: src/Formalism/StatementU.lean.
Pinned source: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/StatementU.lean

This local proof reconstruction adapts the module/namespace boundary to native
RH_Lean. No upstream compiled artifact or terminal RH theorem is imported.
The source archive/mirror states no license; this notice preserves attribution
without assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace RHLean.Analysis.AlpogeThin

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Formalism

def Gzbar (x : ℝ) : ℝ := ∫ u in (1 : ℝ)..2, u * Gz (x / u)

def wavg {m : ℕ} (xs ω : Fin m → ℝ) (x : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∑ j, ω j * (x / xs j) * f (xs j)

def ZetaLandau : Prop :=
  ∀ s₀ : ℝ, (s₀ = 1 ∨ s₀ = -1) → ∀ θ : ℝ, 0 < θ → θ < 1 →
  (∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → s₀ * Gz x ≤ C * x ^ θ) →
  ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0

def ZetaLandauBar : Prop :=
  ∀ s₀ : ℝ, (s₀ = 1 ∨ s₀ = -1) → ∀ θ : ℝ, 0 < θ → θ < 1 →
  (∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → s₀ * Gzbar x ≤ C * x ^ θ) →
  ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0

def ZetaLandauEps : Prop :=
  ∀ s₀ : ℝ, (s₀ = 1 ∨ s₀ = -1) → ∀ θ : ℝ, 0 ≤ θ → θ < 1 →
  (∀ ε : ℝ, 0 < ε → ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → s₀ * Gz x ≤ C * x ^ (θ + ε)) →
  ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0

def ZetaLandauBarEps : Prop :=
  ∀ s₀ : ℝ, (s₀ = 1 ∨ s₀ = -1) → ∀ θ : ℝ, 0 ≤ θ → θ < 1 →
  (∀ ε : ℝ, 0 < ε → ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → s₀ * Gzbar x ≤ C * x ^ (θ + ε)) →
  ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0

def GzLipschitz : Prop :=
  ∃ K : ℝ, ∀ t t' : ℝ, 1 / 2 ≤ t → 1 / 2 ≤ t' → |Gz t| ≤ K * t ∧ |Gz t - Gz t'| ≤ K * |t - t'|

def SampleAverageApprox : Prop :=
  ∃ K : ℝ, ∀ (m : ℕ) (xs ω : Fin m → ℝ) (x η : ℝ), 1 ≤ x → (∀ j, 0 ≤ ω j) → ∑ j, ω j = 1 →
    (∀ j, x / 2 ≤ xs j ∧ xs j ≤ x) → (∀ j, |xs j / x - 1| ≤ η) →
    |wavg xs ω x Gz - Gz x| ≤ K * η * x

def RiemannSumApprox : Prop :=
  ∃ K : ℝ, ∀ (m : ℕ) (x : ℝ), 0 < m → 1 ≤ x →
    |wavg (fun j : Fin m => x / (1 + ((j : ℕ) + 1 : ℝ) / m)) (fun _ => (1 : ℝ) / m) x Gz - Gzbar x|
      ≤ K * x / m

end Formalism

end RHLean.Analysis.AlpogeThin
