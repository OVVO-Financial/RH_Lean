import RHLean.Geometry.AlpogeAllPlace.Development.AbelianVarietyTheory.Proofs.DivisorProofs.HtMapLeOfPoints

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 4000000

/-! Actual all-place integral-family slope descent, ported from the pinned source.
The joint norm and near rank saturation hypotheses retain their original constants.
Every infinite place and the original O_K submodules remain in the statement. -/

open NumberField RHLean.Geometry.AlpogeAllPlace.GlobalTheory.AllWt

namespace RHLean.Geometry

theorem nativeAllPlaceDescent : ∀ (K V W : Type) [Field K] [NumberField K] [IsTotallyComplex K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (NA : (K →+* ℂ) → V → ℝ) (NB : (K →+* ℂ) → W → ℝ) (A : Submodule (𝓞 K) V) (B : Submodule (𝓞 K) W) (n : ℕ) (φ : Fin n → V →ₗ[K] W) (P Λ ε t : ℝ), HasGram NA → HasGram NB → A.FG → B.FG → A ≠ ⊥ → (∀ h, ∀ f ∈ A, φ h f ∈ B) → (∀ f, (∀ h, φ h f = 0) → f = 0) → (∀ σ f, ∑ h, NB σ (φ h f) ^ 2 ≤ Real.exp (2 * P) * NA σ f ^ 2) → (∃ s : Set W, s ⊆ (B : Set W) ∧ (∀ y ∈ s, ∀ σ, NB σ y ≤ Real.exp Λ) ∧ (B : Set W) ⊆ (Submodule.span K s : Set W)) → 0 ≤ Λ → 0 ≤ ε → (n : ℝ) * RHLean.Geometry.AlpogeAllPlace.Formalism.HN.rkK B ≤ (1 + ε) * RHLean.Geometry.AlpogeAllPlace.Formalism.HN.rkK A → t ≤ slope_sq NA A - 2 * P → t - ε * (|t| + 2 * Λ) ≤ slope_sq NB B :=
  RHLean.Geometry.AlpogeAllPlace.GlobalTheory.DescentFamily.descent

end RHLean.Geometry
