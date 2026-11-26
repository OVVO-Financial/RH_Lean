import RHLean.Geometry.NativeThetaCuspFourierTransform
import RHLean.Geometry.NativeThetaCuspParabolic
import RHLean.Geometry.NativeThetaCuspTransformationComposition
import RHLean.Geometry.NativeThetaCuspSymplecticGeneration

/-!
# The actual rational Weil operators from Fourier and Poisson summation

Every rational symplectic matrix has a Schwartz–Bruhat operator satisfying
the theta transformation law and preserving the original finite Haar inner
product. The proof composes the explicit parabolic operator with the Fourier
operator whose theta law was proved by Gaussian Poisson summation. Neither
the standard-J law nor a multiplier character is an input assumption.

Source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsWeilOfSymplectic.lean.
The source mirror states no license; attribution is retained.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open Matrix Complex
open scoped ComplexConjugate Real

namespace RHLean.Geometry.NativeTheta.Cusp

theorem exists_weil_mul {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι]
    {σ σ' : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ}
    (hσ : σ ∈ Matrix.symplecticGroup ι ℚ) (hσ' : σ' ∈ Matrix.symplecticGroup ι ℚ)
    (h : ∃ ω : (Matrix κ ι ℚ → ℂ) → (Matrix κ ι ℚ → ℂ), ∀ φ, IsSB φ →
      IsSB (ω φ) ∧ TransS σ φ (ω φ) ∧
        ∀ φ', IsSB φ' → ip (ω φ) (ω φ') = ip φ φ')
    (h' : ∃ ω : (Matrix κ ι ℚ → ℂ) → (Matrix κ ι ℚ → ℂ), ∀ φ, IsSB φ →
      IsSB (ω φ) ∧ TransS σ' φ (ω φ) ∧
        ∀ φ', IsSB φ' → ip (ω φ) (ω φ') = ip φ φ') :
    ∃ ω : (Matrix κ ι ℚ → ℂ) → (Matrix κ ι ℚ → ℂ), ∀ φ, IsSB φ →
      IsSB (ω φ) ∧ TransS (σ * σ') φ (ω φ) ∧
        ∀ φ', IsSB φ' → ip (ω φ) (ω φ') = ip φ φ' := by
  obtain ⟨ω, hω⟩ := h
  obtain ⟨ω', hω'⟩ := h'
  refine ⟨fun φ => ω (ω' φ), fun φ hφ => ?_⟩
  obtain ⟨hs', ht', hi'⟩ := hω' φ hφ
  obtain ⟨hs, ht, hi⟩ := hω (ω' φ) hs'
  refine ⟨hs, transS_comp κ ι σ' σ hσ' hσ φ (ω' φ) (ω (ω' φ)) ht' ht,
    fun φ' hφ' => ?_⟩
  rw [hi _ (hω' φ' hφ').1, hi' φ' hφ']

/-- Rational symplectic covariance and exact Haar unitarity, obtained from
the proved Fourier, Poisson, parabolic and composition laws. -/
theorem exists_weil_of_symplectic (κ ι : Type) [Fintype κ] [Fintype ι]
    [DecidableEq ι] (σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ)
    (hκ : Even (Fintype.card κ)) (hσ : σ ∈ Matrix.symplecticGroup ι ℚ) :
    ∃ ω : (Matrix κ ι ℚ → ℂ) → (Matrix κ ι ℚ → ℂ), ∀ φ, IsSB φ →
      IsSB (ω φ) ∧ TransS σ φ (ω φ) ∧
        ∀ φ', IsSB φ' → ip (ω φ) (ω φ') = ip φ φ' := by
  obtain ⟨p₁, h₁, p₂, h₂, p₃, h₃, l₁, l₂, l₃, rfl⟩ :=
    symplectic_eq_parabolic_J_parabolic_J_parabolic ι σ hσ
  have hJ : Matrix.J ι ℚ ∈ Matrix.symplecticGroup ι ℚ := SymplecticGroup.J_mem ι ℚ
  have w₁ := Parab.trans_parabolic κ ι p₁ hκ h₁ l₁
  have w₂ := Parab.trans_parabolic κ ι p₂ hκ h₂ l₂
  have w₃ := Parab.trans_parabolic κ ι p₃ hκ h₃ l₃
  have wJ := FourierJ.exists_trans_J κ ι hκ
  have a₁ := mul_mem h₁ hJ
  have a₂ := mul_mem a₁ h₂
  have a₃ := mul_mem a₂ hJ
  exact exists_weil_mul a₃ h₃
    (exists_weil_mul a₂ hJ (exists_weil_mul a₁ h₂ (exists_weil_mul h₁ hJ w₁ wJ) w₂) wJ) w₃

end RHLean.Geometry.NativeTheta.Cusp
