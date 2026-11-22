import Mathlib

/-!
# Real tensor coordinates from the exact CM half of the embeddings

Source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Formalism/LocalToGlobal/ProjectiveLattices/DatTheta.lean`, through
`phiI_bijective`, and the complete proof of its scalar independence input
`src/Lemmata/GeneralBFactThirdVariant/Imports.lean`, `goal1`.
The source mirror states no license; attribution is retained without assigning one.

These are finite real-linear constructions from the actual embeddings of a
number field and its integral basis. The scalar embedding map is proved
bijective using Mathlib's canonical-embedding basis, conjugate-complement
identity and exact dimension. No real realization, complex structure,
positivity condition or geometric datum is assumed.

The general source `theta` formula is retained. Its native prescribed-lattice
instantiation uses the actual inverse half-different and its proved rank in
`NativePrescribedPolarizationRealization`; it does not import the source's
larger D7 record or a terminal RH consumer.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace RHLean.Geometry.NativePolarizationRealCoordinates

open NumberField TensorProduct
open scoped nonZeroDivisors ComplexConjugate

variable {E : Type} [Field E]

section Scalar

variable (Ψ : Finset (E →+* ℂ))

def embO : 𝓞 E →+ (Ψ → ℂ) where
  toFun e τ := (τ : E →+* ℂ) (e : E)
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

def phi1 : ℝ ⊗[ℤ] 𝓞 E →ₗ[ℝ] (Ψ → ℂ) := LinearMap.liftBaseChange ℝ (embO Ψ).toIntLinearMap

theorem phi1_tmul (x : ℝ) (e : 𝓞 E) :
    phi1 Ψ (x ⊗ₜ e) = fun τ : Ψ => (x : ℂ) * (τ : E →+* ℂ) (e : E) := by
  ext τ
  simp [phi1, LinearMap.liftBaseChange_tmul, embO, Complex.real_smul]

variable {Ψ}

theorem conj_mem_iff (hΨ : ∀ σ : E →+* ℂ, σ ∈ Ψ ↔ ComplexEmbedding.conjugate σ ∉ Ψ)
    (σ : E →+* ℂ) : ComplexEmbedding.conjugate σ ∈ Ψ ↔ σ ∉ Ψ := by
  rw [hΨ]
  simp [ComplexEmbedding.conjugate]

theorem li1 [NumberField E] (hΨ : ∀ σ : E →+* ℂ, σ ∈ Ψ ↔ ComplexEmbedding.conjugate σ ∉ Ψ)
    (x : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → ℝ)
    (hx : ∀ τ ∈ Ψ, ∑ k, (x k : ℂ) * τ ((RingOfIntegers.basis E k : 𝓞 E) : E) = 0) : x = 0 := by
  have hall : ∀ σ : RingHom E Complex, (Finset.univ.sum fun k =>
      (Complex.ofReal (x k)) * σ (NumberField.RingOfIntegers.val
        (NumberField.RingOfIntegers.basis E k))) = 0 := by
    intro σ
    by_cases hσ : σ ∈ Ψ
    · exact hx σ hσ
    · have hc : NumberField.ComplexEmbedding.conjugate σ ∈ Ψ := by
        by_contra hc
        exact hσ ((hΨ σ).mpr hc)
      have h2 := congrArg (starRingEnd Complex) (hx _ hc)
      rw [map_sum, map_zero] at h2
      simpa only [map_mul, Complex.conj_ofReal, NumberField.ComplexEmbedding.conjugate_coe_eq,
        Complex.conj_conj] using h2
  have hli := (NumberField.canonicalEmbedding.latticeBasis E).linearIndependent
  rw [Fintype.linearIndependent_iff] at hli
  funext k
  have h3 := hli (fun k => Complex.ofReal (x k)) (by
    funext σ
    rw [Finset.sum_apply]
    simp only [NumberField.canonicalEmbedding.latticeBasis_apply, Pi.smul_apply,
      NumberField.canonicalEmbedding.apply_at, NumberField.integralBasis_apply, smul_eq_mul,
      Pi.zero_apply]
    exact hall σ) k
  exact_mod_cast h3

theorem two_card [NumberField E] (hΨ : ∀ σ : E →+* ℂ, σ ∈ Ψ ↔ ComplexEmbedding.conjugate σ ∉ Ψ) :
    2 * Ψ.card = Module.finrank ℚ E := by
  classical
  have h1 : Ψᶜ = Ψ.image ComplexEmbedding.conjugate := by
    ext σ
    simp only [Finset.mem_compl, Finset.mem_image]
    constructor
    · intro h
      exact ⟨ComplexEmbedding.conjugate σ, (conj_mem_iff hΨ σ).2 h, by simp [ComplexEmbedding.conjugate]⟩
    · rintro ⟨τ, hτ, rfl⟩
      exact (hΨ τ).1 hτ
  have hinj : Function.Injective (ComplexEmbedding.conjugate : (E →+* ℂ) → (E →+* ℂ)) := by
    intro a c h
    simpa [ComplexEmbedding.conjugate] using congrArg star h
  have h2 : (Ψ.image ComplexEmbedding.conjugate).card = Ψ.card := Finset.card_image_of_injective _ hinj
  have h3 := Finset.card_compl Ψ
  have h4 := Embeddings.card E ℂ
  have h5 := Finset.card_le_univ Ψ
  rw [h1, h2] at h3
  omega

theorem phi1_bijective [NumberField E] (hΨ : ∀ σ : E →+* ℂ, σ ∈ Ψ ↔ ComplexEmbedding.conjugate σ ∉ Ψ) :
    Function.Bijective (phi1 Ψ) := by
  classical
  have hinj : Function.Injective (phi1 Ψ) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro t ht
    let B := Algebra.TensorProduct.basis ℝ (RingOfIntegers.basis E)
    have hx := li1 hΨ (fun k => B.repr t k) (fun τ hτ => by
      have h1 := congrFun ht ⟨τ, hτ⟩
      rw [← B.sum_repr t, map_sum] at h1
      simpa [B, Algebra.TensorProduct.basis_apply, phi1_tmul, Finset.sum_apply, Complex.real_smul]
        using h1)
    have : B.repr t = 0 := by
      ext k
      exact congrFun hx k
    simpa using B.repr.injective (this.trans (map_zero _).symm)
  refine ⟨hinj, ?_⟩
  rwa [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
  rw [Module.finrank_baseChange, RingOfIntegers.rank, Module.finrank_pi_fintype]
  simp only [Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    Fintype.card_coe]
  rw [← two_card hΨ]
  ring

end Scalar

section General

variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
variable {ι : Type}
variable (b : Module.Basis ι E V) (Ψ : Finset (E →+* ℂ)) (M : Submodule (𝓞 E) V)

def coordO : M →+ (Ψ → ι → ℂ) where
  toFun v τ i := (τ : E →+* ℂ) (b.repr v i)
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

def theta : ℝ ⊗[ℤ] M →ₗ[ℝ] (Ψ → ι → ℂ) :=
  LinearMap.liftBaseChange ℝ (coordO b Ψ M).toIntLinearMap

theorem theta_tmul (x : ℝ) (v : M) :
    theta b Ψ M (x ⊗ₜ v) = fun (τ : Ψ) i => (x : ℂ) * (τ : E →+* ℂ) (b.repr v i) := by
  ext τ i
  simp [theta, LinearMap.liftBaseChange_tmul, coordO, Complex.real_smul]

def embI : (ι → 𝓞 E) →+ (Ψ → ι → ℂ) where
  toFun n τ i := (τ : E →+* ℂ) (n i : E)
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

def phiI : ℝ ⊗[ℤ] (ι → 𝓞 E) →ₗ[ℝ] (Ψ → ι → ℂ) :=
  LinearMap.liftBaseChange ℝ (embI (ι := ι) Ψ).toIntLinearMap

theorem phiI_tmul (x : ℝ) (n : ι → 𝓞 E) :
    phiI Ψ (x ⊗ₜ n) = fun (τ : Ψ) i => (x : ℂ) * (τ : E →+* ℂ) (n i : E) := by
  ext τ i
  simp [phiI, LinearMap.liftBaseChange_tmul, embI, Complex.real_smul]

theorem phiI_eq [Fintype ι] [DecidableEq ι] (t : ℝ ⊗[ℤ] (ι → 𝓞 E)) (τ : Ψ) (i : ι) :
    phiI Ψ t τ i = phi1 Ψ (TensorProduct.piRight ℤ ℝ ℝ (fun _ : ι => 𝓞 E) t i) τ := by
  induction t using TensorProduct.inductionOn with
  | tmul x n => simp [phiI_tmul, phi1_tmul, TensorProduct.piRightHom_tmul]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

variable {Ψ}

theorem phiI_bijective [NumberField E] [Fintype ι] [DecidableEq ι] (hΨ : ∀ σ : E →+* ℂ, σ ∈ Ψ ↔ ComplexEmbedding.conjugate σ ∉ Ψ) :
    Function.Bijective (phiI (ι := ι) Ψ) := by
  constructor
  · intro t t' h
    apply (TensorProduct.piRight ℤ ℝ ℝ (fun _ : ι => 𝓞 E)).injective
    funext i
    apply (phi1_bijective hΨ).1
    funext τ
    rw [← phiI_eq, ← phiI_eq, h]
  · intro u
    choose y hy using fun i => (phi1_bijective hΨ).2 (fun τ => u τ i)
    refine ⟨(TensorProduct.piRight ℤ ℝ ℝ (fun _ : ι => 𝓞 E)).symm y, ?_⟩
    funext τ i
    rw [phiI_eq, LinearEquiv.apply_symm_apply, hy]


end General

end RHLean.Geometry.NativePolarizationRealCoordinates

end
