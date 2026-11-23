import Mathlib

/-!
# Effective descent for the native theta value

The pushout and scalar descent used in the short-theta construction are
proved from Mathlib's faithfully flat base change and effective equalizer.
In particular, the preimage is constructed in the original base algebra;
neither a descended value nor a section-existence law is an input.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/`
`FaithfullyFlatPointsBaseChangeDescent.lean`.
The source archive/mirror states no license; this notice preserves
attribution without assigning a new license.
-/

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace RHLean.Geometry.NativeTheta.Descent

/-- Flatness and lifting of geometric points imply faithful flatness. -/
theorem faithfullyFlat_of_geometric_points (S B : Type) [CommRing S] [CommRing B]
    (φ : S →+* B) (hφ : φ.Flat)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (ψ : S →+* K),
      ∃ χ : B →+* K, χ.comp φ = ψ) : φ.FaithfullyFlat := by
  rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
  refine ⟨hφ, fun p => ?_⟩
  obtain ⟨χ, hχ⟩ := h (AlgebraicClosure p.asIdeal.ResidueField)
    ((algebraMap p.asIdeal.ResidueField _).comp (algebraMap S p.asIdeal.ResidueField))
  refine ⟨⟨RingHom.ker χ, RingHom.ker_isPrime χ⟩, ?_⟩
  ext x
  have hx := RingHom.congr_fun hχ x
  simp only [RingHom.comp_apply] at hx
  change χ (φ x) = 0 ↔ _
  rw [hx, map_eq_zero, Ideal.algebraMap_residueField_eq_zero]

/-- The localizations used in a chart refinement preserve flatness. -/
theorem flat_comp_localizationAway (S B : Type) [CommRing S] [CommRing B]
    (φ : S →+* B) (e : B) (hφ : φ.Flat) :
    ((algebraMap B (Localization.Away e)).comp φ).Flat :=
  hφ.comp (RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (Submonoid.powers e)))

/-- Construct the common comparison algebra as the actual tensor pushout.
The map out of the first algebra is faithfully flat and injective. -/
theorem exists_faithfullyFlat_pushout (K S S₁ S₂ : Type) [Field K]
    [CommRing S] [CommRing S₁] [CommRing S₂]
    [Algebra K S] [Algebra K S₁] [Algebra K S₂]
    (φ₁ : S →ₐ[K] S₁) (φ₂ : S →ₐ[K] S₂)
    (h : φ₂.toRingHom.FaithfullyFlat) :
    ∃ (T : Type) (_ : CommRing T) (_ : Algebra K T)
      (ψ₁ : S₁ →ₐ[K] T) (ψ₂ : S₂ →ₐ[K] T),
      ψ₁.comp φ₁ = ψ₂.comp φ₂ ∧
      ψ₁.toRingHom.FaithfullyFlat ∧ Function.Injective ψ₁ := by
  letI : Algebra S S₁ := φ₁.toRingHom.toAlgebra
  letI : Algebra S S₂ := φ₂.toRingHom.toAlgebra
  have : Module.FaithfullyFlat S S₂ := RingHom.faithfullyFlat_algebraMap_iff.1 h
  letI : Algebra K (S₁ ⊗[S] S₂) :=
    ((Algebra.TensorProduct.includeLeftRingHom : S₁ →+* S₁ ⊗[S] S₂).comp
      (algebraMap K S₁)).toAlgebra
  have hff : (algebraMap S₁ (S₁ ⊗[S] S₂)).FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.2 inferInstance
  refine ⟨S₁ ⊗[S] S₂, inferInstance, inferInstance,
    { (Algebra.TensorProduct.includeLeftRingHom : S₁ →+* S₁ ⊗[S] S₂) with
      commutes' := fun _ => rfl },
    { (Algebra.TensorProduct.includeRight : S₂ →ₐ[S] S₁ ⊗[S] S₂).toRingHom with
      commutes' := fun c => ?_ }, ?_, hff, hff.injective⟩
  · show (1 : S₁) ⊗ₜ[S] algebraMap K S₂ c = algebraMap K S₁ c ⊗ₜ[S] (1 : S₂)
    rw [← φ₁.commutes, ← φ₂.commutes]
    exact (Algebra.TensorProduct.tmul_one_eq_one_tmul (algebraMap K S c)).symm
  · exact AlgHom.ext fun s => Algebra.TensorProduct.tmul_one_eq_one_tmul s

/-- Descend a compatible element through a faithfully flat algebra map.
Compatibility is tested in common algebras and then applied to the tensor
square; Mathlib's effective descent constructs the unique base element. -/
theorem existsUnique_preimage_of_faithfullyFlat (K S B : Type) [Field K]
    [CommRing S] [CommRing B] [Algebra K S] [Algebra K B]
    (φ : S →ₐ[K] B) (h : φ.toRingHom.FaithfullyFlat) (w : B)
    (hw : ∀ (T : Type) [CommRing T] [Algebra K T] (ψ₁ ψ₂ : B →ₐ[K] T),
      ψ₁.comp φ = ψ₂.comp φ → ψ₁ w = ψ₂ w) : ∃! v : S, φ v = w := by
  letI : Algebra S B := φ.toRingHom.toAlgebra
  have : Module.FaithfullyFlat S B := RingHom.faithfullyFlat_algebraMap_iff.1 h
  letI : Algebra K (B ⊗[S] B) :=
    ((Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[S] B).comp
      (algebraMap K B)).toAlgebra
  let ψ₁ : B →ₐ[K] B ⊗[S] B :=
    { (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[S] B) with
      commutes' := fun _ => rfl }
  let ψ₂ : B →ₐ[K] B ⊗[S] B :=
    { (Algebra.TensorProduct.includeRight : B →ₐ[S] B ⊗[S] B).toRingHom with
      commutes' := fun c => by
        show (1 : B) ⊗ₜ[S] algebraMap K B c = algebraMap K B c ⊗ₜ[S] (1 : B)
        rw [← φ.commutes]
        exact (Algebra.TensorProduct.tmul_one_eq_one_tmul (algebraMap K S c)).symm }
  have hcomp : ψ₁.comp φ = ψ₂.comp φ :=
    AlgHom.ext fun s => Algebra.TensorProduct.tmul_one_eq_one_tmul s
  have hw' : w ⊗ₜ[S] (1 : B) = (1 : B) ⊗ₜ[S] w := hw (B ⊗[S] B) ψ₁ ψ₂ hcomp
  obtain ⟨v, hv⟩ := (Algebra.IsEffective.of_faithfullyFlat S B w).1
    (by rw [Algebra.TensorProduct.includeLeftSubRight_apply, sub_eq_zero]; exact hw')
  exact ⟨v, hv, fun v' hv' => h.injective (hv'.trans hv.symm)⟩

end RHLean.Geometry.NativeTheta.Descent

end
