import RHLean.Geometry.NativeThetaCuspQuotientAdjoint

/-!
# A constructed nontrivial character of the actual finite quotient

The determinant on the automorphisms of the original projective module
modulo the split-five ideal has a nontrivial finite character. A diagonal
minus-one automorphism witnesses nontriviality. Its values generate an
actual number field, and every value is integral and has norm one at every
complex embedding. Neither a character nor its norm law is a premise.

This is the arithmetic character used before the source constructs its
component section. The geometric PsiTie law still requires the actual
moduli cover and component idempotents.

Source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsDeltaDatLargeCoeff.lean
(`exists_char_ne_one` and its finite-root-of-unity coefficient construction),
src/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsComponentWeight.lean
(`exists_char_subfield`), and
src/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/IsIntegralZpowOfPowEqOne.lean.
The source mirror states no license; attribution is retained.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open NumberField Module Matrix
open scoped Pointwise BigOperators Classical

namespace RHLean.Geometry.NativeTheta.Cusp.FiniteCharacter

/-- A concrete determinant character detects the actual diagonal sign. -/
theorem exists_char_ne_one {R Q : Type} [CommRing R] [AddCommGroup Q] [Module R Q]
    (I : Ideal R) [Finite (R ⧸ I)] {r : ℕ} (hr : 1 ≤ r)
    (e : Q ≃ₗ[R] (Fin r → R ⧸ I)) (h2 : (-1 : (R ⧸ I)ˣ) ≠ 1) :
    ∃ ψ : (Q ≃ₗ[R] Q) →* ℂˣ, ψ ≠ 1 := by
  have hs : Function.Surjective (algebraMap R (R ⧸ I)) := Ideal.Quotient.mk_surjective
  let cj : (Q ≃ₗ[R] Q) →* ((Fin r → R ⧸ I) ≃ₗ[R ⧸ I] (Fin r → R ⧸ I)) :=
    MonoidHom.mk' (fun k => (e.symm ≪≫ₗ k ≪≫ₗ e).extendScalarsOfSurjective hs)
      (fun a b => by ext x i; simp [LinearEquiv.mul_apply])
  let i₀ : Fin r := ⟨0, hr⟩
  let δ : Fin r → R ⧸ I := Function.update 1 i₀ (-1)
  have hδ : Matrix.diagonal δ * Matrix.diagonal δ = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    by_cases h : i = i₀
    · subst i
      simp [δ]
    · simp [δ, h]
  let g : (Fin r → R ⧸ I) ≃ₗ[R ⧸ I] (Fin r → R ⧸ I) := Matrix.toLin'OfInv hδ hδ
  have hg : LinearEquiv.det g = -1 := by
    apply Units.ext
    rw [LinearEquiv.coe_det]
    have he : (g : (Fin r → R ⧸ I) →ₗ[R ⧸ I] (Fin r → R ⧸ I)) =
        Matrix.toLin' (Matrix.diagonal δ) := rfl
    rw [he, LinearMap.det_toLin', Matrix.det_diagonal,
      Finset.prod_update_of_mem (Finset.mem_univ _)]
    simp
  have hk : cj (e ≪≫ₗ g.restrictScalars R ≪≫ₗ e.symm) = g := by
    ext x i
    simp [cj]
  obtain ⟨χ, hχ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (R ⧸ I)ˣ ℂ h2
  refine ⟨χ.comp (LinearEquiv.det.comp cj), fun h => hχ ?_⟩
  have he := DFunLike.congr_fun h (e ≪≫ₗ g.restrictScalars R ≪≫ₗ e.symm)
  rwa [MonoidHom.comp_apply, MonoidHom.comp_apply, hk, hg] at he

/-- The values of an actual finite character generate a number field.
Their integrality and unit norm at every embedding follow from finite order. -/
theorem exists_numberField_character {G : Type} [Group G] [Finite G]
    (ψ₀ : G →* ℂˣ) (hψ₀ : ψ₀ ≠ 1) :
    ∃ (F : IntermediateField ℚ ℂ) (_ : NumberField F) (ψ : G →* Fˣ),
      ψ ≠ 1 ∧ (∀ g, (((ψ g : Fˣ) : F) : ℂ) = (ψ₀ g : ℂ)) ∧
      ∀ g, IsIntegral ℤ (ψ g : F) ∧ ∀ σ : F →+* ℂ, ‖σ (ψ g : F)‖ = 1 := by
  have hN : 0 < Nat.card G := Nat.card_pos
  have hp : ∀ g, (ψ₀ g : ℂ) ^ Nat.card G = 1 := fun g => by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]
  let S : Set ℂ := Set.range fun g => (ψ₀ g : ℂ)
  have hS : S.Finite := Set.finite_range _
  let : Finite S := hS.to_subtype
  have hi : ∀ z ∈ S, IsIntegral ℚ z := by
    rintro z ⟨g, rfl⟩
    exact IsIntegral.of_pow hN (by rw [hp]; exact isIntegral_one)
  let F := IntermediateField.adjoin ℚ S
  let : FiniteDimensional ℚ F := IntermediateField.finiteDimensional_adjoin hi
  let : NumberField F := ⟨⟩
  have hm : ∀ g, (ψ₀ g : ℂ) ∈ F := fun g =>
    IntermediateField.subset_adjoin ℚ S ⟨g, rfl⟩
  let ψ : G →* Fˣ := MonoidHom.toHomUnits
    { toFun := fun g => (⟨(ψ₀ g : ℂ), hm g⟩ : F)
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp) }
  have he : ∀ g, (((ψ g : Fˣ) : F) : ℂ) = (ψ₀ g : ℂ) := fun _ => rfl
  have hne : ψ ≠ 1 := fun h => hψ₀ (MonoidHom.ext fun g => Units.ext (by
    rw [← he g, h]
    rfl))
  refine ⟨F, inferInstance, ψ, hne, he, fun g => ?_⟩
  have hp' : (ψ g : F) ^ Nat.card G = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]
  refine ⟨IsIntegral.of_pow hN (by rw [hp']; exact isIntegral_one), fun σ => ?_⟩
  exact Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hp', map_one]) hN.ne'

open QuotientAdjoint

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
  {H : NativeGeometricHost E}

/-- Nontriviality is paid by the constructed five-level quotient itself;
the module remains the original finite projective D.La. -/
theorem exists_five_character (D : NativeGeometricDatum H)
    (P : Ideal (𝓞 E)) (hP : P ≠ ⊤) (hP0 : P ≠ ⊥)
    (h5 : (5 : 𝓞 E) ∈ P) (hr : 1 ≤ D.p + D.q) :
    ∃ (F : IntermediateField ℚ ℂ) (_ : NumberField F)
      (ψ : (IQuot D P ≃ₗ[𝓞 E] IQuot D P) →* Fˣ),
      ψ ≠ 1 ∧ ∀ g, IsIntegral ℤ (ψ g : F) ∧
        ∀ σ : F →+* ℂ, ‖σ (ψ g : F)‖ = 1 := by
  let : Finite (𝓞 E ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot _ hP0
  let : Nontrivial (𝓞 E ⧸ P) := Ideal.Quotient.nontrivial_iff.mpr hP
  let := D.fin
  let := D.proj
  obtain ⟨e⟩ := NativeThetaFullLevelCost.nonempty_equiv_mod (𝓞 E) D.La P (D.p + D.q) D.rank
  have h2 : (-1 : (𝓞 E ⧸ P)ˣ) ≠ 1 := by
    intro h
    have hneg : (-1 : 𝓞 E ⧸ P) = 1 := by simpa using congrArg Units.val h
    have hzero : (5 : 𝓞 E ⧸ P) = 0 := by
      simpa only [map_ofNat] using
        (Ideal.Quotient.eq_zero_iff_mem.mpr h5 : Ideal.Quotient.mk P (5 : 𝓞 E) = 0)
    exact (one_ne_zero : (1 : 𝓞 E ⧸ P) ≠ 0) (by linear_combination hzero + 2 * hneg)
  obtain ⟨ψ₀, hψ₀⟩ := exists_char_ne_one P hr e h2
  let : Finite (IQuot D P ≃ₗ[𝓞 E] IQuot D P) :=
    NativeThetaFullLevelCost.finite_quotient_aut (𝓞 E) D.La P
  obtain ⟨F, hF, ψ, hψ, _, hnorm⟩ := exists_numberField_character ψ₀ hψ₀
  exact ⟨F, hF, ψ, hψ, hnorm⟩

end RHLean.Geometry.NativeTheta.Cusp.FiniteCharacter
