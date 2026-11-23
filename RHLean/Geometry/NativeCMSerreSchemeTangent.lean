import RHLean.Geometry.NativeCMWeierstrassIntegralTangent

/-!
# Scalar operations on actual dual-number tangent maps

This is the small geometric cut needed for the Lie module of the constructed
Serre scheme. Additivity is proved with the two-coordinate square-zero
extension, rather than supplied as a formal module law or a tangent premise.

Source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/
FormallyUnramifiedOfTangentMapInjective.lean, only `hom_ext_of_ker_inf` and
the dual-number scalar operations through `epsScale_add_comp`.
The source archive states no license; attribution is retained without
assigning one. No smoothness or tangent-surjectivity criterion is imported.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace RHLean.Geometry.NativeCM.SchemeTheory

/-- Two ring maps with jointly trivial kernel detect equality of actual
scheme maps when the first map is surjective on spectra. -/
theorem hom_ext_of_ker_inf {D E₁ E₂ : CommRingCat.{0}} (p₁ : D ⟶ E₁) (p₂ : D ⟶ E₂)
    (hs : Function.Surjective (Spec.map p₁)) (h : ∀ d, p₁ d = 0 → p₂ d = 0 → d = 0)
    {X : Scheme.{0}} {g g' : Spec D ⟶ X}
    (h₁ : Spec.map p₁ ≫ g = Spec.map p₁ ≫ g')
    (h₂ : Spec.map p₂ ≫ g = Spec.map p₂ ≫ g') : g = g' := by
  have hsurj : Function.Surjective (equalizer.ι g g') := by
    intro y
    obtain ⟨z, rfl⟩ := hs y
    exact ⟨equalizer.lift _ h₁ z, by rw [← Scheme.Hom.comp_apply, equalizer.lift_ι]⟩
  have : IsClosedImmersion (equalizer.ι g g') :=
    .of_isPreimmersion _ (by rw [hsurj.range_eq]; exact isClosed_univ)
  have key : ∀ {E : CommRingCat.{0}} (p : D ⟶ E) (_ : Spec.map p ≫ g = Spec.map p ≫ g')
      (d : Γ(Spec D, ⊤)), (equalizer.ι g g').appTop d = 0 → p ((Scheme.ΓSpecIso D).hom d) = 0 := by
    intro E p hp d hd
    have e : (Spec.map p).appTop d = 0 := by
      rw [← equalizer.lift_ι _ hp, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hd, map_zero]
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply, e, map_zero]
  have : IsIso (equalizer.ι g g') := by
    refine IsClosedImmersion.isIso_of_injective_of_isAffine ((injective_iff_map_eq_zero _).mpr ?_)
    intro d hd
    apply (Scheme.ΓSpecIso D).commRingCatIsoToRingEquiv.injective
    rw [map_zero]
    exact h _ (key p₁ h₁ d hd) (key p₂ h₂ d hd)
  rw [← cancel_epi (equalizer.ι g g'), equalizer.condition]

variable {R : Type} [CommRing R] {G H : Over (Sp R)} [GrpObj G] [GrpObj H]

def epsZero (R : Type) [CommRing R] : 𝟙_ (Over (Sp R)) ⟶ epsR R :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom R R R).toRingHom) (by
    change Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
    congr 1)

def epsScale (c : R) : epsR R ⟶ epsR R :=
  Over.homMk (spMap (epsScaleR c)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl])

@[simp] theorem epsScale_left (c : R) : (epsScale c).left = spMap (epsScaleR c) := rfl

theorem isTangent_iff (w : epsR R ⟶ G) : IsTangent w ↔ epsZero R ≫ w = 1 := by
  rw [← one_eq_one]
  exact ⟨fun h => Over.OverMorphism.ext h, fun h => congrArg Over.Hom.left h⟩

theorem isTangent_comp {w : epsR R ⟶ G} (hw : IsTangent w) (f : G ⟶ H) [IsMonHom f] :
    IsTangent (w ≫ f) := by
  rw [isTangent_iff] at hw ⊢
  rw [← Category.assoc, hw, one_comp]

@[reassoc]
theorem epsZero_epsScale (c : R) : epsZero R ≫ epsScale c = epsZero R := by
  ext1
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
  simp [epsScaleR]

@[reassoc]
theorem epsScale_mul (a b : R) : epsScale a ≫ epsScale b = epsScale (a * b) := by
  ext1
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
  ext <;> simp [epsScaleR, _root_.mul_assoc]

theorem epsScale_one : epsScale (1 : R) = 𝟙 _ := by
  ext1
  change Spec.map _ = 𝟙 _
  rw [← Spec.map_id]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
  ext <;> simp [epsScaleR]

theorem epsScale_zero : epsScale (0 : R) = toUnit _ ≫ epsZero R := by
  ext1
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
  ext <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]

theorem isTangent_epsScale (c : R) {w : epsR R ⟶ G} (hw : IsTangent w) :
    IsTangent (epsScale c ≫ w) := by
  rw [isTangent_iff] at hw ⊢
  rw [epsZero_epsScale_assoc, hw]

theorem epsScale_zero_comp {w : epsR R ⟶ G} (hw : IsTangent w) : epsScale 0 ≫ w = 1 := by
  rw [epsScale_zero, Category.assoc, (isTangent_iff w).mp hw, comp_one]

def sqZeroMap {M N : Type} [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
    [AddCommGroup N] [Module R N] [Module Rᵐᵒᵖ N] [IsCentralScalar R N] (l : M →ₗ[R] N) :
    Over.mk (spMap (algebraMap R (TrivSqZeroExt R N))) ⟶
      Over.mk (spMap (algebraMap R (TrivSqZeroExt R M))) :=
  Over.homMk (spMap (TrivSqZeroExt.map l).toRingHom) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (TrivSqZeroExt.map l).comp_algebraMap)

theorem sqZeroMap_comp_eq {M : Type} [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M]
    [IsCentralScalar R M] (l : R →ₗ[R] M) (l' : M →ₗ[R] R) :
    sqZeroMap l' ≫ sqZeroMap l = epsScale (l' (l 1)) := by
  ext1
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
  have : l' (l x.snd) = l' (l 1) * x.snd := by
    rw [mul_comm, ← smul_eq_mul, ← map_smul, ← map_smul, smul_eq_mul, _root_.mul_one]
  ext <;> simp [epsScaleR, this]

/-- Actual tangent addition follows from the square-zero scheme laws. -/
theorem epsScale_add_comp (a b : R) {w : epsR R ⟶ G} (hw : IsTangent w) :
    epsScale (a + b) ≫ w = (epsScale a ≫ w) * (epsScale b ≫ w) := by
  let i₁ := LinearMap.inl R R R
  let i₂ := LinearMap.inr R R R
  have key : sqZeroMap (i₁ + i₂) ≫ w = (sqZeroMap i₁ ≫ w) * (sqZeroMap i₂ ≫ w) := by
    ext1
    refine hom_ext_of_ker_inf
      (CommRingCat.ofHom (TrivSqZeroExt.map (LinearMap.fst R R R)).toRingHom)
      (CommRingCat.ofHom (TrivSqZeroExt.map (LinearMap.snd R R R)).toRingHom) ?_ ?_ ?_ ?_
    · refine (PrimeSpectrum.isHomeomorph_comap (TrivSqZeroExt.map (LinearMap.fst R R R)).toRingHom
        (fun x => ⟨1, one_pos, TrivSqZeroExt.map i₁ x, by ext <;> simp [i₁]⟩) fun d hd => ?_).surjective
      have h : d.fst = 0 := by simpa using congrArg TrivSqZeroExt.fst hd
      exact ⟨2, by ext1 <;> simp [pow_two, h]⟩
    · intro d h₁ h₂
      have h₃ : d.fst = 0 := by simpa using congrArg TrivSqZeroExt.fst h₁
      have h₄ : d.snd.1 = 0 := by simpa using congrArg TrivSqZeroExt.snd h₁
      have h₅ : d.snd.2 = 0 := by simpa using congrArg TrivSqZeroExt.snd h₂
      exact TrivSqZeroExt.ext h₃ (Prod.ext h₄ h₅)
    · refine congrArg Over.Hom.left
        (?_ : sqZeroMap (LinearMap.fst R R R) ≫ _ = sqZeroMap (LinearMap.fst R R R) ≫ _)
      rw [comp_mul]
      simp only [← Category.assoc, sqZeroMap_comp_eq]
      simp [i₁, i₂, epsScale_zero_comp hw]
    · refine congrArg Over.Hom.left
        (?_ : sqZeroMap (LinearMap.snd R R R) ≫ _ = sqZeroMap (LinearMap.snd R R R) ≫ _)
      rw [comp_mul]
      simp only [← Category.assoc, sqZeroMap_comp_eq]
      simp [i₁, i₂, epsScale_zero_comp hw]
  have := congrArg (sqZeroMap (a • LinearMap.fst R R R + b • LinearMap.snd R R R) ≫ ·) key
  simp only [comp_mul, ← Category.assoc, sqZeroMap_comp_eq] at this
  simpa [i₁, i₂] using this

/-- The actual tangent maps form an additive subgroup of dual-number
points, with the group law inherited from the given group scheme. -/
def lieSubgroup (G : Over (Sp R)) [GrpObj G] : AddSubgroup (Additive (epsR R ⟶ G)) where
  carrier := {x | IsTangent x.toMul}
  zero_mem' := by
    change IsTangent (1 : epsR R ⟶ G)
    rw [isTangent_iff, MonObj.comp_one]
  add_mem' {x y} hx hy := by
    change IsTangent (x.toMul * y.toMul)
    rw [isTangent_iff, MonObj.comp_mul,
      (isTangent_iff _).mp hx, (isTangent_iff _).mp hy, mul_one]
  neg_mem' {x} hx := by
    change IsTangent x.toMul⁻¹
    rw [isTangent_iff, GrpObj.comp_inv, (isTangent_iff _).mp hx, inv_one]

abbrev Lie (G : Over (Sp R)) [GrpObj G] := lieSubgroup G

namespace Lie

def hom (x : Lie G) : epsR R ⟶ G := x.val.toMul

@[ext] theorem ext {x y : Lie G} (h : hom x = hom y) : x = y := Subtype.ext h

@[simp] theorem hom_zero : hom (0 : Lie G) = 1 := rfl

@[simp] theorem hom_add (x y : Lie G) : hom (x + y) = hom x * hom y := rfl

theorem isTangent (x : Lie G) : IsTangent (hom x) := x.property

variable [IsCommMonObj G]

/-- Scalars act by the literal dual-number substitution epsilon ↦ c epsilon.
This module structure is intrinsic to the scheme's tangent maps. -/
instance module : Module R (Lie G) where
  smul c x := ⟨Additive.ofMul (epsScale c ≫ hom x), isTangent_epsScale c x.property⟩
  one_smul x := by
    apply Subtype.ext
    change Additive.ofMul (epsScale 1 ≫ hom x) = Additive.ofMul (hom x)
    rw [epsScale_one, Category.id_comp]
  mul_smul c d x := by
    apply Subtype.ext
    change Additive.ofMul (epsScale (c * d) ≫ hom x) =
      Additive.ofMul (epsScale c ≫ epsScale d ≫ hom x)
    rw [epsScale_mul_assoc]
  smul_zero c := by
    apply Subtype.ext
    change Additive.ofMul (epsScale c ≫ (1 : epsR R ⟶ G)) = Additive.ofMul 1
    rw [MonObj.comp_one]
  smul_add c x y := by
    apply Subtype.ext
    change Additive.ofMul (epsScale c ≫ (hom x * hom y)) =
      Additive.ofMul ((epsScale c ≫ hom x) * (epsScale c ≫ hom y))
    rw [MonObj.comp_mul]
  add_smul c d x := by
    apply Subtype.ext
    exact congrArg Additive.ofMul (epsScale_add_comp c d x.property)
  zero_smul x := by
    apply Subtype.ext
    exact congrArg Additive.ofMul (epsScale_zero_comp x.property)

@[simp] theorem hom_smul (c : R) (x : Lie G) : hom (c • x) = epsScale c ≫ hom x := rfl

end Lie

end RHLean.Geometry.NativeCM.SchemeTheory

end
