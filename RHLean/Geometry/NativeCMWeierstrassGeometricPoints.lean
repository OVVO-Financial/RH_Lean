import RHLean.Geometry.NativeCMWeierstrassGroupFromPoints

/-!
# Geometric point detection for the finite-field CM scheme construction

Closed points detect open covers and morphisms of reduced schemes of finite
type over a field. The morphism statement below works with one fixed embedding
into an algebraically closed extension. It is proved by extending the finite
residue field at each closed point, so it assumes no analytic algebraization
or extension theorem.

The closed-point arguments follow Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/
SurjectiveOfComplexPointsLiftOfUniversallyClosed.lean, through
`hom_ext_of_points`. The embedded-field version is a native derivation from
the same residue-field argument and Mathlib's algebraic-closure extension.
The source archive states no license; attribution is retained without
assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

namespace RHLean.Geometry.NativeCM.SchemeTheory.GeometricPoints

universe u

variable {K : Type u} [Field K] [IsAlgClosed K]

theorem exists_point_mem {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    [LocallyOfFiniteType p] {Z : Set X} (hZ : IsLocallyClosed Z) (hne : Z.Nonempty) :
    ∃ x : Spec (.of K) ⟶ X, x ≫ p = 𝟙 _ ∧ ∀ a, x a ∈ Z := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
  obtain ⟨y, hyZ, hy⟩ := nonempty_inter_closedPoints hne hZ
  have hy : IsClosed {y} := hy
  exact ⟨pointOfClosedPoint p y hy, pointOfClosedPoint_comp p y hy,
    fun a => by rw [pointOfClosedPoint_apply]; exact hyZ⟩

theorem exists_geomPoint_mem {X S : Scheme.{u}} (p : X ⟶ S) [LocallyOfFiniteType p]
    (t : Spec (.of K) ⟶ S) [Surjective t]
    {Z : Set X} (hZ : IsLocallyClosed Z) (hne : Z.Nonempty) :
    ∃ x : Spec (.of K) ⟶ X, x ≫ p = t ∧ ∀ a, x a ∈ Z := by
  obtain ⟨z, hz⟩ := hne
  obtain ⟨w, hw⟩ := (pullback.fst p t).surjective z
  obtain ⟨y, hy, hyZ⟩ := exists_point_mem (pullback.snd p t)
    (hZ.preimage (pullback.fst p t).continuous) ⟨w, show pullback.fst p t w ∈ Z from hw ▸ hz⟩
  refine ⟨y ≫ pullback.fst p t, ?_, fun a => hyZ a⟩
  rw [Category.assoc, pullback.condition, reassoc_of% hy]

omit [IsAlgClosed K] in
theorem surjective_specMap_field {F : Type u} [Field F] (σ : F →+* K) :
    Surjective (Spec.map (CommRingCat.ofHom σ)) :=
  ⟨fun _ => ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ _⟩⟩

omit [IsAlgClosed K] in
theorem top_le_preimage_iff {X : Scheme.{u}} (x : Spec (.of K) ⟶ X)
    (U : X.Opens) (a : ↥(Spec (.of K))) : ⊤ ≤ x ⁻¹ᵁ U ↔ x a ∈ U := by
  constructor
  · intro h
    exact h (show a ∈ (⊤ : (Spec (.of K)).Opens) from trivial)
  · intro h b _
    rw [Subsingleton.elim b a]
    exact h

theorem opens_le_of_geomPoints {X S : Scheme.{u}} (p : X ⟶ S) [LocallyOfFiniteType p]
    (t : Spec (.of K) ⟶ S) [Surjective t] (U V : X.Opens)
    (h : ∀ x : Spec (.of K) ⟶ X, x ≫ p = t → ⊤ ≤ x ⁻¹ᵁ U → ⊤ ≤ x ⁻¹ᵁ V) : U ≤ V := by
  intro z hzU
  by_contra hzV
  obtain ⟨x, hx, hxZ⟩ := exists_geomPoint_mem p t (Z := (U : Set X) ∩ (V : Set X)ᶜ)
    (U.isOpen.isLocallyClosed.inter V.isOpen.isClosed_compl.isLocallyClosed) ⟨z, hzU, hzV⟩
  let a : ↥(Spec (.of K)) := IsLocalRing.closedPoint K
  exact (hxZ a).2 ((top_le_preimage_iff x V a).1
    (h x hx ((top_le_preimage_iff x U a).2 (hxZ a).1)))

variable {F : Type u} [Field F] [Algebra F K]

/-- Morphisms are detected by the points of one fixed algebraically closed
extension, with the specified embedding of the original field retained. -/
theorem hom_ext_of_embedded_points {X Y S : Scheme.{u}}
    (p : X ⟶ Spec (.of F)) [LocallyOfFiniteType p] [IsReduced X]
    (q : Y ⟶ S) [IsSeparated q] {f g : X ⟶ Y} (hfg : f ≫ q = g ≫ q)
    (h : ∀ x : Spec (.of K) ⟶ X,
      x ≫ p = Spec.map (CommRingCat.ofHom (algebraMap F K)) → x ≫ f = x ≫ g) : f = g := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
  refine ext_of_fromSpecResidueField_eq f g q (closedPoints X)
    (dense_iff_closure_eq.mpr closure_closedPoints) ?_ hfg
  intro y hy
  have hy : IsClosed {y} := hy
  have : IsFinite (X.fromSpecResidueField y ≫ p) := by
    rw [isClosed_singleton_iff_isClosedImmersion] at hy
    rw [isFinite_iff_locallyOfFiniteType_of_jacobsonSpace]
    infer_instance
  let φ := Spec.preimage (X.fromSpecResidueField y ≫ p)
  let : Algebra F (X.residueField y) := φ.hom.toAlgebra
  have hφ : φ.hom.IsIntegral := by
    rw [← IsIntegralHom.SpecMap_iff]
    rw [Spec.map_preimage]
    infer_instance
  have : Algebra.IsIntegral F (X.residueField y) := ⟨hφ⟩
  let σ : X.residueField y →ₐ[F] K := IsAlgClosed.lift
  let ι : Spec (.of K) ⟶ Spec (X.residueField y) :=
    Spec.map (CommRingCat.ofHom σ.toRingHom)
  have hι : (ι ≫ X.fromSpecResidueField y) ≫ p =
      Spec.map (CommRingCat.ofHom (algebraMap F K)) := by
    rw [Category.assoc, ← Spec.map_preimage (X.fromSpecResidueField y ≫ p)]
    change Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ Spec.map φ = _
    rw [← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext σ.comp_algebraMap)
  have : Surjective ι := surjective_specMap_field σ.toRingHom
  refine ext_of_isDominant_of_isSeparated q (by simp only [Category.assoc, hfg]) ι ?_
  simpa only [Category.assoc] using h (ι ≫ X.fromSpecResidueField y) hι

theorem over_hom_ext_of_embedded_points {A B : Over (Spec (.of F))}
    [LocallyOfFiniteType A.hom] [IsReduced A.left] [IsSeparated B.hom] {f g : A ⟶ B}
    (h : ∀ x : specOver F K ⟶ A, x ≫ f = x ≫ g) : f = g := by
  apply Over.OverMorphism.ext
  refine hom_ext_of_embedded_points (K := K) A.hom B.hom ((Over.w f).trans (Over.w g).symm) ?_
  intro x hx
  exact congrArg Over.Hom.left (h (Over.homMk x hx))

end RHLean.Geometry.NativeCM.SchemeTheory.GeometricPoints

end
