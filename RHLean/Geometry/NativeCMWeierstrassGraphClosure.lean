import RHLean.Geometry.NativeCMWeierstrassGenericFaithful

/-!
# The actual flat closure of the generic CM graph

The closure is the scheme-theoretic image of the actual generic graph.
Its flatness follows from torsion freeness over the valuation base, and
its generic fibre is proved isomorphic to the original graph. The final
theorem retains both projection maps and the original generic morphism.

Source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
`src/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FlatOfIsSchemeTheoreticallyDominantOfFractionRing.lean`.
The explicit graph specialization follows the beginning of
`src/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsUniqueHomExtensionSemiAbelianDvr.lean`.
The source archive states no license; attribution is retained without assigning one.
This does not yet assert that the first projection is an isomorphism:
its geometric-kernel finiteness is still to be proved.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace RHLean.Geometry.NativeCM.SchemeTheory.IntegralExtension

theorem ringHom_flat_of_injective_of_isUnit {R A B : Type*} [CommRing R] [IsDomain R]
    [IsBezout R] [CommRing A] [CommRing B] (φ : R →+* A) (ψ : A →+* B)
    (hψ : Function.Injective ψ) (h : ∀ r : R, r ≠ 0 → IsUnit (ψ (φ r))) : φ.Flat := by
  letI := φ.toAlgebra
  change Module.Flat R A
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  rintro a ⟨⟨r, hr⟩, hra⟩
  have h1 : φ r * a = 0 := hra
  have h2 : ψ (φ r) * ψ a = 0 := by rw [← map_mul, h1, map_zero]
  have h3 : ψ a = 0 := (h r (nonZeroDivisors.ne_zero hr)).mul_right_eq_zero.mp h2
  exact hψ (by rw [h3, map_zero])

theorem isSchemeTheoreticallyDominant_toImage {X Y : Scheme.{0}} (f : X ⟶ Y)
    [QuasiCompact f] : IsSchemeTheoreticallyDominant f.toImage := by
  rw [isSchemeTheoreticallyDominant_iff]
  have : QuasiCompact (f.toImage ≫ f.imageι) := by rw [f.toImage_imageι]; infer_instance
  have : QuasiCompact f.toImage := QuasiCompact.of_comp f.toImage f.imageι
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun U : Y.affineOpens => ⟨f.imageι ⁻¹ᵁ U.1, U.2.preimage f.imageι⟩) ?_ ?_
  · have h := f.imageι.preimage_iSup (fun U : Y.affineOpens => U.1)
    rw [← h, iSup_affineOpens_eq_top]
    simp
  · intro U
    rw [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply,
      ← RingHom.injective_iff_ker_eq_bot]
    exact f.toImage_app_injective U

theorem flat_of_isSchemeTheoreticallyDominant_of_fractionRing (R K : Type) [CommRing R]
    [IsDomain R] [IsBezout R] [Field K] [Algebra R K] [IsFractionRing R K] {Z G : Scheme.{0}}
    (p : Z ⟶ G) [QuasiCompact p] [IsSchemeTheoreticallyDominant p] (s : G ⟶ Sp R)
    (z : Z ⟶ Sp K) (w : p ≫ s = z ≫ spMap (algebraMap R K)) : Flat s := by
  refine HasRingHomProperty.of_iSup_eq_top (P := @Flat) (fun U : G.affineOpens => U)
    (iSup_affineOpens_eq_top G) fun U => ?_
  have key : ((Scheme.ΓSpecIso (.of R)).inv ≫ s.appLE ⊤ U le_top) ≫ p.app U =
      CommRingCat.ofHom (algebraMap R K) ≫ (Scheme.ΓSpecIso (.of K)).inv ≫
        z.appLE ⊤ (p ⁻¹ᵁ U) le_top := by
    rw [Scheme.ΓSpecIso_inv_naturality_assoc, Category.assoc, p.app_eq_appLE,
      Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    congr 1
    refine (Scheme.Hom.appLE_comp_appLE p s ⊤ U (p ⁻¹ᵁ U) _ _).trans
      (Eq.trans ?_ (Scheme.Hom.appLE_comp_appLE z (spMap (algebraMap R K))
        ⊤ ⊤ (p ⁻¹ᵁ U) _ _).symm)
    rw [w]
  have hfl : ((Scheme.ΓSpecIso (.of R)).inv ≫ s.appLE ⊤ U le_top).hom.Flat := by
    refine ringHom_flat_of_injective_of_isUnit (R := R) _ (p.app U).hom (p.app_injective U) ?_
    intro r hr
    have h1 : IsUnit (algebraMap R K r) := IsUnit.mk0 _ (by simpa using hr)
    have h2 := h1.map ((Scheme.ΓSpecIso (.of K)).inv ≫ z.appLE ⊤ (p ⁻¹ᵁ U) le_top).hom
    have h3 := congrArg (fun φ => CommRingCat.Hom.hom φ r) key
    exact h3 ▸ h2
  exact (RingHom.Flat.respectsIso.cancel_left_isIso _ _).mp hfl

/-- The actual schematic image supplies a flat model of any closed generic
subscheme, with its proved generic-fibre identification. -/
theorem exists_flat_closure (R K : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (X : Over (Sp R)) (Z : Over (Sp K))
    (i : Z ⟶ (Over.pullback (spMap (algebraMap R K))).obj X) [IsClosedImmersion i.left] :
    ∃ (Ga : Over (Sp R)) (io : Ga ⟶ X)
      (e : (Over.pullback (spMap (algebraMap R K))).obj Ga ≅ Z),
      IsClosedImmersion io.left ∧ Flat Ga.hom ∧
        e.hom ≫ i = (Over.pullback (spMap (algebraMap R K))).map io := by
  let j : Sp K ⟶ Sp R := spMap (algebraMap R K)
  have : IsPreimmersion j := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have : Flat j := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat K (nonZeroDivisors R))
  let i' : Z.left ⟶ pullback X.hom j := i.left
  have : IsClosedImmersion i' := inferInstanceAs (IsClosedImmersion i.left)
  have hw : i' ≫ pullback.snd X.hom j = Z.hom := Over.w i
  let f : Z.left ⟶ X.left := i' ≫ pullback.fst X.hom j
  have : QuasiCompact f := inferInstance
  have : QuasiCompact (f.toImage ≫ f.imageι) := by rw [f.toImage_imageι]; infer_instance
  have : QuasiCompact f.toImage := QuasiCompact.of_comp f.toImage f.imageι
  have := isSchemeTheoreticallyDominant_toImage f
  have hsq : f.toImage ≫ (f.imageι ≫ X.hom) = Z.hom ≫ j := by
    rw [f.toImage_imageι_assoc, Category.assoc, pullback.condition, reassoc_of% hw]
  let Ga : Over (Sp R) := Over.mk (f.imageι ≫ X.hom)
  let io : Ga ⟶ X := Over.homMk f.imageι rfl
  let t : Z.left ⟶ pullback (f.imageι ≫ X.hom) j := pullback.lift f.toImage Z.hom hsq
  let m : pullback (f.imageι ≫ X.hom) j ⟶ pullback X.hom j :=
    pullback.map _ _ _ _ f.imageι (𝟙 _) (𝟙 _) (by simp) (by simp)
  have : MorphismProperty.IsStableUnderComposition @IsClosedImmersion.{0} :=
    ⟨fun f g hf hg => @IsClosedImmersion.comp _ _ _ f g hf hg⟩
  have : IsClosedImmersion m :=
    MorphismProperty.pullbackMap (P := @IsClosedImmersion.{0}) inferInstance inferInstance
      rfl (by simp)
  have htm : t ≫ m = i' := by
    apply pullback.hom_ext
    · simp [t, m, f]
    · simp [t, m, hw]
  have : IsClosedImmersion (t ≫ m) := htm ▸ inferInstanceAs (IsClosedImmersion i')
  have : IsClosedImmersion t := IsClosedImmersion.of_comp_isClosedImmersion t m
  have hpb : IsPullback (𝟙 Z.left) t f.toImage (pullback.fst (f.imageι ≫ X.hom) j) :=
    IsPullback.of_horiz_isIso_mono ⟨by simp [t]⟩
  have : IsSchemeTheoreticallyDominant t := .of_isPullback hpb
  have : IsIso t := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr t.ker_eq_bot
  refine ⟨Ga, io,
    (Over.isoMk (f := Z) (g := (Over.pullback j).obj Ga) (asIso t) ?_).symm,
    inferInstanceAs (IsClosedImmersion f.imageι),
    flat_of_isSchemeTheoreticallyDominant_of_fractionRing R K f.toImage _ Z.hom hsq, ?_⟩
  · exact pullback.lift_snd _ _ _
  · rw [Iso.symm_hom, Iso.inv_comp_eq]
    apply Over.OverMorphism.ext
    change i' = t ≫ _
    rw [← htm]
    congr 1

/-- The generic morphism has an actual flat graph closure over the
valuation ring. Both projections recover the same original morphism. -/
theorem exists_flat_graph (R K : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (G H : Over (Sp R)) [IsSeparated G.hom] [IsSeparated H.hom]
    (f : (Over.pullback (spMap (algebraMap R K))).obj G ⟶
      (Over.pullback (spMap (algebraMap R K))).obj H) :
    ∃ (Ga : Over (Sp R)) (io : Ga ⟶ G ⊗ H)
      (e : (Over.pullback (spMap (algebraMap R K))).obj Ga ≅
        (Over.pullback (spMap (algebraMap R K))).obj G),
      IsClosedImmersion io.left ∧ Flat Ga.hom ∧
        (Over.pullback (spMap (algebraMap R K))).map (io ≫ fst G H) = e.hom ∧
        (Over.pullback (spMap (algebraMap R K))).map (io ≫ snd G H) = e.hom ≫ f := by
  let Φ := Over.pullback (spMap (algebraMap R K))
  let i : Φ.obj G ⟶ Φ.obj (G ⊗ H) := lift (𝟙 _) f ≫ Functor.LaxMonoidal.μ Φ G H
  have hi1 : i ≫ Φ.map (fst G H) = 𝟙 _ := by
    rw [Category.assoc, Functor.Monoidal.μ_fst, lift_fst]
  have hi2 : i ≫ Φ.map (snd G H) = f := by simp [i]
  have : IsSeparated (G ⊗ H).hom :=
    inferInstanceAs (IsSeparated (pullback.fst G.hom H.hom ≫ G.hom))
  have : IsSeparated (Φ.map (fst G H)).left := by
    have h : IsSeparated (Φ.obj (G ⊗ H)).hom :=
      inferInstanceAs (IsSeparated (pullback.snd (G ⊗ H).hom _))
    rw [← Over.w (Φ.map (fst G H))] at h
    exact IsSeparated.of_comp _ (Φ.obj G).hom
  have : IsClosedImmersion i.left := by
    have : IsClosedImmersion (i.left ≫ (Φ.map (fst G H)).left) := by
      rw [← Over.comp_left, hi1, Over.id_left]
      infer_instance
    exact IsClosedImmersion.of_comp i.left (Φ.map (fst G H)).left
  obtain ⟨Ga, io, e, hio, hGa, he⟩ := exists_flat_closure R K (G ⊗ H) (Φ.obj G) i
  refine ⟨Ga, io, e, hio, hGa, ?_, ?_⟩
  · rw [Functor.map_comp, ← he, Category.assoc, hi1, Category.comp_id]
  · rw [Functor.map_comp, ← he, Category.assoc, hi2]

end RHLean.Geometry.NativeCM.SchemeTheory.IntegralExtension

end
