import RHLean.Geometry.NativeCMWeierstrassGeometricKernel
import RHLean.Geometry.NativeCMWeierstrassGraphGroup
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Integral extension on the actual good-reduction elliptic graph

Use relative normalization, rather than reconstruct the general
normality of smooth schemes. In the pinned Mathlib, normalization
commutes with smooth base change and a proper locally quasi-finite
morphism is finite.

The generic point of a DVR has relative normalization the original
base (integral closedness). Smooth base change gives the same assertion
for the generic fibre of the original elliptic model. The universal
property of relative normalization supplies a section of the finite
graph projection. Generic-fibre faithfulness on the flat actual graph
makes this section its inverse. Thus the actual generic homomorphism
extends to the original two elliptic equations over the DVR.

This pays a compatibility input to the one-sided CM period supplier.
The mathematical source for the graph-extension strategy is Levent
Alpoge (with Claude), CocoSgt/riemann-hypothesis-lean at
7cbf7a0c32fca1badf05931879a37c3f8a2b03b4, the good-reduction proof in
Development/AbelianVarietyTheory/Proofs/UnitaryExistence/
ExistsUniqueHomExtensionSemiAbelianDvr.lean. Here the normalization
argument uses the original Mathlib universal property and its existing
smooth-base-change theorem, not an assumed hom-extension result.
The source archive states no license; attribution is retained without
assigning one.

The actual generic homomorphisms between the selected class models,
their normalized tangent comparison at all embeddings and the
global arithmetic assembly remain separate inputs. This file does
not assert the complete physical signed-excess estimate or RH.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Classical CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace RHLean.Geometry.NativeCM.SchemeTheory.IntegralExtension

open SchemeTheory.WeierstrassCurve SchemeTheory.WeierstrassLie

/-- Integral closedness of the actual base identifies its relative
normalization in the fraction field. This is an affine calculation,
with the genuine Spec global-section isomorphisms. -/
theorem fractionField_fromNormalization_isIso
    (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K] :
    IsIso (spMap (algebraMap R K)).fromNormalization := by
  let j := spMap (algebraMap R K)
  let _ : Algebra Γ(Sp R, ⊤) Γ(Sp K, ⊤) := j.appTop.hom.toAlgebra
  let er : Γ(Sp R, ⊤) →+* R := (Scheme.ΓSpecIso (.of R)).hom.hom
  let ek : Γ(Sp K, ⊤) →+* K := (Scheme.ΓSpecIso (.of K)).hom.hom
  have her : Function.Bijective er :=
    ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).hom
  have hek : Function.Bijective ek :=
    ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).hom
  have he (a : Γ(Sp R, ⊤)) : algebraMap R K (er a) = ek (j.appTop a) := by
    exact (congrArg (fun f => f a)
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R K)))).symm
  have he' : (algebraMap R K).comp er =
      ek.comp (algebraMap Γ(Sp R, ⊤) Γ(Sp K, ⊤)) := by
    ext a
    exact he a
  let A := integralClosure Γ(Sp R, ⊤) Γ(Sp K, ⊤)
  have hbij : Function.Bijective (algebraMap Γ(Sp R, ⊤) A) := by
    constructor
    · intro a b h
      apply her.1
      apply IsFractionRing.injective R K
      rw [he, he]
      exact congrArg ek (congrArg Subtype.val h)
    · intro z
      have hz : IsIntegral R (ek z.1) := z.2.map_of_comp_eq er ek he'
      obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp hz
      obtain ⟨a, ha⟩ := her.2 r
      refine ⟨a, Subtype.ext (hek.1 ?_)⟩
      change ek (j.appTop a) = ek z.1
      rw [← he, ha, hr]
  have hι : IsIso (CommRingCat.ofHom (algebraMap Γ(Sp R, ⊤) A)) :=
    (ConcreteCategory.isIso_iff_bijective _).2 hbij
  have happ : IsIso j.fromNormalization.appTop := by
    change IsIso (j.fromNormalization.app ⊤)
    rw [Scheme.Hom.fromNormalization_app j (isAffineOpen_top _)]
    exact IsIso.comp_isIso' hι (j.normalizationObjIso (isAffineOpen_top (Sp R))).isIso_inv
  have : IsAffine j.normalization := isAffine_of_isAffineHom j.fromNormalization
  have : IsIso (j.fromNormalization ≫ (Sp R).isoSpec.hom) := by
    rw [← Scheme.isoSpec_hom_naturality j.fromNormalization]
    infer_instance
  exact IsIso.of_isIso_comp_right j.fromNormalization (Sp R).isoSpec.hom

/-- A finite projection with the genuine generic-fibre isomorphism is
an isomorphism over the DVR when its target is smooth and its source
flat and separated. The inverse is constructed by the universal
property of relative normalization, not by assuming normality of a
new geometric object. -/
theorem finiteProjection_isIso
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (Ga G : Over (Sp R)) (p : Ga ⟶ G)
    [Flat Ga.hom] [IsSeparated Ga.hom] [Smooth G.hom] [IsFinite p.left]
    [IsIso ((Over.pullback (spMap (algebraMap R K))).map p)] :
    IsIso p := by
  let t := spMap (algebraMap R K)
  let Φ := Over.pullback t
  have ht : IsIso t.fromNormalization := fractionField_fromNormalization_isIso R K
  let j : pullback t G.hom ⟶ G.left := pullback.snd t G.hom
  have hjN : IsIso j.fromNormalization := by
    change IsIso (pullback.snd t G.hom).fromNormalization
    rw [← Scheme.Hom.normalizationPullback_snd t G.hom]
    infer_instance
  let q : pullback Ga.hom t ⟶ pullback G.hom t := (Φ.map p).left
  have hq : IsIso q := inferInstanceAs (IsIso ((Over.forget _).map (Φ.map p)))
  have hqfst : q ≫ pullback.fst G.hom t = pullback.fst Ga.hom t ≫ p.left :=
    pullback.lift_fst _ _ _
  let r : pullback t G.hom ⟶ Ga.left :=
    (pullbackSymmetry t G.hom).hom ≫ inv q ≫ pullback.fst Ga.hom t
  have hr : j = r ≫ p.left := by
    dsimp only [j, r]
    simp only [Category.assoc, ← hqfst, IsIso.inv_hom_id_assoc,
      pullbackSymmetry_hom_comp_fst]
  let s : G.left ⟶ Ga.left :=
    inv j.fromNormalization ≫ j.normalizationDesc r p.left hr
  have hs : s ≫ p.left = 𝟙 G.left := by
    dsimp only [s]
    rw [Category.assoc, Scheme.Hom.normalizationDesc_comp, IsIso.inv_hom_id]
  let F : G ⟶ Ga := Over.homMk s (by
    rw [← Over.w p, ← Category.assoc, hs, Category.id_comp])
  have hright : F ≫ p = 𝟙 G := Over.OverMorphism.ext hs
  have hleft : p ≫ F = 𝟙 Ga := by
    apply fractionField_map_injective R K
    change Φ.map (p ≫ F) = Φ.map (𝟙 Ga)
    have hright' : Φ.map F ≫ Φ.map p = 𝟙 (Φ.obj G) :=
      (Φ.map_comp F p).symm.trans ((congrArg (fun g => Φ.map g) hright).trans (Φ.map_id G))
    calc
      Φ.map (p ≫ F) = Φ.map p ≫ Φ.map F := Φ.map_comp p F
      _ = 𝟙 (Φ.obj Ga) := by
        apply (cancel_mono (Φ.map p)).1
        rw [Category.assoc, hright', Category.comp_id, Category.id_comp]
      _ = Φ.map (𝟙 Ga) := (Φ.map_id Ga).symm
  exact ⟨⟨F, hleft, hright⟩⟩

private theorem map_graph_section {C D : Type*} [Category C] [Category D] (Φ : C ⥤ D)
    {X A B : C} (p : X ⟶ A) [IsIso p] (q : X ⟶ B) (f : Φ.obj A ⟶ Φ.obj B)
    (e : Φ.obj X ≅ Φ.obj A) (hp : Φ.map p = e.hom) (hq : Φ.map q = e.hom ≫ f) :
    Φ.map (inv p ≫ q) = f := by
  have h : Φ.map q = Φ.map p ≫ f := hq.trans (congrArg (fun g => g ≫ f) hp.symm)
  rw [Functor.map_comp, Functor.map_inv, h, IsIso.inv_hom_id_assoc]

private theorem elliptic_graph_projection_isIso
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (G Ga : Over (Sp R)) [GrpObj G] [GrpObj Ga] [IsCommMonObj G] [IsCommMonObj Ga]
    [IsProper G.hom] [Smooth G.hom] [Flat Ga.hom]
    (V : _root_.WeierstrassCurve R) [V.IsElliptic]
    (io : Ga ⟶ G ⊗ schemeOver V) [IsClosedImmersion io.left] [IsMonHom io]
    [IsIso ((Over.pullback (spMap (algebraMap R K))).map (io ≫ fst G (schemeOver V)))] :
    IsIso (io ≫ fst G (schemeOver V)) := by
  let H := schemeOver V
  have hHp : IsProper H.hom := inferInstanceAs (IsProper (toSpec V))
  have hproj : IsProper (fst G H).left :=
    inferInstanceAs (IsProper (pullback.fst G.hom H.hom))
  have hprod : IsProper (G ⊗ H).hom :=
    inferInstanceAs (IsProper (pullback.fst G.hom H.hom ≫ G.hom))
  have hGap : IsProper Ga.hom := by rw [← Over.w io]; infer_instance
  let p : Ga ⟶ G := io ≫ fst G H
  have hproper : IsProper p.left := by
    dsimp only [p]
    rw [Over.comp_left]
    infer_instance
  have hqf : LocallyQuasiFinite p.left :=
    elliptic_graph_projection_locallyQuasiFinite R K G Ga V io
  have hfin : IsFinite p.left := IsFinite.of_isProper_of_locallyQuasiFinite p.left
  exact finiteProjection_isIso R K Ga G p

private theorem unique_extension_from_graph
    (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (G H Ga : Over (Sp R)) [MonObj G] [MonObj H] [Flat G.hom] [IsSeparated H.hom]
    (p : Ga ⟶ G) [IsIso p] (q : Ga ⟶ H)
    (f : (Over.pullback (spMap (algebraMap R K))).obj G ⟶
      (Over.pullback (spMap (algebraMap R K))).obj H) [IsMonHom f]
    (e : (Over.pullback (spMap (algebraMap R K))).obj Ga ≅
      (Over.pullback (spMap (algebraMap R K))).obj G)
    (hp : (Over.pullback (spMap (algebraMap R K))).map p = e.hom)
    (hq : (Over.pullback (spMap (algebraMap R K))).map q = e.hom ≫ f) :
    ∃! F : G ⟶ H, IsMonHom F ∧ (Over.pullback (spMap (algebraMap R K))).map F = f := by
  let t := spMap (algebraMap R K)
  let F := inv p ≫ q
  have hF : (Over.pullback t).map F = f := map_graph_section (Over.pullback t) p q f e hp hq
  have ht : IsSchemeTheoreticallyDominant t := schemeTheoreticallyDominant_fractionField R K
  have hFK : IsMonHom ((Over.pullback t).map F) := hF.symm ▸ (inferInstance : IsMonHom f)
  exact ⟨F, ⟨isMonHom_of_pullback_of_flat t F, hF⟩, fun F' hF' =>
    fractionField_map_injective R K (Y := G) (X := H) (hF'.2.trans hF.symm)⟩

private theorem existsUnique_hom_to_elliptic_extension_dvr
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [IsProper G.hom] [Smooth G.hom]
    (V : _root_.WeierstrassCurve R) [V.IsElliptic]
    (f : (Over.pullback (spMap (algebraMap R K))).obj G ⟶
      (Over.pullback (spMap (algebraMap R K))).obj (schemeOver V)) [IsMonHom f] :
    ∃! F : G ⟶ schemeOver V,
      IsMonHom F ∧ (Over.pullback (spMap (algebraMap R K))).map F = f := by
  let H := schemeOver V
  have hHp : IsProper H.hom := inferInstanceAs (IsProper (toSpec V))
  obtain ⟨Ga, grp, io, e, hcomm, hclosed, hflat, hmon, _, hp, hq⟩ :=
    exists_commutative_flat_graph R K G H f
  let _ : GrpObj Ga := grp
  have hpK : IsIso ((Over.pullback (spMap (algebraMap R K))).map (io ≫ fst G H)) :=
    hp.symm ▸ e.isIso_hom
  have hpiso : IsIso (io ≫ fst G H) := elliptic_graph_projection_isIso R K G Ga V io
  exact unique_extension_from_graph R K G H Ga (io ≫ fst G H) (io ≫ snd G H) f e hp hq

/-- The finite graph projection over the DVR gives the unique extension of the
generic homomorphism between the two original elliptic equations. -/
theorem existsUnique_elliptic_hom_extension_dvr
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (W V : _root_.WeierstrassCurve R) [W.IsElliptic] [V.IsElliptic]
    (f : (Over.pullback (spMap (algebraMap R K))).obj (schemeOver W) ⟶
      (Over.pullback (spMap (algebraMap R K))).obj (schemeOver V)) [IsMonHom f] :
    ∃! F : schemeOver W ⟶ schemeOver V,
      IsMonHom F ∧ (Over.pullback (spMap (algebraMap R K))).map F = f := by
  have hproper : IsProper (schemeOver W).hom := inferInstanceAs (IsProper (toSpec W))
  have hsmooth : Smooth (schemeOver W).hom := inferInstanceAs (Smooth (toSpec W))
  exact existsUnique_hom_to_elliptic_extension_dvr R K (schemeOver W) V f

/-- The integral tangent coordinate of the extension is supplied by
the actual dual-number vector of the target equation. This is the
coordinate required for local reverse-isogeny integrality. -/
theorem exists_elliptic_extension_integral_coordinate
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (W V : _root_.WeierstrassCurve R) [W.IsElliptic] [V.IsElliptic]
    (f : (Over.pullback (spMap (algebraMap R K))).obj (schemeOver W) ⟶
      (Over.pullback (spMap (algebraMap R K))).obj (schemeOver V)) [IsMonHom f] :
    ∃ (F : schemeOver W ⟶ schemeOver V) (c : R),
      IsMonHom F ∧ (Over.pullback (spMap (algebraMap R K))).map F = f ∧
      (integralVector W ≫ F).left = vec V c := by
  obtain ⟨F, ⟨hF, hgeneric⟩, _⟩ := existsUnique_elliptic_hom_extension_dvr R K W V f
  have hv : IsTangent (integralVector W ≫ F) := by
    unfold IsTangent
    rw [Over.comp_left, ← Category.assoc, integralVector_isTangent W]
    exact congrArg Over.Hom.left (IsMonHom.one_hom F)
  obtain ⟨c, hc, _⟩ := integral_tangent_coordinate V (integralVector W ≫ F) hv
  exact ⟨F, c, hF, hgeneric, hc⟩

end RHLean.Geometry.NativeCM.SchemeTheory.IntegralExtension

end
