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
    rw [Scheme.Hom.fromNormalization_app j (isAffineOpen_top _)]
    infer_instance
  exact (HasAffineProperty.iff_of_isAffine (P := .isomorphisms _)).mpr
    ⟨isAffine_of_isAffineHom j.fromNormalization, happ⟩

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
    have hright' := congrArg (fun g => Φ.map g) hright
    simp only [Functor.map_comp, Functor.map_id] at hright' ⊢
    apply (cancel_mono (Φ.map p)).1
    rw [Category.assoc, hright', Category.comp_id, Category.id_comp]
  exact ⟨⟨F, hleft, hright⟩⟩

/-- The existing actual graph construction, geometric-kernel theorem
and Mathlib's proper quasi-finite theorem supply the original elliptic
homomorphism extension, with its exact generic map. -/
theorem existsUnique_elliptic_hom_extension_dvr
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (W V : _root_.WeierstrassCurve R) [W.IsElliptic] [V.IsElliptic]
    (f : (Over.pullback (spMap (algebraMap R K))).obj (schemeOver W) ⟶
      (Over.pullback (spMap (algebraMap R K))).obj (schemeOver V)) [IsMonHom f] :
    ∃! F : schemeOver W ⟶ schemeOver V,
      IsMonHom F ∧ (Over.pullback (spMap (algebraMap R K))).map F = f := by
  let G := schemeOver W
  let H := schemeOver V
  let t := spMap (algebraMap R K)
  let Φ := Over.pullback t
  have hGp : IsProper G.hom := inferInstanceAs (IsProper (toSpec W))
  have hHp : IsProper H.hom := inferInstanceAs (IsProper (toSpec V))
  have hGs : Smooth G.hom := inferInstanceAs (Smooth (toSpec W))
  have hHs : Smooth H.hom := inferInstanceAs (Smooth (toSpec V))
  obtain ⟨Ga, grp, io, e, hcomm, hclosed, hflat, hmon, _, hp, hsecond⟩ :=
    exists_commutative_flat_graph R K G H f
  let _ : GrpObj Ga := grp
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
  have hpK : IsIso (Φ.map p) := by
    change IsIso (Φ.map (io ≫ fst G H))
    rw [hp]
    infer_instance
  have hqf : LocallyQuasiFinite p.left :=
    elliptic_graph_projection_locallyQuasiFinite R K G Ga V io
  have hfin : IsFinite p.left := IsFinite.of_isProper_of_locallyQuasiFinite p.left
  have hpiso : IsIso p := finiteProjection_isIso R K Ga G p
  let F : G ⟶ H := inv p ≫ (io ≫ snd G H)
  have hF : Φ.map F = f := by
    dsimp only [F, p]
    rw [Functor.map_comp, Functor.map_inv, hp, hsecond, IsIso.inv_hom_id_assoc]
  have hFmon : IsMonHom F := by
    have ht : IsSchemeTheoreticallyDominant t := schemeTheoreticallyDominant_fractionField R K
    have hFK : IsMonHom (Φ.map F) := by rw [hF]; infer_instance
    exact isMonHom_of_pullback_of_flat t F
  exact ⟨F, ⟨hFmon, hF⟩, fun F' hF' =>
    fractionField_map_injective R K (hF'.2.trans hF.symm)⟩

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
