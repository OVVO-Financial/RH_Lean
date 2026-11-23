import RHLean.Geometry.NativeCMLineBundleGerms
import RHLean.Geometry.NativeCMWeierstrassOriginSections
import RHLean.Geometry.NativeCMWeierstrassOriginSymmetry

/-!
# Base-change sections of the actual origin line bundle

Native declaration cuts from Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`.

- `src/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/SabPull.lean`
- `src/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/IsRegularFnIffOfIsAffineOpen.lean`
- `src/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/MemNonzeroLocusIffPowFn.lean`
- `src/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/AwayToSectionFromZero.lean`
- `src/Development/AbelianVarietyTheory/Definitions/AbelianSchemeLaws/SpecMapAwayFnEquivAwayChart.lean`
- `src/Development/AbelianVarietyTheory/Definitions/AbelianSchemeLaws/ExistsUniqueEqConstMulOriginSec.lean`
- `src/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/OriginLineBundlePolarisation.lean`

The explicit projective base-change map identifies the original origin atlas
and canonical section over every commutative base ring. Uniqueness of global
sections is then transported through the actual pullback square. In particular,
every pulled-back global section vanishes along the actual zero section.
The source archive states no license; attribution is retained without assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open scoped BigOperators

namespace RHLean.Geometry.NativeCM.SchemeTheory

variable {X X' Y Y' Z : Scheme.{0}}

open LBGerm

namespace Cartier

theorem pull_U (L : LB X) (φ : Y ⟶ X) (j : PUnit → L.ι) : (L.pull φ).U j = φ ⁻¹ᵁ L.U (j ⟨⟩) :=
  le_antisymm (LB.wchart_le L (fun _ => φ) j ⟨⟩) fun _ hy => Set.mem_iInter.2 fun _ => hy

theorem pull_g (L : LB X) (φ : Y ⟶ X) (j j' : PUnit → L.ι) :
    (L.pull φ).g j j' = res (LB.wchart_inter_le L (fun _ => φ) j j' ⟨⟩)
      (pullU φ _ (L.g (j ⟨⟩) (j' ⟨⟩))) := by
  change LB.lcg L (fun _ : PUnit => φ) (fun _ => 1) j j' = _
  rw [LB.lcg, Fintype.prod_unique, zpow_one]

def secPull {L : LB X} (s : L.Sec) (φ : Y ⟶ X) : (L.pull φ).Sec where
  f j := resG Y (pull_U L φ j).le ((φ.app _).hom (s.f (j ⟨⟩)))
  compat j j' := by
    change PUnit → L.ι at j j'
    have hs : resG X inf_le_left (s.f (j ⟨⟩)) =
        (L.g (j ⟨⟩) (j' ⟨⟩) : Γ(X, L.U (j ⟨⟩) ⊓ L.U (j' ⟨⟩))) *
          resG X inf_le_right (s.f (j' ⟨⟩)) := s.compat (j ⟨⟩) (j' ⟨⟩)
    have e := congrArg (fun a => resG Y (LB.wchart_inter_le L (fun _ => φ) j j' ⟨⟩)
      ((φ.app _).hom a)) hs
    simp only [map_mul] at e
    rw [app_resG, app_resG, resG_resG, resG_resG] at e
    refine (resG_resG _ _ _).trans (e.trans ?_)
    exact congrArg₂ (· * ·) (congrArg Units.val (pull_g L φ j j')).symm (resG_resG _ _ _).symm

end Cartier

structure ChartPull (A' : LB Y') (A : LB Y) (h : Y' ⟶ Y) where
  idx : A'.ι → A.ι
  le : ∀ i, A'.U i ≤ h ⁻¹ᵁ A.U (idx i)
  g : ∀ (y : Y') i j, y ∈ A'.U i → y ∈ A'.U j →
    gm (𝟙 Y') y (A'.U i ⊓ A'.U j) (A'.g i j) = gm h y (A.U (idx i) ⊓ A.U (idx j)) (A.g (idx i) (idx j))

theorem gm_pull_g {Z : Scheme.{0}} (L : LB X) (F : X' ⟶ X) (r : Z ⟶ X') (z : Z) (J J' : PUnit → L.ι)
    (hj : r z ∈ (L.pull F).U J) (hj' : r z ∈ (L.pull F).U J') :
    gm r z ((L.pull F).U J ⊓ (L.pull F).U J') ((L.pull F).g J J') =
      gm (r ≫ F) z _ (L.g (J PUnit.unit) (J' PUnit.unit)) :=
  (gm_linComb L (fun _ : PUnit => F) (fun _ => 1) r z J J' hj hj').trans (by rw [Fintype.prod_unique, zpow_one])

theorem mem_pull {L : LB X} {F : Y ⟶ X} {y : Y} {J : PUnit → L.ι} :
    y ∈ (L.pull F).U J ↔ F y ∈ L.U (J PUnit.unit) :=
  ⟨fun h => Set.mem_iInter.1 h PUnit.unit, fun h => Set.mem_iInter.2 fun _ => h⟩

section ChartSection

variable {A' : LB Y'} {A : LB Y} {h : Y' ⟶ Y}

def chartSec (a : ChartPull A' A h) (s : A.Sec) : A'.Sec :=
  secOfGerm (fun i => (h.appLE _ _ (a.le i)).hom (s.f (a.idx i))) fun y i j hi hj => by
    rw [a.g y i j hi hj, gs_appLE h _ _ _ (𝟙 _) y hi, gs_appLE h _ _ _ (𝟙 _) y hj, Category.id_comp]
    exact gs_compat s h y (a.le i hi) (a.le j hj)

theorem chartSec_f (a : ChartPull A' A h) (s : A.Sec) (i : A'.ι) :
    (chartSec a s).f i = (h.appLE _ _ (a.le i)).hom (s.f (a.idx i)) := rfl

end ChartSection

theorem appLE_injective_of_isIso (e : Y ⟶ X) [IsIso e] {U : X.Opens} {V : Y.Opens}
    (hV : V = e ⁻¹ᵁ U) : Function.Injective (e.appLE U V hV.le).hom := by
  subst hV
  rw [← Scheme.Hom.app_eq_appLE]
  exact (ConcreteCategory.bijective_of_isIso (e.app U)).1

namespace LBGerm

variable {V : Type} [CommRing V]

def cst (q : Z ⟶ Sp V) (z : Z) (a : V) : Z.presheaf.stalk z :=
  gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a)

theorem gs_constFn (p : X ⟶ Sp V) (W : X.Opens) (r : Z ⟶ X) (z : Z)
    (hz : r z ∈ W) (a : V) : gs r z W (constFn p W a) = cst (r ≫ p) z a := by
  unfold constFn cst
  exact gs_appLE p ⊤ W le_top r z hz _

end LBGerm

namespace ProjFrac

variable {A σ B τ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {ℬ : ℕ → τ} [GradedRing ℬ]
  (φ : 𝒜 →+*ᵍ ℬ) (hφ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map φ)

theorem map_app_frac (U : (Proj 𝒜).Opens) {d : ℕ} (a b : A) (ha : a ∈ 𝒜 d) (hb : b ∈ 𝒜 d)
    (hU : U ≤ Proj.basicOpen 𝒜 b) :
    ((Proj.map φ hφ).app U).hom (frac 𝒜 U a b ha hb hU) =
      frac ℬ (Proj.map φ hφ ⁻¹ᵁ U) (φ a) (φ b) (φ.2 ha) (φ.2 hb) (fun _ hx => hU hx) := by
  refine Subtype.ext <| funext fun p ↦ ?_
  change HomogeneousLocalization.mk _ = .mk _
  ext
  simp

end ProjFrac

namespace WeierstrassCurve

open ProjFrac

variable {R : Type} [CommRing R] (W : WeierstrassCurve R)

section BaseChange

variable {R' : Type} [CommRing R'] {W' : WeierstrassCurve R'} (f : R →+* R') (h : W.map f = W')

theorem mapHom_app_ratioOn {U : (scheme W).Opens} {i : Fin 3} (hi : U ≤ coordOpen W i) (j : Fin 3) :
    ((mapHom W f h).app U).hom (ratioOn W U i hi j) = ratioOn W' (mapHom W f h ⁻¹ᵁ U) i
      (((mapHom W f h).preimage_mono hi).trans (mapHom_preimage_coordOpen W f h i).le) j :=
  (map_app_frac (gradedMap W f h) (irrelevant_le_map_gradedMap W f h) U _ _ _ _ hi).trans
    (frac_eq (congrArg₂ (· * ·) (homRingMap_coord W f h j) (homRingMap_coord W f h i).symm))

theorem mapHom_app_constOn (U : (scheme W).Opens) (r : R) :
    ((mapHom W f h).app U).hom (constOn W U r) = constOn W' (mapHom W f h ⁻¹ᵁ U) (f r) := by
  refine (app_baseRingHom (mapHom W f h) (toSpec W) U r).trans ?_
  rw [mapHom_toSpec, baseRingHom_comp_SpecMap]
  rfl

theorem mapHom_app_originCofactor {U : (scheme W).Opens} (hU : U ≤ coordOpen W 1) :
    ((mapHom W f h).app U).hom (originCofactor W U hU) = originCofactor W' (mapHom W f h ⁻¹ᵁ U)
      (((mapHom W f h).preimage_mono hU).trans (mapHom_preimage_coordOpen W f h 1).le) := by
  simp only [originCofactor, map_add, map_sub, map_mul, map_pow, map_one, mapHom_app_constOn,
    mapHom_app_ratioOn]
  subst h
  rfl

theorem mapHom_preimage_originOpen : mapHom W f h ⁻¹ᵁ originOpen W = originOpen W' := by
  have e := mapHom_preimage_coordOpen W f h 1
  have e₁ := mapHom_app_originCofactor W f h le_rfl
  rw [← resG_originCofactor le_rfl e.le] at e₁
  refine (Scheme.preimage_basicOpen _ _).trans ((congrArg (scheme W').basicOpen e₁).trans
    (((scheme W').basicOpen_res _ (homOfLE e.le).op).trans ?_))
  exact inf_eq_right.2 ((originOpen_le W').trans e.ge)

theorem mapHom_preimage_originLB_U : ∀ i : Bool,
    mapHom W f h ⁻¹ᵁ (originLB W).U i = (originLB W').U i
  | true => mapHom_preimage_originOpen W f h
  | false => mapHom_preimage_coordOpen W f h 2

theorem mapHom_app_originSec : ∀ i : Bool,
    ((mapHom W f h).app ((originLB W).U i)).hom ((originSec W).f i) =
      resG _ (mapHom_preimage_originLB_U W f h i).le ((originSec W').f i)
  | true => mapHom_app_ratioOn W f h (originOpen_le W) 0
  | false => (map_one _).trans (map_one _).symm

theorem gs_mapHom_originSec (i : Bool) (y : scheme W') (hy : y ∈ (originLB W').U i) :
    gs (mapHom W f h) y _ ((originSec W).f i) = gs (𝟙 _) y _ ((originSec W').f i) := by
  have hy' := (mapHom_preimage_originLB_U W f h i).ge hy
  have := gs_pull (𝟙 _) (mapHom W f h) y _ hy' ((originSec W).f i)
  rw [Category.id_comp, mapHom_app_originSec] at this
  exact this.symm.trans (gs_res (𝟙 _) y _ hy' _)

def chartPullOriginLB : ChartPull (originLB W') (originLB W) (mapHom W f h) where
  idx i := i
  le i := (mapHom_preimage_originLB_U W f h i).ge
  g y i j hi hj := by
    have hi' := (mapHom_preimage_originLB_U W f h i).ge hi
    have hj' := (mapHom_preimage_originLB_U W f h j).ge hj
    have e₁ := gs_compat (originSec W') (𝟙 _) y hi hj
    have e₂ := gs_compat (originSec W) (mapHom W f h) y hi' hj'
    rw [gs_mapHom_originSec W f h i y hi, gs_mapHom_originSec W f h j y hj, e₁] at e₂
    have hr := Cartier.isRegularFn_iff_germ.1 (isRegularSec_originSec W' j) y hj
    refine Units.ext ((mul_cancel_right_mem_nonZeroDivisors ?_).1 e₂)
    rw [gs_eq (𝟙 _) y _ hj]
    exact hr

end BaseChange

theorem existsUnique_eq_const_mul_secPull {R' : Type} [CommRing R'] {f : R →+* R'} {Y : Scheme.{0}}
    {φ : Y ⟶ scheme W} {p : Y ⟶ Sp R'} (H : IsPullback φ p (toSpec W) (spMap f))
    (s : ((originLB W).pull φ).Sec) :
    ∃! c : R', ∀ j, s.f j = constFn p _ c * (Cartier.secPull (originSec W) φ).f j := by
  let e : scheme (W.map f) ⟶ Y := ((isPullback_mapHom W f rfl).isoIsPullback _ _ H).hom
  have e₁ : e ≫ φ = mapHom W f rfl := IsPullback.isoIsPullback_hom_fst _ _ _ _
  have e₂ : e ≫ p = toSpec (W.map f) := IsPullback.isoIsPullback_hom_snd _ _ _ _
  have hU : ∀ i : Bool, (originLB (W.map f)).U i = e ⁻¹ᵁ ((originLB W).pull φ).U (fun _ => i) :=
    fun i => by
      refine (mapHom_preimage_originLB_U W f rfl i).symm.trans ?_
      rw [← e₁]
      exact congrArg (e ⁻¹ᵁ ·) (Cartier.pull_U (originLB W) φ fun _ => i).symm
  let a : ChartPull (originLB (W.map f)) ((originLB W).pull φ) e :=
    { idx := fun i _ => i
      le := fun i => (hU i).le
      g := fun y i j hi hj => ((chartPullOriginLB W f rfl).g y i j hi hj).trans (by
        rw [gm_pull_g _ φ e y _ _ ((hU i).le hi) ((hU j).le hj), e₁]
        rfl) }
  have key : ∀ (c : R') (i : Bool), (e.appLE _ _ (hU i).le).hom
      (constFn p _ c * (Cartier.secPull (originSec W) φ).f (fun _ => i)) =
      constFn (toSpec (W.map f)) _ c * (originSec (W.map f)).f i := fun c i => fn_ext fun y hy => by
    have hy' := (hU i).le hy
    rw [gs_appLE e _ _ _ (𝟙 _) y hy, Category.id_comp, gs_mul e y _ hy', gs_mul _ y _ hy,
      gs_constFn p _ e y hy', gs_constFn _ _ _ y hy, e₂, Category.id_comp,
      ← gs_mapHom_originSec W f rfl i y hy, ← e₁]
    exact congrArg _ ((gs_res e y _ hy' _).trans (gs_pull e φ y _ (mem_pull.1 hy') _))
  refine (existsUnique_congr fun c => ?_).1
    (existsUnique_eq_const_mul_originSec (W.map f) (chartSec a s))
  exact ⟨fun hc j => appLE_injective_of_isIso e (hU (j ⟨⟩)) ((hc (j ⟨⟩)).trans (key c (j ⟨⟩)).symm),
    fun hc i => (congrArg (e.appLE _ _ (hU i).le).hom (hc fun _ => i)).trans (key c i)⟩

theorem existsUnique_eq_appLE_mul_secPull {T Y : Scheme.{0}} [IsAffine T] {t : T ⟶ Sp R}
    {φ : Y ⟶ scheme W} {p : Y ⟶ T} (H : IsPullback φ p (toSpec W) t)
    (s : ((originLB W).pull φ).Sec) :
    ∃! c : Γ(T, ⊤), ∀ j, s.f j =
      (p.appLE ⊤ _ le_top).hom c * (Cartier.secPull (originSec W) φ).f j := by
  obtain ⟨f, hf⟩ := Spec.map_surjective (T.isoSpec.inv ≫ t)
  have H' : IsPullback φ (p ≫ T.isoSpec.hom) (toSpec W) (spMap f.hom) :=
    H.of_iso (Iso.refl _) (Iso.refl _) T.isoSpec (Iso.refl _) (by simp) (by simp) (by simp)
      ((Category.comp_id _).trans ((Iso.hom_inv_id_assoc T.isoSpec t).symm.trans
        (congrArg (_ ≫ ·) hf.symm)))
  have e : ∀ (U : Y.Opens) (c : Γ(T, ⊤)),
      constFn (p ≫ T.isoSpec.hom) U c = (p.appLE ⊤ U le_top).hom c := fun U c => by
    have e₁ : (p ≫ T.isoSpec.hom).appLE ⊤ U le_top = T.isoSpec.hom.appTop ≫ p.appLE ⊤ U le_top :=
      Scheme.Hom.comp_appLE _ _ _ _ _
    have e₂ : T.isoSpec.hom.appTop = (Scheme.ΓSpecIso Γ(T, ⊤)).hom := Scheme.toSpecΓ_appTop T
    rw [e₂] at e₁
    exact (congrArg (fun q => q.hom ((Scheme.ΓSpecIso Γ(T, ⊤)).inv.hom c)) e₁).trans
      (congrArg (p.appLE ⊤ U le_top).hom (Iso.inv_hom_id_apply (Scheme.ΓSpecIso Γ(T, ⊤)) c))
  simpa only [e] using existsUnique_eq_const_mul_secPull W H' s

theorem appLE_sec_pull_originLB_eq_zero {R : Type} [CommRing R] (W : WeierstrassCurve R)
    {R' : Type} [CommRing R'] {f : Sp R' ⟶ Sp R} {Y : Scheme.{0}} {φ : Y ⟶ scheme W} {q : Y ⟶ Sp R'}
    (H : IsPullback φ q (toSpec W) f) (s : ((originLB W).pull φ).Sec) {T : Scheme.{0}} (t : T ⟶ Y)
    (j : ((originLB W).pull φ).ι) (h : ⊤ ≤ t ⁻¹ᵁ ((originLB W).pull φ).U j)
    (e : t ≫ φ = t ≫ φ ≫ toSpec W ≫ zero W) :
    (t.appLE (((originLB W).pull φ).U j) ⊤ h).hom (s.f j) = 0 := by
  obtain ⟨c, hc, -⟩ := existsUnique_eq_appLE_mul_secPull W H s
  have h' : ⊤ ≤ (t ≫ φ) ⁻¹ᵁ (originLB W).U (j ⟨⟩) :=
    fun p hp => (Cartier.pull_U (originLB W) φ j).le (h hp)
  have h0 := (appLE_originSec_eq_zero_iff W (t ≫ φ) (j ⟨⟩) h').2 (e.trans (Category.assoc _ _ _).symm)
  have h1 : (t.appLE (((originLB W).pull φ).U j) ⊤ h).hom
      ((Cartier.secPull (originSec W) φ).f j) = 0 := by
    refine Eq.trans ?_ h0
    have := Scheme.Hom.appLE_comp_appLE t φ ((originLB W).U (j ⟨⟩)) _ ⊤
      (Cartier.pull_U (originLB W) φ j).le h
    exact congrArg (fun g => g.hom ((originSec W).f (j ⟨⟩))) this
  rw [hc j, map_mul, h1, mul_zero]

end WeierstrassCurve

end RHLean.Geometry.NativeCM.SchemeTheory
