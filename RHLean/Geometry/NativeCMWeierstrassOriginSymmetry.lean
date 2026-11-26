import RHLean.Geometry.NativeCMWeierstrassOriginDivisor
import RHLean.Geometry.NativeCMLineBundleSectionIso

/-!
# Inversion symmetry of the actual origin line bundle

Native declaration cut from Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/OriginLineBundlePolarisation.lean`
and `src/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/SymmetricLineBundleOfRegularSection.lean`.

The actual regular origin section vanishes on a test scheme exactly when
its morphism factors through the identity. This yields a genuine global
unit-transition isomorphism between the origin bundle and its inversion
pullback, on the same integral group scheme. Relative ampleness and the
principal translation kernel are separate subsequent properties.
The source archive states no license; attribution is retained without assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace RHLean.Geometry.NativeCM.SchemeTheory

abbrev identitySection {S : Scheme.{0}} (A : Over S) [GrpObj A] : S ⟶ A.left :=
  η[A].left

namespace SectionSymmetry

theorem appLE_mem_nonZeroDivisors {X Y : Scheme.{0}} (f : Y ⟶ X) [IsOpenImmersion f]
    (W : X.Opens) (a : Γ(X, W))
    (ha : ∀ (V : X.Opens) (h : V ≤ W), resG X h a ∈ nonZeroDivisors Γ(X, V))
    (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ W) : (f.appLE W V h).hom a ∈ nonZeroDivisors Γ(Y, V) := by
  have h' : f ''ᵁ V ≤ W := by
    rintro _ ⟨y, hy, rfl⟩
    exact h hy
  have e : (f.appLE W V h).hom a = (f.appIso V).hom.hom (resG X h' a) := by
    rw [Scheme.Hom.appIso_hom']
    change _ = (X.presheaf.map (homOfLE h').op ≫ f.appLE _ _ _).hom a
    rw [Scheme.Hom.map_appLE]
  rw [e]
  rw [← MulEquivClass.map_nonZeroDivisors (f.appIso V).commRingCatIsoToRingEquiv]
  exact Submonoid.mem_map_of_mem _ (ha _ h')

theorem inv_eq_zero_iff {S : Scheme.{0}} (A : Over S) [GrpObj A]
    {T : Scheme.{0}} (t : T ⟶ A.left) :
    t ≫ (GrpObj.inv : A ⟶ A).left =
        (t ≫ (GrpObj.inv : A ⟶ A).left) ≫ A.hom ≫ identitySection A ↔
      t = t ≫ A.hom ≫ identitySection A := by
  have h1 : (GrpObj.inv : A ⟶ A).left ≫ A.hom = A.hom := Over.w _
  have h2 : identitySection A ≫ (GrpObj.inv : A ⟶ A).left = identitySection A := by
    unfold identitySection
    rw [← Over.comp_left, GrpObj.one_inv]
  have h3 : (t ≫ (GrpObj.inv : A ⟶ A).left) ≫ A.hom ≫ identitySection A =
      (t ≫ A.hom ≫ identitySection A) ≫ (GrpObj.inv : A ⟶ A).left := by
    rw [Category.assoc, reassoc_of% h1]
    simp only [Category.assoc]
    exact congrArg (fun u => t ≫ A.hom ≫ u) h2.symm
  rw [h3]
  exact cancel_mono _

end SectionSymmetry

namespace WeierstrassCurve

/-- The unit generator rigidifies the actual origin bundle along the
literal zero section; every chart containing that section is the origin chart. -/
theorem originLB_rigidified {R : Type} [CommRing R] (W : WeierstrassCurve R) :
    ∃ t : LB.Gen ((originLB W).pull (zero W)), t.IsGen := by
  refine ⟨⟨fun _ => 1⟩, ?_⟩
  intro i j
  have hg : ((originLB W).pull (zero W)).g i j = 1 := by
    apply Units.ext
    apply Cartier.ext_germ
    intro p hp
    have key : ∀ k : PUnit → Bool,
        p ∈ ((originLB W).pull (zero W)).U k → k = fun _ => true := by
      intro k hk
      have hk' : zero W p ∈ (originLB W).U (k PUnit.unit) :=
        Set.mem_iInter.1 hk PUnit.unit
      funext ⟨⟩
      rcases e : k PUnit.unit with _ | _
      · rw [e] at hk'
        exact absurd ((zero_preimage_coordOpen_two W).le hk') id
      · rfl
    obtain rfl := key i hp.1
    obtain rfl := key j hp.2
    have hunit : ((originLB W).pull (zero W)).g (fun _ => true) (fun _ => true) = 1 := by
      change (∏ _ : PUnit, (res _ (pullU (zero W) _
        (1 : Γ(scheme W, originOpen W ⊓ originOpen W)ˣ))) ^ (1 : ℤ)) = 1
      rw [Fintype.prod_unique, _root_.map_one, _root_.map_one, one_zpow]
    rw [hunit]
  change res _ 1 = ((originLB W).pull (zero W)).g i j * res _ 1
  rw [map_one, map_one, hg, _root_.one_mul]

theorem appLE_top_eq_zero_iff {X T : Scheme.{0}} (t : T ⟶ X) {U : X.Opens}
    (h : ⊤ ≤ t ⁻¹ᵁ U) (a : Γ(X, U)) :
    (t.appLE U ⊤ h).hom a = 0 ↔ (t.app U).hom a = 0 := by
  have e : (t.appLE U ⊤ h).hom a = resG _ h ((t.app U).hom a) := rfl
  rw [e]
  refine ⟨fun h0 => ?_, fun h0 => by rw [h0, map_zero]⟩
  have := congrArg (resG _ (le_top : t ⁻¹ᵁ U ≤ ⊤)) h0
  rwa [resG_resG, resG_self, map_zero] at this

/-- Scheme-valued vanishing detects the identity, including nilpotent test
rings. Thus the source's zero-subscheme condition is actually proved. -/
theorem appLE_originSec_eq_zero_iff {R : Type} [CommRing R] (W : WeierstrassCurve R)
    {T : Scheme.{0}} (t : T ⟶ scheme W) (i : (originLB W).ι)
    (h : ⊤ ≤ t ⁻¹ᵁ (originLB W).U i) :
    (t.appLE ((originLB W).U i) ⊤ h).hom ((originSec W).f i) = 0 ↔
      t = t ≫ toSpec W ≫ zero W := by
  rw [appLE_top_eq_zero_iff]
  constructor
  · intro h0
    rcases i with _ | _
    · have h1 : (1 : Γ(T, t ⁻¹ᵁ coordOpen W 2)) = 0 := (map_one _).symm.trans h0
      have hT : IsEmpty T := ⟨fun p => by
        have := congrArg (T.presheaf.germ (t ⁻¹ᵁ coordOpen W 2) p (h (Set.mem_univ p))).hom h1
        rw [map_one, map_zero] at this
        exact absurd this one_ne_zero⟩
      exact (eq_comp_zero_iff W t).2
        ⟨fun p _ => (hT.false p).elim, Cartier.ext_germ fun p _ => (hT.false p).elim⟩
    · exact (eq_comp_zero_iff W t).2 ⟨h, h0⟩
  · intro e
    rcases i with _ | _
    · apply Cartier.ext_germ
      intro p hp
      change t p ∈ coordOpen W 2 at hp
      rw [e] at hp
      exact ((zero_preimage_coordOpen_two W).le hp).elim
    · exact ((eq_comp_zero_iff W t).1 e).2

/-- A genuine global inversion isomorphism, expressed by the unit generator
of the exact difference atlas. Its group object is the one constructed from
this same Weierstrass equation. -/
theorem originLB_inversion_isomorphic {R : Type} [CommRing R] [_root_.IsReduced R]
    (W : WeierstrassCurve R) [W.IsElliptic] :
    ∃ t : LB.Gen (LB.LinComb (originLB W) (K := Fin 2)
      ![(GrpObj.inv : schemeOver W ⟶ schemeOver W).left, 𝟙 (scheme W)] ![1, -1]),
      t.IsGen := by
  have : IsIso (GrpObj.inv : schemeOver W ⟶ schemeOver W).left :=
    inferInstanceAs (IsIso ((Over.forget _).map (GrpObj.inv : schemeOver W ⟶ schemeOver W)))
  have hz : ∀ (T : Scheme.{0}) (t : T ⟶ (schemeOver W).left) (i : (originLB W).ι)
      (h : ⊤ ≤ t ⁻¹ᵁ (originLB W).U i),
      (t.appLE ((originLB W).U i) ⊤ h).hom ((originSec W).f i) = 0 ↔
        t = t ≫ (schemeOver W).hom ≫ identitySection (schemeOver W) := by
    intro T t i h
    change _ ↔ t = t ≫ toSpec W ≫ zero W
    exact appLE_originSec_eq_zero_iff W t i h
  refine SectionIso.exists_isGen_linComb _ _ (originLB W) (originSec W)
    (GrpObj.inv : schemeOver W ⟶ schemeOver W).left (𝟙 _) (originLB_isLB W)
    (fun i V h => SectionSymmetry.appLE_mem_nonZeroDivisors _ _ _
      (isRegularSec_originSec W i) V h)
    (fun i V h => SectionSymmetry.appLE_mem_nonZeroDivisors _ _ _
      (isRegularSec_originSec W i) V h) ?_
  intro T t i j h h'
  rw [hz, hz]
  simpa only [Category.comp_id] using SectionSymmetry.inv_eq_zero_iff (schemeOver W) t

end WeierstrassCurve

end RHLean.Geometry.NativeCM.SchemeTheory
