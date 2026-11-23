import RHLean.Geometry.NativeCMWeierstrassOriginBundle
import RHLean.Geometry.NativeCMWeierstrassIntegralTangent

/-!
# Evaluate the actual origin-chart sections at scheme points

Native declaration cut from Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`.

- `src/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TangentBijectionOfValues.lean`
- `src/Development/AbelianVarietyTheory/Definitions/AbelianSchemeLaws/SpecMapAwayFnEquivAwayChart.lean`

The evaluation map is induced by the actual scheme morphism and the Spec
section equivalence. It recovers the literal projective coordinates and the
structure-map coefficients, including over nonreduced rings.
The source archive states no license; attribution is retained without assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite

namespace RHLean.Geometry.NativeCM.SchemeTheory

def constFn {A : Type} [CommRing A] {X : Scheme.{0}}
    (p : X ⟶ Sp A) (U : X.Opens) (a : A) : Γ(X, U) :=
  (p.appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)

namespace SectionPoints

variable {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}}

def evalPt (x : Sp R ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(X, U) →+* R :=
  (x.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom

theorem evalPt_res (x : Sp R ⟶ X) {U V : X.Opens} (e : V ≤ U) (hU : ⊤ ≤ x ⁻¹ᵁ U)
    (hV : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(X, U)) : evalPt x V hV (resG X e f) = evalPt x U hU f := by
  have := congrArg (fun φ => ((φ ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom f))
    (x.map_appLE hV (homOfLE e).op)
  exact this

theorem evalPt_spMap_comp (φ : R →+* R') (x : Sp R ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ U) (f : Γ(X, U)) :
    evalPt (spMap φ ≫ x) U h' f = φ (evalPt x U h f) := by
  have e1 : (spMap φ ≫ x).appLE U ⊤ h' = x.appLE U ⊤ h ≫ (spMap φ).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  have e2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  unfold evalPt
  rw [e1, Category.assoc, e2]
  rfl

theorem eq_spec_fromSpec {U : X.Opens} (hU : IsAffineOpen U) (x : Sp R ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ U) :
    x = Spec.map (CommRingCat.ofHom (evalPt x U h)) ≫ hU.fromSpec := by
  have := IsAffineOpen.SpecMap_appLE_fromSpec x hU (isAffineOpen_top _) h
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at this
  unfold evalPt
  rw [CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, this, ← Category.assoc,
    ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.id_comp]

theorem ext_evalPt {U : X.Opens} (hU : IsAffineOpen U) {x y : Sp R ⟶ X} (hx : ⊤ ≤ x ⁻¹ᵁ U)
    (hy : ⊤ ≤ y ⁻¹ᵁ U) (e : evalPt x U hx = evalPt y U hy) : x = y := by
  exact (eq_spec_fromSpec hU x hx).trans (e ▸ (eq_spec_fromSpec hU y hy).symm)

theorem exists_evalPt_eq {U : X.Opens} (hU : IsAffineOpen U) (ψ : Γ(X, U) →+* R) :
    ∃ (x : Sp R ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ U), evalPt x U h = ψ := by
  have h : ⊤ ≤ (Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec) ⁻¹ᵁ U := by
    rw [Scheme.Hom.comp_preimage, hU.fromSpec_preimage_self]
    exact le_rfl
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec, h, ?_⟩
  have := eq_spec_fromSpec hU _ h
  rw [cancel_mono] at this
  have := Spec.map_injective this
  exact (congrArg CommRingCat.Hom.hom this).symm

theorem evalPt_constFn {k : Type} [CommRing k] (p : X ⟶ Sp k) (x : Sp R ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (a : k) :
    evalPt x U h (constFn p U a) = evalPt (x ≫ p) ⊤ le_rfl ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a) := by
  have := Scheme.Hom.appLE_comp_appLE x p ⊤ U ⊤ (fun _ _ => trivial) h
  unfold evalPt constFn
  rw [← this]
  rfl

theorem evalPt_spMap (φ : R →+* R') (a : R) :
    evalPt (spMap φ) ⊤ le_rfl ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) = φ a := by
  have := evalPt_spMap_comp φ (𝟙 (Sp R)) ⊤ le_rfl le_rfl ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)
  simp only [Category.comp_id] at this
  rw [this]
  congr 1
  have e : Scheme.Hom.appLE (𝟙 (Sp R)) ⊤ ⊤ le_rfl = 𝟙 _ := by
    simp [Scheme.Hom.appLE]
  unfold evalPt
  rw [e, Category.id_comp]
  exact Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of R)) a

theorem eq_spMap_of_evalPt {k : Type} [CommRing k] (y : Sp R ⟶ Sp k) (φ : k →+* R)
    (h : ∀ a, evalPt y ⊤ le_rfl ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a) = φ a) :
    y = spMap φ := by
  refine ext_evalPt (isAffineOpen_top _) le_rfl le_rfl (RingHom.ext fun b => ?_)
  obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv).2 b
  exact (h a).trans (evalPt_spMap φ a).symm


end SectionPoints

namespace WeierstrassCurve

open SectionPoints

variable {R : Type} [CommRing R] (W : WeierstrassCurve R)

theorem constOn_apply (U : (scheme W).Opens) (r : R) :
    constOn W U r = constFn (toSpec W) U r := rfl

theorem SpecMap_awayFnEquiv_awayChart (i : Fin 3) :
    spMap (awayFnEquiv W i : AwayRing W i →+* Γ(scheme W, coordOpen W i)) ≫ awayChart W i =
      (isAffineOpen_coordOpen W i).fromSpec := by
  have h := Proj.basicOpenIsoSpec_hom (grading W) (coord W i) (coord_mem W i) one_pos
  have hU := Proj.isAffineOpen_basicOpen (grading W) (coord W i) (coord_mem W i) one_pos
  change Spec.map (Proj.awayToSection (grading W) (coord W i)) ≫
    Proj.awayι (grading W) (coord W i) (coord_mem W i) one_pos = hU.fromSpec
  rw [Proj.awayι, IsAffineOpen.fromSpec, ← Category.assoc]
  congr 1
  rw [Iso.comp_inv_eq, h, Iso.eq_inv_comp]
  rfl

theorem fromSpec_coordOpen_eq_ptHom (i : Fin 3) :
    (isAffineOpen_coordOpen W i).fromSpec = ptHom W (constOn W (coordOpen W i)) (ratio W i)
      (.of_isUnit (equation_ratioOn le_rfl) i (by simp)) := by
  rw [← SpecMap_awayFnEquiv_awayChart, SpecMap_awayChart]
  exact ptHom_congr W _ _ _ (RingHom.ext (awayFnEquiv_awayConst W i))
    (funext (awayFnEquiv_awayCoord W i)) _

section

variable {W} {A : Type} [CommRing A]

theorem evalPt_constOn {x : Sp A ⟶ scheme W} {ρ : R →+* A} (hx : x ≫ toSpec W = spMap ρ)
    {U : (scheme W).Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (r : R) : evalPt x U h (constOn W U r) = ρ r := by
  rw [constOn_apply, evalPt_constFn]
  exact (congrArg (fun y : Sp A ⟶ Sp R => evalPt y ⊤ le_rfl
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) hx).trans (evalPt_spMap _ r)

theorem eq_ptHom_evalPt {x : Sp A ⟶ scheme W} {ρ : R →+* A} (hx : x ≫ toSpec W = spMap ρ)
    {U : (scheme W).Opens} {i : Fin 3} (hi : U ≤ coordOpen W i) (h : ⊤ ≤ x ⁻¹ᵁ U)
    {P : Fin 3 → A} (hP : ∀ j, evalPt x U h (ratioOn W U i hi j) = P j) :
    ∃ hP, x = ptHom W ρ P hP := by
  have h' : ⊤ ≤ x ⁻¹ᵁ coordOpen W i := h.trans (x.preimage_mono hi)
  have e := eq_spec_fromSpec (isAffineOpen_coordOpen W i) x h'
  rw [fromSpec_coordOpen_eq_ptHom, SpecMap_ptHom] at e
  have e₁ : (evalPt x _ h').comp (constOn W _) = ρ := RingHom.ext (evalPt_constOn hx h')
  have e₂ : evalPt x _ h' ∘ ratio W i = P := funext fun j =>
    (evalPt_res x hi h' h _).symm.trans (hP j)
  subst e₁ e₂
  exact ⟨_, e⟩

theorem evalPt_ptHom_ratioOn_mul (ρ : R →+* A) (P : Fin 3 → A) (hP : IsUnimodularSol (W.map ρ) P)
    {U : (scheme W).Opens} {i : Fin 3} (hi : U ≤ coordOpen W i) (h : ⊤ ≤ ptHom W ρ P hP ⁻¹ᵁ U)
    (j : Fin 3) : evalPt (ptHom W ρ P hP) U h (ratioOn W U i hi j) * P i = P j := by
  have h' : ⊤ ≤ ptHom W ρ P hP ⁻¹ᵁ coordOpen W i := h.trans ((ptHom W ρ P hP).preimage_mono hi)
  have hu : IsUnit (P i) := by
    rw [ptHom_preimage_coordOpen] at h'
    by_contra hu
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (Ideal.span {P i})
      (by rwa [Ne, Ideal.span_singleton_eq_top])
    exact h' (Set.mem_univ (⟨m, hm.isPrime⟩ : PrimeSpectrum A))
      (hle (Ideal.mem_span_singleton_self _))
  have e₁ := eq_spec_fromSpec (isAffineOpen_coordOpen W i) _ h'
  have e₂ := ptHom_eq_awayChart W i ρ P hP hu
  rw [← SpecMap_awayFnEquiv_awayChart, ← Category.assoc, ← Spec.map_comp] at e₁
  have e₃ := congrArg (fun φ => φ.hom (awayCoord W i j))
    (Spec.map_injective ((cancel_mono _).1 (e₁.symm.trans e₂)))
  have e₄ : evalPt _ _ h' (awayFnEquiv W i (awayCoord W i j)) =
      awayEval W i ρ P hP.equation hu (awayCoord W i j) := e₃
  rw [awayFnEquiv_awayCoord] at e₄
  rw [← awayEval_awayCoord_mul W i ρ P hP.equation hu j, ← e₄, ← evalPt_res _ hi h' h]
  rfl

end


end WeierstrassCurve

end RHLean.Geometry.NativeCM.SchemeTheory
