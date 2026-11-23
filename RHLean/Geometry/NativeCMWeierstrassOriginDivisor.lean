import RHLean.Geometry.NativeCMLineBundleRegularSection
import RHLean.Geometry.NativeCMWeierstrassSectionPoints

/-!
# The original zero section as a regular origin divisor

Native declaration cut from Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`.

- `src/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/IsRegularFnIffOfIsAffineOpen.lean`
- `src/Development/AbelianVarietyTheory/Definitions/AbelianSchemeLaws/SpecMapAwayFnEquivAwayChart.lean`
- `src/Development/AbelianVarietyTheory/Definitions/AbelianSchemeLaws/ExistsUniqueEqConstMulOriginSec.lean`

The canonical origin section is regular on every restricted chart, and its
scheme-theoretic vanishing condition is exactly factorization through the
actual identity section. No set-theoretic replacement of the zero scheme is used.
The source archive states no license; attribution is retained without assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite

namespace RHLean.Geometry.NativeCM.SchemeTheory

open SectionPoints Cartier

variable {X Y : Scheme.{0}}

theorem evalPt_eq_zero_iff {A : Type} [CommRing A] (x : Sp A ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U)
    (a : Γ(X, U)) : evalPt x U h a = 0 ↔ (x.app U).hom a = 0 := by
  have e : evalPt x U h a = (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
      (resG _ h ((x.app U).hom a)) := rfl
  rw [e, map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of A)).hom).1]
  refine ⟨fun h0 => ?_, fun h0 => by rw [h0, map_zero]⟩
  have := congrArg (resG _ (le_top : x ⁻¹ᵁ U ≤ ⊤)) h0
  rwa [resG_resG, resG_self, map_zero] at this


theorem resG_injective_of_eq_basicOpen {U V : X.Opens} (hU : IsAffineOpen U) {a : Γ(X, U)}
    (ha : a ∈ nonZeroDivisors Γ(X, U)) (hV : V = X.basicOpen a) (h : V ≤ U) :
    Function.Injective (resG X h) := by
  subst hV
  have := hU.isLocalization_basicOpen a
  exact IsLocalization.injective Γ(X, X.basicOpen a) (Submonoid.powers_le.2 ha)


namespace WeierstrassCurve

variable {R : Type} [CommRing R] (W : WeierstrassCurve R)

def originFnEquiv : OriginRing W ≃+* Γ(scheme W, coordOpen W 1) :=
  (awayEquivOrigin W).symm.trans (awayFnEquiv W 1)

@[simp] theorem originFnEquiv_originZ : originFnEquiv W (originZ W) = -ratio W 1 0 := by
  have : awayEquivOrigin W (-awayCoord W 1 0) = originZ W :=
    ((map_neg _ _).trans (mul_neg_one _).symm).trans (awayEval_awayCoord_mul W 1 (algebraMap R _)
      ![originZ W, -1, originW W] (equation_originZ_originW W) isUnit_one.neg 0)
  simp [originFnEquiv, ← this]

@[simp] theorem originFnEquiv_originW : originFnEquiv W (originW W) = -ratio W 1 2 := by
  have : awayEquivOrigin W (-awayCoord W 1 2) = originW W :=
    ((map_neg _ _).trans (mul_neg_one _).symm).trans (awayEval_awayCoord_mul W 1 (algebraMap R _)
      ![originZ W, -1, originW W] (equation_originZ_originW W) isUnit_one.neg 2)
  simp [originFnEquiv, ← this]

@[simp] theorem originFnEquiv_algebraMap (r : R) :
    originFnEquiv W (algebraMap R _ r) = constOn W _ r := by
  have : awayEquivOrigin W (awayConst W 1 r) = algebraMap R _ r :=
    awayEval_awayConst W 1 (algebraMap R _) ![originZ W, -1, originW W]
      (equation_originZ_originW W) isUnit_one.neg r
  simp [originFnEquiv, ← this]

theorem originW_mem_nonZeroDivisors : originW W ∈ nonZeroDivisors (OriginRing W) := by
  have h : IsSMulRegular (OriginRing W) (Polynomial.X : Polynomial R) :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors (Polynomial.monic_X (R := R)).mem_nonZeroDivisors
  refine mem_nonZeroDivisors_iff_left.2 fun a ha => h ?_
  have e : algebraMap (Polynomial R) (OriginRing W) Polynomial.X = originW W :=
    AdjoinRoot.algebraMap_eq (originPolynomial W) ▸ rfl
  simp only [Algebra.smul_def, e, ha, mul_zero]

theorem isRegularFn_ratio_one_two : Cartier.IsRegularFn (ratio W 1 2) := by
  rw [Cartier.isRegularFn_iff_of_isAffineOpen (isAffineOpen_coordOpen W 1)]
  refine mem_nonZeroDivisors_iff_left.2 fun a ha => ?_
  obtain ⟨a, rfl⟩ := (originFnEquiv W).surjective a
  have : originW W * a = 0 := (originFnEquiv W).injective (by
    rw [map_mul, originFnEquiv_originW, neg_mul, ha, neg_zero, map_zero])
  rw [mem_nonZeroDivisors_iff_left.1 (originW_mem_nonZeroDivisors W) a this, map_zero]

theorem isRegularFn_originParam : Cartier.IsRegularFn (originParam W) := by
  have h := ((isRegularFn_ratio_one_two W).resG (originOpen_le W)).mul
    (.of_isUnit (isUnit_originCofactor (le_refl (originOpen W))))
  rw [resG_ratioOn, ratioOn_mul_originCofactor] at h
  exact h.of_dvd (dvd_pow_self _ three_ne_zero)

theorem resG_originOpen_injective :
    Function.Injective (resG _ (inf_le_left : originOpen W ⊓ coordOpen W 2 ≤ originOpen W)) :=
  resG_injective_of_eq_basicOpen (isAffineOpen_originOpen W) (isRegularFn_originParam W).mem
    (basicOpen_originParam W).symm _

theorem isRegularSec_originSec : Cartier.IsRegularSec (originSec W)
  | true => isRegularFn_originParam W
  | false => .of_isUnit isUnit_one

theorem evalPt_zero_ratioOn {U : (scheme W).Opens} (hU : U ≤ coordOpen W 1)
    (h : ⊤ ≤ zero W ⁻¹ᵁ U) (j : Fin 3) :
    evalPt (zero W) U h (ratioOn W U 1 hU j) = ![0, 1, 0] j :=
  (mul_one _).symm.trans (evalPt_ptHom_ratioOn_mul (algebraMap R R) ![0, 1, 0]
    (isUnimodularSol_zero _) hU h j)

variable {W} in

theorem evalPt_zero_constOn {U : (scheme W).Opens} (h : ⊤ ≤ zero W ⁻¹ᵁ U) (r : R) :
    evalPt (zero W) U h (constOn W U r) = r :=
  evalPt_constOn (ρ := RingHom.id R) ((zero_toSpec W).trans (Spec.map_id _).symm) h r

variable {W} in

theorem evalPt_zero_originCofactor {U : (scheme W).Opens} (hU : U ≤ coordOpen W 1)
    (h : ⊤ ≤ zero W ⁻¹ᵁ U) : evalPt (zero W) U h (originCofactor W U hU) = 1 := by
  simp [originCofactor, evalPt_zero_ratioOn]

theorem zero_preimage_originOpen : zero W ⁻¹ᵁ originOpen W = ⊤ := by
  refine top_le_iff.1 fun p _ => ?_
  rcases (originOpen_sup_coordOpen_two W).ge (Set.mem_univ (zero W p)) with h | h
  · exact h
  · exact absurd ((zero_preimage_coordOpen_two W).le h) id

abbrev originValue : Γ(scheme W, originOpen W) →+* R :=
  evalPt (zero W) (originOpen W) (zero_preimage_originOpen W).ge

theorem originValue_originParam : originValue W (originParam W) = 0 :=
  evalPt_zero_ratioOn W (originOpen_le W) (zero_preimage_originOpen W).ge 0

variable {W} in

theorem eq_spMap_zero_of_evalPt {A : Type} [CommRing A] {x : Sp A ⟶ scheme W} {ρ : R →+* A}
    (hx : x ≫ toSpec W = spMap ρ) (h : ⊤ ≤ x ⁻¹ᵁ originOpen W)
    (hz : evalPt x _ h (originParam W) = 0) : x = spMap ρ ≫ zero W := by
  have hw : evalPt x _ h (ratioOn W _ 1 (originOpen_le W) 2) = 0 := by
    have := congrArg (evalPt x _ h) (ratioOn_mul_originCofactor (originOpen_le W))
    rw [map_mul, map_pow, hz, zero_pow three_ne_zero] at this
    exact ((isUnit_originCofactor le_rfl).map (evalPt x _ h)).mul_left_eq_zero.1 this
  obtain ⟨hP, e⟩ := eq_ptHom_evalPt hx (originOpen_le W) h (P := ![0, 1, 0]) fun j => by
    fin_cases j
    · exact hz
    · exact (congrArg _ (ratioOn_self _)).trans (map_one _)
    · exact hw
  exact e.trans (SpecMap_zero W ρ).symm

theorem eq_comp_zero_iff {T : Scheme.{0}} (g : T ⟶ scheme W) : g = g ≫ toSpec W ≫ zero W ↔
    ⊤ ≤ g ⁻¹ᵁ originOpen W ∧ (g.app (originOpen W)).hom (originParam W) = 0 := by
  constructor
  · intro e
    have key : ∀ q : T ⟶ Sp R, ⊤ ≤ (q ≫ zero W) ⁻¹ᵁ originOpen W ∧
        ((q ≫ zero W).app (originOpen W)).hom (originParam W) = 0 := fun q => by
      refine ⟨fun t _ => (zero_preimage_originOpen W).ge (Set.mem_univ (q t)), ?_⟩
      have := (evalPt_eq_zero_iff _ _ _).1 (originValue_originParam W)
      exact (congrArg (q.app _).hom this).trans (map_zero _)
    rw [e, ← Category.assoc]
    exact key _
  · rintro ⟨h, hz⟩
    refine T.affineCover.hom_ext _ _ fun i => ?_
    obtain ⟨ρ, hρ⟩ := Spec.map_surjective (T.affineCover.f i ≫ g ≫ toSpec W)
    have h' : ⊤ ≤ (T.affineCover.f i ≫ g) ⁻¹ᵁ originOpen W :=
      fun t _ => h (Set.mem_univ (T.affineCover.f i t))
    have := eq_spMap_zero_of_evalPt (x := T.affineCover.f i ≫ g) (ρ := ρ.hom)
      ((Category.assoc _ _ _).trans hρ.symm) h' ((evalPt_eq_zero_iff _ _ _).2
        ((congrArg ((T.affineCover.f i).app _).hom hz).trans (map_zero _)))
    exact this.trans ((congrArg (· ≫ zero W) hρ).trans ((Category.assoc _ _ _).trans
      (congrArg (_ ≫ ·) (Category.assoc _ _ _))))


end WeierstrassCurve

end RHLean.Geometry.NativeCM.SchemeTheory
