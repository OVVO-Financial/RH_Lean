import RHLean.Geometry.NativeCMWeierstrassOpenPoint
import RHLean.Geometry.NativeCMWeierstrassGeometricGlue

/-!
# From the actual rational point formula to a global scheme homomorphism

The localization map is extended across its finite kernel by the explicit
translated patch. Both the geometric kernel test and the value of the local
map are proved from the rational point formula. An actual section outside
the denominator is the only translation datum. The resulting morphism is
proved to preserve the group law by reduced geometric-point detection.

This is a native construction from the preceding explicit rational-map,
localization and two-patch lemmas. No global rational-map extension theorem,
scheme CM-action premise or integral extension premise occurs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace RHLean.Geometry.NativeCM.SchemeTheory.WeierstrassCurve

universe u

variable {F k : Type u} [Field F] [Field k] [Algebra F k]
    (W : _root_.WeierstrassCurve F) [W.IsElliptic]

private def multiplicativeHom {P Q : Type u} [AddMonoid P] [AddMonoid Q]
    (φ : P →+ Q) : Multiplicative P →* Multiplicative Q where
  toFun x := Multiplicative.ofAdd (φ x.toAdd)
  map_one' := φ.map_zero
  map_mul' x y := φ.map_add x.toAdd y.toAdd

variable [DecidableEq k]

/-- The same point action expressed on the actual scheme-valued points. -/
def schemePointAction (φ : (W.baseChange k).toAffine.Point →+ (W.baseChange k).toAffine.Point) :
    (specOver F k ⟶ schemeOver W) →* (specOver F k ⟶ schemeOver W) :=
  (affinePointMulEquiv W k).toMonoidHom.comp
    ((multiplicativeHom φ).comp (affinePointMulEquiv W k).symm.toMonoidHom)

theorem schemePointAction_ofAffinePoint
    (φ : (W.baseChange k).toAffine.Point →+ (W.baseChange k).toAffine.Point)
    (P : (W.baseChange k).toAffine.Point) :
    schemePointAction W φ (ofAffinePoint W k P) = ofAffinePoint W k (φ P) := by
  change (affinePointMulEquiv W k)
    (Multiplicative.ofAdd (φ ((affinePointMulEquiv W k).symm
      ((affinePointMulEquiv W k) (Multiplicative.ofAdd P))).toAdd)) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

variable [IsAlgClosed k]

/-- An actual rational point homomorphism, its original formula, and one
point in the denominator open construct a global group-scheme morphism. -/
theorem exists_global_hom_of_rational_point_map
    (α : F) (hα : α ≠ 0) (A D : F[X])
    (hshort : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0)
    (hID : Weierstrass.RationalIdentity W α A D)
    (φ : (W.baseChange k).toAffine.Point →+ (W.baseChange k).toAffine.Point)
    (hφ : ∀ (x y : k) (h : (W.baseChange k).toAffine.Nonsingular x y),
      (aeval x D = 0 → φ (.some x y h) = 0) ∧
      (aeval x D ≠ 0 → ∃ h', φ (.some x y h) =
        .some (aeval x A / aeval x D)
          ((algebraMap F k α)⁻¹ *
            (aeval x (derivative A * D - A * derivative D) / aeval x D ^ 2) * y) h'))
    (x₀ y₀ : F) (h₀ : W.toAffine.Equation x₀ y₀) (hD₀ : D.eval x₀ ≠ 0) :
    ∃ f : schemeOver W ⟶ schemeOver W,
      IsMonHom f ∧ rationalOpenIncl W D ≫ f = rationalOpenHom W α hα A D hshort hID ∧
      ∀ P : (W.baseChange k).toAffine.Point,
        ofAffinePoint W k P ≫ f = ofAffinePoint W k (φ P) := by
  classical
  let Φ := schemePointAction W φ
  have hzero : ofAffinePoint W k (0 : (W.baseChange k).toAffine.Point) = 1 :=
    (affinePointMulEquiv W k).map_one
  have hU : ∀ x : specOver F k ⟶ schemeOver W,
      Φ x ≠ 1 ↔ ∃ z : specOver F k ⟶ specOver F (RationalOpenRing W D),
        z ≫ rationalOpenIncl W D = x := by
    intro x
    constructor
    · intro hx
      obtain ⟨P, rfl⟩ := (affinePointEquiv W k).surjective x
      change schemePointAction W φ (ofAffinePoint W k P) ≠ 1 at hx
      rw [schemePointAction_ofAffinePoint] at hx
      cases P with
      | zero => exact (hx (by rw [map_zero, hzero])).elim
      | some x y h =>
        have hd : aeval x D ≠ 0 := fun hd => hx (by rw [(hφ x y h).1 hd, hzero])
        exact ⟨specOverMap (rationalOpenPoint W D x y h.left hd),
          rationalOpenPoint_incl W D x y h.left hd h⟩
    · rintro ⟨z, rfl⟩
      obtain ⟨g, rfl⟩ := exists_eq_specOverMap z
      obtain ⟨hx, hy, hinc, -⟩ :=
        rationalOpenHom_fieldPoint W α hα A D hshort hID g
      change schemePointAction W φ _ ≠ 1
      rw [hinc, schemePointAction_ofAffinePoint]
      obtain ⟨h', he⟩ := (hφ _ _ hx).2 (rationalOpen_map_denominator W D g).1
      intro hh
      have hh' : φ (.some _ _ hx) = 0 :=
        (affinePointEquiv W k).injective (hh.trans hzero.symm)
      rw [he] at hh'
      cases hh'
  have hfU : ∀ z : specOver F k ⟶ specOver F (RationalOpenRing W D),
      z ≫ rationalOpenHom W α hα A D hshort hID = Φ (z ≫ rationalOpenIncl W D) := by
    intro z
    obtain ⟨g, rfl⟩ := exists_eq_specOverMap z
    obtain ⟨hx, hy, hinc, hmap⟩ :=
      rationalOpenHom_fieldPoint W α hα A D hshort hID g
    change _ = schemePointAction W φ _
    rw [hinc, schemePointAction_ofAffinePoint, hmap]
    obtain ⟨h', he⟩ := (hφ _ _ hx).2 (rationalOpen_map_denominator W D g).1
    rw [he]
  obtain ⟨f, hjf, hf⟩ := GeometricPoints.exists_hom_of_kernel_open
    (rationalOpenIncl W D) (rationalOpenHom W α hα A D hshort hID)
    (rationalOpenSection W D x₀ y₀ h₀ hD₀) Φ hU hfU
  refine ⟨f, GeometricPoints.isMonHom_of_embedded_points f Φ hf, hjf, fun P => ?_⟩
  exact (hf (ofAffinePoint W k P)).trans (schemePointAction_ofAffinePoint W φ P)

end RHLean.Geometry.NativeCM.SchemeTheory.WeierstrassCurve

namespace RHLean.Geometry.NativeCM.Weierstrass

variable {K K' : Type*} [Field K] [Field K']

/-- The exact rational differential identity survives the actual finite
coefficient extension used to obtain a translation point. -/
theorem RationalIdentity.map {W : _root_.WeierstrassCurve K} {α : K} {A D : K[X]}
    (h : RationalIdentity W α A D) (f : K →+* K') :
    RationalIdentity (W.map f) (f α) (A.map f) (D.map f) := by
  unfold RationalIdentity at h ⊢
  have he := congrArg (Polynomial.map f) h
  simpa only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_sub,
    Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X, ← derivative_map,
    map_pow, _root_.WeierstrassCurve.map_a₄, _root_.WeierstrassCurve.map_a₆] using he

variable [DecidableEq K]

/-- Equality of equations identifies the existing point groups without
changing any affine coordinate. -/
def pointCongr {V W : _root_.WeierstrassCurve K} (h : V = W) :
    V.toAffine.Point ≃+ W.toAffine.Point := by
  subst W
  exact AddEquiv.refl _

@[simp] theorem pointCongr_some {V W : _root_.WeierstrassCurve K} (h : V = W)
    {x y : K} (hp : V.toAffine.Nonsingular x y) :
    pointCongr h (.some x y hp) = .some x y (h ▸ hp) := by
  subst W
  rfl

@[simp] theorem pointCongr_symm_some {V W : _root_.WeierstrassCurve K} (h : V = W)
    {x y : K} (hp : W.toAffine.Nonsingular x y) :
    (pointCongr h).symm (.some x y hp) = .some x y (h.symm ▸ hp) := by
  subst W
  rfl

/-- Transport of the actual additive action across equality of equations. -/
def pointConjugate {V W : _root_.WeierstrassCurve K} (h : V = W)
    (φ : W.toAffine.Point →+ W.toAffine.Point) : V.toAffine.Point →+ V.toAffine.Point :=
  (pointCongr h).symm.toAddMonoidHom.comp (φ.comp (pointCongr h).toAddMonoidHom)

@[simp] theorem pointCongr_pointConjugate {V W : _root_.WeierstrassCurve K} (h : V = W)
    (φ : W.toAffine.Point →+ W.toAffine.Point) (P : V.toAffine.Point) :
    pointCongr h (pointConjugate h φ P) = φ (pointCongr h P) :=
  (pointCongr h).apply_symm_apply _

@[simp] theorem pointConjugate_pointCongr_symm {V W : _root_.WeierstrassCurve K} (h : V = W)
    (φ : W.toAffine.Point →+ W.toAffine.Point) (P : W.toAffine.Point) :
    pointConjugate h φ ((pointCongr h).symm P) = (pointCongr h).symm (φ P) := by
  change (pointCongr h).symm (φ (pointCongr h ((pointCongr h).symm P))) = _
  rw [AddEquiv.apply_symm_apply]

end RHLean.Geometry.NativeCM.Weierstrass

end
