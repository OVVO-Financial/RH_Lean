import RHLean.Geometry.NativeCMWeierstrassRationalIdentity
import RHLean.Geometry.NativeCMWeierstrassTranslationScheme

/-!
# The actual CM rational scheme map on its denominator open

For the literal A,D supplied by the CM point formula, the polynomial identity
constructs a morphism on Spec of the affine coordinate ring localized at D(x).
The source is proved to be an open subscheme of the actual Weierstrass scheme.
Its image coordinates are A/D and alpha⁻¹(A'D-AD')y/D², with no omitted scale.

This is a native construction using the existing affine chart and localization
APIs. It supplies an actual local scheme morphism, not a rational-map extension
assumption. The points above D(x)=0 and the origin still require other patches
before a global CM scheme endomorphism can be asserted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial

namespace RHLean.Geometry.NativeCM.Weierstrass

/-- Clearing only actual units turns the polynomial identity into the curve
equation over any coefficient ring, including the localization chart. -/
theorem cubic_equation_of_identity {R : Type*} [CommRing R]
    {α αi a d di b x y c₄ c₆ : R}
    (hα : αi * α = 1) (hd : d * di = 1)
    (hy : y ^ 2 = x ^ 3 + c₄ * x + c₆)
    (h : α ^ 2 * d * (a ^ 3 + c₄ * a * d ^ 2 + c₆ * d ^ 3) =
      b ^ 2 * (x ^ 3 + c₄ * x + c₆)) :
    (αi * b * di ^ 2 * y) ^ 2 = (a * di) ^ 3 + c₄ * (a * di) + c₆ := by
  rw [← hy] at h
  calc
    (αi * b * di ^ 2 * y) ^ 2 = αi ^ 2 * di ^ 4 * (b ^ 2 * y ^ 2) := by ring
    _ = αi ^ 2 * di ^ 4 *
        (α ^ 2 * d * (a ^ 3 + c₄ * a * d ^ 2 + c₆ * d ^ 3)) := by rw [h]
    _ = (αi * α) ^ 2 * (d * di) *
        ((a * di) ^ 3 + c₄ * (a * di) * (d * di) ^ 2 + c₆ * (d * di) ^ 3) := by ring
    _ = (a * di) ^ 3 + c₄ * (a * di) + c₆ := by rw [hα, hd]; ring

end RHLean.Geometry.NativeCM.Weierstrass

namespace RHLean.Geometry.NativeCM.SchemeTheory.WeierstrassCurve

universe u

variable {K : Type u} [Field K] (W : _root_.WeierstrassCurve K)

abbrev RationalOpenRing (D : K[X]) :=
  Localization.Away (aeval (affineX W) D)

def rationalOpenX (D : K[X]) : RationalOpenRing W D :=
  algebraMap W.toAffine.CoordinateRing _ (affineX W)

def rationalOpenY (D : K[X]) : RationalOpenRing W D :=
  algebraMap W.toAffine.CoordinateRing _ (affineY W)

theorem rationalOpen_aeval (D p : K[X]) :
    algebraMap W.toAffine.CoordinateRing (RationalOpenRing W D) (aeval (affineX W) p) =
      aeval (rationalOpenX W D) p :=
  Polynomial.algHom_eval₂_algebraMap p
    (IsScalarTower.toAlgHom K W.toAffine.CoordinateRing (RationalOpenRing W D)) (affineX W)

theorem rationalOpen_denominator_isUnit (D : K[X]) :
    IsUnit (aeval (rationalOpenX W D) D) := by
  rw [← rationalOpen_aeval]
  exact IsLocalization.Away.algebraMap_isUnit (aeval (affineX W) D)

def rationalDenominatorInv (D : K[X]) : RationalOpenRing W D :=
  ((rationalOpen_denominator_isUnit W D).unit⁻¹ : (RationalOpenRing W D)ˣ)

theorem rationalOpen_denom_mul_inv (D : K[X]) :
    aeval (rationalOpenX W D) D * rationalDenominatorInv W D = 1 := by
  let u := (rationalOpen_denominator_isUnit W D).unit
  have hu : (u : RationalOpenRing W D) = aeval (rationalOpenX W D) D :=
    (rationalOpen_denominator_isUnit W D).unit_spec
  change aeval (rationalOpenX W D) D * ((u⁻¹ : (RationalOpenRing W D)ˣ) : RationalOpenRing W D) = 1
  exact (congrArg (fun v : RationalOpenRing W D =>
    v * ((u⁻¹ : (RationalOpenRing W D)ˣ) : RationalOpenRing W D)) hu.symm).trans u.mul_inv

theorem rationalOpen_equation (D : K[X]) :
    (W.baseChange (RationalOpenRing W D)).toAffine.Equation
      (rationalOpenX W D) (rationalOpenY W D) :=
  (equation_affineX_affineY W).baseChange
    (IsScalarTower.toAlgHom K W.toAffine.CoordinateRing (RationalOpenRing W D))

/-- The literal open chart on which the rational formula is defined. -/
def rationalOpenIncl (D : K[X]) :
    specOver K (RationalOpenRing W D) ⟶ schemeOver W :=
  ptOver W ![rationalOpenX W D, rationalOpenY W D, 1]
    (isUnimodularSol_some (rationalOpen_equation W D))

theorem rationalOpenIncl_left (D : K[X]) :
    (rationalOpenIncl W D).left =
      Spec.map (CommRingCat.ofHom
        (algebraMap W.toAffine.CoordinateRing (RationalOpenRing W D))) ≫ chartZ W := by
  let g := IsScalarTower.toAlgHom K W.toAffine.CoordinateRing (RationalOpenRing W D)
  have hp : (![rationalOpenX W D, rationalOpenY W D, 1] : Fin 3 → RationalOpenRing W D) =
      g ∘ ![affineX W, affineY W, 1] := by
    funext i
    fin_cases i
    · rfl
    · rfl
    · exact (map_one g).symm
  exact (pt_congr W _ (isUnimodularSol_some (rationalOpen_equation W D)) hp
    ((isUnimodularSol_some (equation_affineX_affineY W)).baseChange g)).trans
      (SpecMap_pt W _ (isUnimodularSol_some (equation_affineX_affineY W)) g).symm

instance isOpenImmersion_rationalOpenIncl (D : K[X]) :
    IsOpenImmersion (rationalOpenIncl W D).left := by
  rw [rationalOpenIncl_left]
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap W.toAffine.CoordinateRing (RationalOpenRing W D)))) :=
    IsOpenImmersion.of_isLocalization (aeval (affineX W) D)
  infer_instance

def rationalTargetX (A D : K[X]) : RationalOpenRing W D :=
  aeval (rationalOpenX W D) A * rationalDenominatorInv W D

def rationalTargetY (α : K) (A D : K[X]) : RationalOpenRing W D :=
  algebraMap K _ α⁻¹ * aeval (rationalOpenX W D) (derivative A * D - A * derivative D) *
    rationalDenominatorInv W D ^ 2 * rationalOpenY W D

variable (α : K) (hα : α ≠ 0) (A D : K[X])
    (hshort : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0)
    (hID : Weierstrass.RationalIdentity W α A D)

include hα hshort hID in
theorem rationalTarget_equation :
    (W.baseChange (RationalOpenRing W D)).toAffine.Equation
      (rationalTargetX W A D) (rationalTargetY W α A D) := by
  have hxy := rationalOpen_equation W D
  rw [_root_.WeierstrassCurve.Affine.equation_iff] at hxy ⊢
  simp only [_root_.WeierstrassCurve.baseChange, _root_.WeierstrassCurve.map_a₁,
    _root_.WeierstrassCurve.map_a₂, _root_.WeierstrassCurve.map_a₃, hshort.1, hshort.2.1,
    hshort.2.2, map_zero, zero_mul, add_zero] at hxy ⊢
  have hid := congrArg (aeval (rationalOpenX W D)) hID
  simp only [map_mul, map_add, map_pow, aeval_C, aeval_X] at hid
  have hai : algebraMap K (RationalOpenRing W D) α⁻¹ * algebraMap K _ α = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hα, map_one]
  exact Weierstrass.cubic_equation_of_identity hai (rationalOpen_denom_mul_inv W D) hxy hid

/-- The actual scheme morphism on the denominator open. -/
def rationalOpenHom : specOver K (RationalOpenRing W D) ⟶ schemeOver W :=
  ptOver W ![rationalTargetX W A D, rationalTargetY W α A D, 1]
    (isUnimodularSol_some (rationalTarget_equation W α hα A D hshort hID))

section FieldPoints

variable {k : Type u} [Field k] [Algebra K k]
    (g : RationalOpenRing W D →ₐ[K] k)

theorem rationalOpen_map_aeval (p : K[X]) :
    g (aeval (rationalOpenX W D) p) = aeval (g (rationalOpenX W D)) p :=
  Polynomial.algHom_eval₂_algebraMap p g (rationalOpenX W D)

theorem rationalOpen_map_denominator :
    aeval (g (rationalOpenX W D)) D ≠ 0 ∧
      g (rationalDenominatorInv W D) = (aeval (g (rationalOpenX W D)) D)⁻¹ := by
  have he := congrArg g (rationalOpen_denom_mul_inv W D)
  rw [map_mul, map_one, rationalOpen_map_aeval] at he
  have hn : aeval (g (rationalOpenX W D)) D ≠ 0 := by
    intro h
    rw [h, zero_mul] at he
    exact zero_ne_one he
  refine ⟨hn, ?_⟩
  apply mul_left_cancel₀ hn
  rw [he, mul_inv_cancel₀ hn]

theorem rationalOpen_map_targetX :
    g (rationalTargetX W A D) =
      aeval (g (rationalOpenX W D)) A / aeval (g (rationalOpenX W D)) D := by
  rw [rationalTargetX, map_mul, rationalOpen_map_aeval,
    (rationalOpen_map_denominator W D g).2, div_eq_mul_inv]

theorem rationalOpen_map_targetY :
    g (rationalTargetY W α A D) =
      (algebraMap K k α)⁻¹ *
        (aeval (g (rationalOpenX W D)) (derivative A * D - A * derivative D) /
          aeval (g (rationalOpenX W D)) D ^ 2) * g (rationalOpenY W D) := by
  rw [rationalTargetY, map_mul, map_mul, map_mul, map_pow, g.commutes,
    map_inv₀, rationalOpen_map_aeval, (rationalOpen_map_denominator W D g).2,
    div_eq_mul_inv, inv_pow]
  ring

variable [W.IsElliptic]

/-- On every field-valued chart point the constructed map has the exact
rational coordinates, with the actual denominator proved nonzero. -/
theorem rationalOpenHom_fieldPoint :
    ∃ hx : (W.baseChange k).toAffine.Nonsingular
        (g (rationalOpenX W D)) (g (rationalOpenY W D)),
      ∃ hy : (W.baseChange k).toAffine.Nonsingular
        (aeval (g (rationalOpenX W D)) A / aeval (g (rationalOpenX W D)) D)
        ((algebraMap K k α)⁻¹ *
          (aeval (g (rationalOpenX W D)) (derivative A * D - A * derivative D) /
            aeval (g (rationalOpenX W D)) D ^ 2) * g (rationalOpenY W D)),
      specOverMap g ≫ rationalOpenIncl W D = ofAffinePoint W k (.some _ _ hx) ∧
      specOverMap g ≫ rationalOpenHom W α hα A D hshort hID =
        ofAffinePoint W k (.some _ _ hy) := by
  have hx := (_root_.WeierstrassCurve.Affine.equation_iff_nonsingular).mp
    ((rationalOpen_equation W D).baseChange g)
  have hy := (_root_.WeierstrassCurve.Affine.equation_iff_nonsingular).mp
    ((rationalTarget_equation W α hα A D hshort hID).baseChange g)
  rw [rationalOpen_map_targetX, rationalOpen_map_targetY] at hy
  refine ⟨hx, hy, ?_, ?_⟩
  · rw [rationalOpenIncl, specOverMap_ptOver, ofAffinePoint_some]
    apply Over.OverMorphism.ext
    refine pt_congr W (g ∘ ![rationalOpenX W D, rationalOpenY W D, 1])
      ((isUnimodularSol_some (rationalOpen_equation W D)).baseChange g)
      ?_ (isUnimodularSol_some hx.left)
    funext i
    fin_cases i
    · rfl
    · rfl
    · exact map_one g
  · rw [rationalOpenHom, specOverMap_ptOver, ofAffinePoint_some]
    apply Over.OverMorphism.ext
    refine pt_congr W (g ∘ ![rationalTargetX W A D, rationalTargetY W α A D, 1])
      ((isUnimodularSol_some (rationalTarget_equation W α hα A D hshort hID)).baseChange g)
      ?_ (isUnimodularSol_some hy.left)
    funext i
    fin_cases i
    · exact rationalOpen_map_targetX W A D g
    · exact rationalOpen_map_targetY W α A D g
    · exact map_one g

end FieldPoints

end RHLean.Geometry.NativeCM.SchemeTheory.WeierstrassCurve

end
