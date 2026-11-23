import RHLean.Geometry.NativeCMWeierstrassTranslationScheme
import RHLean.Geometry.NativeCMWeierstrassIntegralTangent

/-!
# The actual equation translation preserves the group and its integral vector

The triangular projective isomorphism is compared with the proved affine
point change over every field. Reduced-scheme point detection then proves
that it preserves the actual group law. Its effect on the literal
dual-number point [c epsilon,-1,0] is calculated over the original ring,
including nonreduced dual numbers. Thus the unit-one normalization does
not change the integral tangent generator.

These are native joins between the actual constructors in
`NativeCMWeierstrassTranslationScheme`, `NativeCMWeierstrassPointChange`
and `NativeCMWeierstrassIntegralTangent`. The source point-detection proof
is reconstructed in those modules from Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
`src/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/OverHomEqIffForallIsAlgClosedAlgebra.lean`.
The source archive states no license; attribution is retained without assigning one.
No extension over a ring of integers is assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Classical

attribute [local instance] Over.cartesianMonoidalCategory

namespace RHLean.Geometry.NativeCM.SchemeTheory.WeierstrassCurve

open WeierstrassLie

variable {R : Type} [CommRing R]
    (W V : _root_.WeierstrassCurve R) (r s t : R)
    (hC : translationChange r s t • W = V)

include hC in
theorem translationChange_baseChange (k : Type) [Field k] [Algebra R k] :
    translationChange (algebraMap R k r) (algebraMap R k s) (algebraMap R k t) •
      W.baseChange k = V.baseChange k := by
  change translationChange _ _ _ • W.map (algebraMap R k) = V.map (algebraMap R k)
  rw [← translationChange_map, _root_.WeierstrassCurve.map_variableChange, hC]

/-- The actual projective scheme morphism gives the same affine point
change that already preserves elliptic addition. -/
theorem ofAffinePoint_translation (k : Type) [Field k] [Algebra R k]
    (P : (V.baseChange k).toAffine.Point) :
    ofAffinePoint V k P ≫ (translationOverIso W V r s t hC).hom =
      ofAffinePoint W k
        (Weierstrass.variableChangePoint
          (translationChange (algebraMap R k r) (algebraMap R k s) (algebraMap R k t))
          (translationChange_baseChange W V r s t hC k) P) := by
  cases P with
  | zero =>
      rw [map_zero, ofAffinePoint_zero, ofAffinePoint_zero,
        zeroOver_eq_ptOver, zeroOver_eq_ptOver]
      apply Over.OverMorphism.ext
      change ptHom V (algebraMap R k) ![0, 1, 0] _ ≫
        translationHom W V r s t hC = ptHom W (algebraMap R k) ![0, 1, 0] _
      rw [ptHom_translationHom]
      apply ptHom_congr W _ _ _ rfl
      funext i
      fin_cases i <;> simp [translationTriple]
  | some x y hP =>
      rw [Weierstrass.variableChangePoint_some, ofAffinePoint_some, ofAffinePoint_some]
      apply Over.OverMorphism.ext
      change ptHom V (algebraMap R k) ![x, y, 1] _ ≫
        translationHom W V r s t hC = ptHom W (algebraMap R k) _ _
      rw [ptHom_translationHom]
      apply ptHom_congr W _ _ _ rfl
      funext i
      fin_cases i <;> simp [translationTriple, translationChange]

section Reduced

variable [_root_.IsReduced R] [W.IsElliptic] [V.IsElliptic]

theorem translation_mul_points (k : Type) [Field k] [Algebra R k]
    (p q : specOver R k ⟶ schemeOver V) :
    (p * q) ≫ (translationOverIso W V r s t hC).hom =
      (p ≫ (translationOverIso W V r s t hC).hom) *
        (q ≫ (translationOverIso W V r s t hC).hom) := by
  obtain ⟨P, rfl⟩ := (affinePointEquiv V k).surjective p
  obtain ⟨Q, rfl⟩ := (affinePointEquiv V k).surjective q
  rw [← ofAffinePoint_add, ofAffinePoint_translation, map_add, ofAffinePoint_add,
    ofAffinePoint_translation, ofAffinePoint_translation]

/-- The actual triangular scheme isomorphism preserves the group law. -/
instance translationOverIso_isMonHom :
    IsMonHom (translationOverIso W V r s t hC).hom where
  one_hom := by
    have : IsReduced (𝟙_ (Over (Spec (.of R)))).left := by
      change IsReduced (Spec (.of R))
      infer_instance
    apply over_hom_eq_iff_forall_field_algebra.mpr
    intro k _ _ x
    rw [← Category.assoc, MonObj.one_eq_one, MonObj.comp_one,
      MonObj.one_eq_one, MonObj.comp_one]
    have hV : ofAffinePoint V k 0 = 1 := (affinePointMulEquiv V k).map_one
    have hW : ofAffinePoint W k 0 = 1 := (affinePointMulEquiv W k).map_one
    simpa only [map_zero, hV, hW] using
      ofAffinePoint_translation W V r s t hC k 0
  mul_hom := by
    apply over_hom_eq_iff_forall_field_algebra.mpr
    intro k _ _ x
    change (x ≫ μ[schemeOver V]) ≫ (translationOverIso W V r s t hC).hom =
      (x ≫ ((translationOverIso W V r s t hC).hom ⊗ₘ
        (translationOverIso W V r s t hC).hom)) ≫ μ[schemeOver W]
    rw [MonObj.mul_eq_mul, MonObj.comp_mul,
      translation_mul_points W V r s t hC,
      MonObj.mul_eq_mul, MonObj.comp_mul]
    simp only [Category.assoc, tensorHom_fst, tensorHom_snd]

end Reduced

/-- A unit-one equation change preserves every literal epsilon vector over
the original ring, without a reducedness or field assumption. -/
theorem vec_translation (c : R) :
    vec V c ≫ (translationOverIso W V r s t hC).hom.left = vec W c := by
  change vec V c ≫ translationHom W V r s t hC = vec W c
  rw [vec, ptHom_translationHom, vec]
  apply (ptHom_eq_ptHom_iff_minors W _ _).mpr
  intro i j
  fin_cases i <;> fin_cases j <;> ext <;> simp [translationTriple]

theorem vec_translation_inv (c : R) :
    vec W c ≫ (translationOverIso W V r s t hC).inv.left = vec V c :=
  vec_translation V W (-r) (-s) (r * s - t)
    (translationChange_reverse W V r s t hC) c

end RHLean.Geometry.NativeCM.SchemeTheory.WeierstrassCurve

namespace RHLean.Geometry.NativeCM.Weierstrass

open SchemeTheory SchemeTheory.WeierstrassCurve SchemeTheory.WeierstrassLie

variable {F : Type} [Field F] [CharZero F] (W : _root_.WeierstrassCurve F)

instance shortModel_isElliptic [W.IsElliptic] : (shortModel W).IsElliptic := by
  rw [← shortChange_spec]
  infer_instance

instance shortModelSchemeIso_isMonHom [W.IsElliptic] :
    IsMonHom (shortModelSchemeIso W).hom :=
  translationOverIso_isMonHom W (shortModel W) _ _ _ (shortChange_spec W)

theorem vec_shortModelSchemeIso (c : F) :
    vec (shortModel W) c ≫ (shortModelSchemeIso W).hom.left = vec W c :=
  vec_translation W (shortModel W) _ _ _ (shortChange_spec W) c

theorem vec_shortModelSchemeIso_inv (c : F) :
    vec W c ≫ (shortModelSchemeIso W).inv.left = vec (shortModel W) c :=
  vec_translation_inv W (shortModel W) _ _ _ (shortChange_spec W) c

end RHLean.Geometry.NativeCM.Weierstrass

end
