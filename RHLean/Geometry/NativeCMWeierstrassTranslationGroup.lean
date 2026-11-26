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
set_option maxHeartbeats 700000

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

/-- The additive change of affine coordinates over the given field. -/
def translationAffinePointHom (k : Type) [Field k] [Algebra R k] :
    (V.baseChange k).toAffine.Point →+ (W.baseChange k).toAffine.Point :=
  Weierstrass.variableChangePoint (W := W.baseChange k) (W' := V.baseChange k)
    (translationChange (algebraMap R k r) (algebraMap R k s) (algebraMap R k t))
    (translationChange_baseChange W V r s t hC k)

/-- Postcomposition on the represented field points of the original two models. -/
def translateFieldPoint (k : Type) [Field k] [Algebra R k]
    (p : specOver R k ⟶ schemeOver V) : specOver R k ⟶ schemeOver W :=
  p ≫ (translationOverIso W V r s t hC).hom

private theorem ptOver_translation {k : Type} [Field k] [Algebra R k]
    {P Q : Fin 3 → k} {hP : IsUnimodularSol (V.baseChange k) P}
    {hQ : IsUnimodularSol (W.baseChange k) Q}
    (he : translationTriple (algebraMap R k r) (algebraMap R k s) (algebraMap R k t) P = Q) :
    ptOver V P hP ≫ (translationOverIso W V r s t hC).hom = ptOver W Q hQ := by
  apply Over.OverMorphism.ext
  exact (ptHom_translationHom W V r s t hC (algebraMap R k) P hP).trans
    (ptHom_congr W _ _ _ rfl he hQ)

/-- The actual projective scheme morphism gives the same affine point
change that already preserves elliptic addition. -/
theorem ofAffinePoint_translation (k : Type) [Field k] [Algebra R k]
    (P : (V.baseChange k).toAffine.Point) :
    translateFieldPoint W V r s t hC k (ofAffinePoint V k P) =
      ofAffinePoint W k (translationAffinePointHom W V r s t hC k P) := by
  unfold translateFieldPoint
  cases P with
  | zero =>
      simp only [← _root_.WeierstrassCurve.Affine.Point.zero_def, map_zero, ofAffinePoint_zero,
        zeroOver_eq_ptOver]
      apply ptOver_translation W V r s t hC
      funext i
      fin_cases i <;> simp [translationTriple]
  | some x y hP =>
      simp only [translationAffinePointHom, Weierstrass.variableChangePoint_some, ofAffinePoint_some]
      apply ptOver_translation W V r s t hC
      funext i
      fin_cases i <;> simp [translationTriple, translationChange]

private theorem mul_hom_of_field_points {G H : Over (Spec (.of R))} [GrpObj G] [GrpObj H]
    [IsReduced (G ⊗ G).left] [IsSeparated H.hom] (f : G ⟶ H)
    (hf : ∀ (k : Type) [Field k] [Algebra R k] (p q : specOver R k ⟶ G),
      (p * q) ≫ f = (p ≫ f) * (q ≫ f)) : μ[G] ≫ f = (f ⊗ₘ f) ≫ μ[H] := by
  apply (over_hom_eq_iff_forall_field_algebra (T := G ⊗ G) (Y := H)).mpr
  intro k _ _ x
  rw [← Category.assoc x, ← Category.assoc x]
  rw [MonObj.mul_eq_mul, MonObj.comp_mul, hf k, MonObj.mul_eq_mul, MonObj.comp_mul]
  simp only [Category.assoc, tensorHom_fst, tensorHom_snd]

section Reduced

variable [_root_.IsReduced R] [W.IsElliptic] [V.IsElliptic]

private theorem translate_affine_mul (k : Type) [Field k] [Algebra R k]
    (P Q : (V.baseChange k).toAffine.Point) :
    translateFieldPoint W V r s t hC k (ofAffinePoint V k P * ofAffinePoint V k Q) =
      translateFieldPoint W V r s t hC k (ofAffinePoint V k P) *
        translateFieldPoint W V r s t hC k (ofAffinePoint V k Q) := by
  rw [← ofAffinePoint_add V k P Q]
  rw [ofAffinePoint_translation W V r s t hC k (P + Q)]
  rw [map_add (translationAffinePointHom W V r s t hC k), ofAffinePoint_add W k]
  rw [ofAffinePoint_translation W V r s t hC k P, ofAffinePoint_translation W V r s t hC k Q]

private theorem translateFieldPoint_mul (k : Type) [Field k] [Algebra R k]
    (p q : specOver R k ⟶ schemeOver V) :
    translateFieldPoint W V r s t hC k (p * q) =
      translateFieldPoint W V r s t hC k p * translateFieldPoint W V r s t hC k q := by
  obtain ⟨P, rfl⟩ := (ofAffinePoint_bijective V k).surjective p
  obtain ⟨Q, rfl⟩ := (ofAffinePoint_bijective V k).surjective q
  exact translate_affine_mul W V r s t hC k P Q

private theorem mul_of_pointwise_eq {M N : Type*} [Mul M] [Mul N]
    (f g : M → N) (he : ∀ x, f x = g x)
    (hf : ∀ x y, f (x * y) = f x * f y) (x y : M) : g (x * y) = g x * g y :=
  (he (x * y)).symm.trans ((hf x y).trans (congrArg₂ (· * ·) (he x) (he y)))

theorem translation_mul_points (k : Type) [Field k] [Algebra R k]
    (p q : specOver R k ⟶ schemeOver V) :
    (p * q) ≫ (translationOverIso W V r s t hC).hom =
      (p ≫ (translationOverIso W V r s t hC).hom : specOver R k ⟶ schemeOver W) *
        (q ≫ (translationOverIso W V r s t hC).hom : specOver R k ⟶ schemeOver W) := by
  refine mul_of_pointwise_eq (M := specOver R k ⟶ schemeOver V)
    (N := specOver R k ⟶ schemeOver W) (translateFieldPoint W V r s t hC k)
    (fun z : specOver R k ⟶ schemeOver V => z ≫ (translationOverIso W V r s t hC).hom)
    ?_ (translateFieldPoint_mul W V r s t hC k) p q
  intro z
  rfl

/-- The actual triangular scheme isomorphism preserves the group law. -/
instance translationOverIso_isMonHom :
    IsMonHom (translationOverIso W V r s t hC).hom where
  one_hom := by
    -- The original zero section is the literal projective triple [0,1,0].
    -- Check it over the base ring, not by reducing the chosen group law at all fields.
    apply Over.OverMorphism.ext
    change η[schemeOver V].left ≫ translationHom W V r s t hC = η[schemeOver W].left
    rw [one_left, one_left]
    simp only [zero, pt_eq_ptHom, ptHom_translationHom]
    apply ptHom_congr W _ _ _ rfl
    funext i
    fin_cases i <;> simp [translationTriple]
  mul_hom := by
    let : IsReduced (schemeOver V ⊗ schemeOver V).left :=
      @isReduced_tensor_left R _ V (schemeOver V) (isReduced_over_left V)
    exact mul_hom_of_field_points (G := schemeOver V) (H := schemeOver W)
      (translationOverIso W V r s t hC).hom
      (fun k _ _ => translation_mul_points W V r s t hC k)

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
