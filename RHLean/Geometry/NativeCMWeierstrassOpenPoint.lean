import RHLean.Geometry.NativeCMWeierstrassCMOpen

/-!
# An algebraic point in the actual denominator open

A nonzero polynomial over a number field has a nonroot in that field. After
adjoining one square root of the short Weierstrass cubic, this gives an actual
point of the denominator open over a proved finite extension. The localization
lift constructs its scheme-valued section. This supplies the translation point
for the two-patch extension of the actual CM rational scheme map.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial NumberField IntermediateField
open MonoidalCategory CartesianMonoidalCategory

attribute [local instance] Over.cartesianMonoidalCategory

namespace RHLean.Geometry.NativeCM.SchemeTheory.WeierstrassCurve

universe u

variable {K : Type u} [Field K] (W : _root_.WeierstrassCurve K) (D : K[X])
    {k : Type u} [Field k] [Algebra K k] (x y : k)
    (hxy : (W.baseChange k).toAffine.Equation x y)
    (hD : aeval x D ≠ 0)

theorem affineAeval_aeval (p : K[X]) :
    affineAeval W x y hxy (aeval (affineX W) p) = aeval x p := by
  change affineAeval W x y hxy (eval₂ (algebraMap K _) (affineX W) p) = _
  rw [Polynomial.algHom_eval₂_algebraMap]
  change eval₂ (algebraMap K k) (affineEval W (algebraMap K k) x y hxy (affineX W)) p = _
  rw [affineEval_affineX]
  rfl

include hD in
theorem isUnit_affineAeval_denominator :
    IsUnit (affineAeval W x y hxy (aeval (affineX W) D)) := by
  rw [affineAeval_aeval]
  exact isUnit_iff_ne_zero.mpr hD

/-- The localization point is constructed from the actual affine coordinates. -/
def rationalOpenPoint : RationalOpenRing W D →ₐ[K] k :=
  IsLocalization.Away.liftAlgHom (aeval (affineX W) D)
    (isUnit_affineAeval_denominator W D x y hxy hD)

theorem rationalOpenPoint_X :
    rationalOpenPoint W D x y hxy hD (rationalOpenX W D) = x := by
  change IsLocalization.Away.lift _ _ (algebraMap W.toAffine.CoordinateRing _ (affineX W)) = _
  rw [IsLocalization.Away.lift_eq]
  exact affineEval_affineX W (algebraMap K k) x y hxy

theorem rationalOpenPoint_Y :
    rationalOpenPoint W D x y hxy hD (rationalOpenY W D) = y := by
  change IsLocalization.Away.lift _ _ (algebraMap W.toAffine.CoordinateRing _ (affineY W)) = _
  rw [IsLocalization.Away.lift_eq]
  exact affineEval_affineY W (algebraMap K k) x y hxy

/-- The localization lift has precisely the original affine coordinates. -/
theorem rationalOpenPoint_incl
    (h : (W.baseChange k).toAffine.Nonsingular x y) :
    specOverMap (rationalOpenPoint W D x y hxy hD) ≫ rationalOpenIncl W D =
      ofAffinePoint W k (.some x y h) := by
  rw [rationalOpenIncl, specOverMap_ptOver, ofAffinePoint_some]
  apply Over.OverMorphism.ext
  refine pt_congr W _ _ ?_ _
  funext i
  fin_cases i
  · exact rationalOpenPoint_X W D x y hxy hD
  · exact rationalOpenPoint_Y W D x y hxy hD
  · exact map_one (rationalOpenPoint W D x y hxy hD)

/-- A point over the coefficient field is an actual section of the open scheme. -/
def rationalOpenSection (x y : K) (hxy : W.toAffine.Equation x y) (hD : D.eval x ≠ 0) :
    𝟙_ (Over (Spec (.of K))) ⟶ specOver K (RationalOpenRing W D) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (rationalOpenPoint W D x y hxy hD).toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      (rationalOpenPoint W D x y hxy hD).comp_algebraMap]
    exact Spec.map_id _)

end RHLean.Geometry.NativeCM.SchemeTheory.WeierstrassCurve

namespace RHLean.Geometry.NativeCM.Weierstrass

open SchemeTheory SchemeTheory.WeierstrassCurve

/-- One finite extension supplies a point outside the actual denominator roots.
No infinite-order point or rational-point density hypothesis is used. -/
theorem exists_numberField_point_off_denominator
    (F : IntermediateField ℚ ℂ) [NumberField F] (V : _root_.WeierstrassCurve F)
    (hshort : V.a₁ = 0 ∧ V.a₂ = 0 ∧ V.a₃ = 0) (D : F[X]) (hD : D ≠ 0) :
    ∃ (L : IntermediateField ℚ ℂ) (_ : NumberField L) (hFL : F ≤ L) (x y : L),
      (V.map (IntermediateField.inclusion hFL).toRingHom).toAffine.Equation x y ∧
      (D.map (IntermediateField.inclusion hFL).toRingHom).eval x ≠ 0 := by
  classical
  have hf : {x : F | D.IsRoot x}.Finite := Polynomial.finite_setOfPred_isRoot hD
  obtain ⟨x, hx⟩ := hf.infinite_compl.nonempty
  have hx : D.eval x ≠ 0 := hx
  let t : F := x ^ 3 + V.a₄ * x + V.a₆
  let y := Complex.sqrt (t : ℂ)
  have hy : y ^ 2 = (t : ℂ) := Complex.sq_sqrt _
  have hyt : IsIntegral ℚ y := IsIntegral.of_pow (by decide : 0 < 2) (by
    rw [hy]
    exact ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) t).algHom F.val).isIntegral)
  have : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {y}) :=
    IntermediateField.finiteDimensional_adjoin fun z hz =>
      (Set.mem_singleton_iff.mp hz).symm ▸ hyt
  let L : IntermediateField ℚ ℂ := F ⊔ IntermediateField.adjoin ℚ {y}
  have : NumberField L := ⟨⟩
  have hFL : F ≤ L := le_sup_left
  let i := IntermediateField.inclusion hFL
  let xL : L := i x
  let yL : L := ⟨y, (le_sup_right : IntermediateField.adjoin ℚ {y} ≤ L)
    (IntermediateField.subset_adjoin ℚ {y} rfl)⟩
  refine ⟨L, inferInstance, hFL, xL, yL, ?_, ?_⟩
  · apply (_root_.WeierstrassCurve.Affine.map_equation _ (f := (L.val : L →+* ℂ))
      (L.val : L →+* ℂ).injective xL yL).mp
    rw [_root_.WeierstrassCurve.Affine.equation_iff]
    change y ^ 2 + (V.a₁ : ℂ) * (x : ℂ) * y + (V.a₃ : ℂ) * y =
      (x : ℂ) ^ 3 + (V.a₂ : ℂ) * (x : ℂ) ^ 2 + (V.a₄ : ℂ) * (x : ℂ) + (V.a₆ : ℂ)
    rw [hshort.1, hshort.2.1, hshort.2.2]
    push_cast
    simp only [zero_mul, add_zero]
    simpa only [t, map_add, map_mul, map_pow] using hy
  · change (D.map i.toRingHom).eval (i x) ≠ 0
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
    exact fun h => hx (i.injective (h.trans (map_zero i).symm))

end RHLean.Geometry.NativeCM.Weierstrass

end
