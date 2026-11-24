import RHLean.Geometry.NativeCMWeierstrassNormalizedModel

/-!
# The normalized equation comparison as an actual scheme isomorphism

A unit-one Weierstrass change is a triangular linear transformation of the
three homogeneous coordinates. This file applies the already constructed
`linearHom` to that transformation, proves its inverse on the actual Proj
charts, and obtains a scheme isomorphism over the original coefficient ring.
In particular the short model used for the rational CM action is isomorphic
to the same original W over its number field, without adjoining its analytic
period scale. No rational-map extension theorem is assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace RHLean.Geometry.NativeCM.SchemeTheory.WeierstrassCurve

variable {R : Type u} [CommRing R]

def translationChange (r s t : R) : _root_.WeierstrassCurve.VariableChange R :=
  ⟨1, r, s, t⟩

def translationTriple (r s t : R) (P : Fin 3 → R) : Fin 3 → R :=
  ![P 0 + r * P 2, P 1 + s * P 0 + t * P 2, P 2]

theorem translationTriple_inverse (r s t : R) (P : Fin 3 → R) :
    translationTriple (-r) (-s) (r * s - t) (translationTriple r s t P) = P := by
  funext i
  fin_cases i
  · change P 0 + r * P 2 + -r * P 2 = P 0
    ring
  · change P 1 + s * P 0 + t * P 2 + -s * (P 0 + r * P 2) +
      (r * s - t) * P 2 = P 1
    ring
  · rfl

theorem translationTriple_inverse' (r s t : R) (P : Fin 3 → R) :
    translationTriple r s t (translationTriple (-r) (-s) (r * s - t) P) = P := by
  funext i
  fin_cases i
  · change P 0 + -r * P 2 + r * P 2 = P 0
    ring
  · change P 1 + -s * P 0 + (r * s - t) * P 2 + s * (P 0 + -r * P 2) +
      t * P 2 = P 1
    ring
  · rfl

theorem translationChange_inverse (r s t : R) :
    (translationChange r s t)⁻¹ = translationChange (-r) (-s) (r * s - t) := by
  ext
  · rfl
  · simp [translationChange, _root_.WeierstrassCurve.VariableChange.inv_def]
  · simp [translationChange, _root_.WeierstrassCurve.VariableChange.inv_def]
  · simp [translationChange, _root_.WeierstrassCurve.VariableChange.inv_def]

theorem translationChange_map {A : Type*} [CommRing A] (ρ : R →+* A) (r s t : R) :
    (translationChange r s t).map ρ = translationChange (ρ r) (ρ s) (ρ t) := by
  ext
  · change ρ 1 = 1
    exact map_one ρ
  · rfl
  · rfl
  · rfl

theorem equation_translationTriple (W : _root_.WeierstrassCurve R)
    (r s t : R) (P : Fin 3 → R) :
    (translationChange r s t • W).toProjective.Equation P ↔
      W.toProjective.Equation (translationTriple r s t P) := by
  rw [_root_.WeierstrassCurve.Projective.equation_iff,
    _root_.WeierstrassCurve.Projective.equation_iff]
  dsimp [translationChange, translationTriple, _root_.WeierstrassCurve.toProjective,
    _root_.WeierstrassCurve.variableChange_def]
  simp only [inv_one, Units.val_one]
  constructor <;> intro h <;> linear_combination h

theorem span_translationTriple_le (r s t : R) (P : Fin 3 → R) :
    Ideal.span (Set.range (translationTriple r s t P)) ≤ Ideal.span (Set.range P) := by
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  have hP : ∀ j, P j ∈ Ideal.span (Set.range P) := fun j => Ideal.subset_span ⟨j, rfl⟩
  fin_cases i
  · exact Ideal.add_mem _ (hP 0) (Ideal.mul_mem_left _ r (hP 2))
  · exact Ideal.add_mem _ (Ideal.add_mem _ (hP 1) (Ideal.mul_mem_left _ s (hP 0)))
      (Ideal.mul_mem_left _ t (hP 2))
  · exact hP 2

theorem span_translationTriple (r s t : R) (P : Fin 3 → R) :
    Ideal.span (Set.range (translationTriple r s t P)) = Ideal.span (Set.range P) := by
  refine le_antisymm (span_translationTriple_le r s t P) ?_
  have h := span_translationTriple_le (-r) (-s) (r * s - t) (translationTriple r s t P)
  rwa [translationTriple_inverse] at h

variable (W V : _root_.WeierstrassCurve R) (r s t : R)
    (hC : translationChange r s t • W = V)

def translationCoord : Fin 3 → HomRing V :=
  translationTriple (algebraMap R (HomRing V) r) (algebraMap R (HomRing V) s)
    (algebraMap R (HomRing V) t) (coord V)

theorem translationCoord_mem (i : Fin 3) : translationCoord V r s t i ∈ grading V 1 := by
  fin_cases i
  · change coord V 0 + algebraMap R _ r * coord V 2 ∈ _
    rw [← Algebra.smul_def]
    exact add_mem (coord_mem V 0) (Submodule.smul_mem _ r (coord_mem V 2))
  · change coord V 1 + algebraMap R _ s * coord V 0 + algebraMap R _ t * coord V 2 ∈ _
    rw [← Algebra.smul_def, ← Algebra.smul_def]
    exact add_mem (add_mem (coord_mem V 1) (Submodule.smul_mem _ s (coord_mem V 0)))
      (Submodule.smul_mem _ t (coord_mem V 2))
  · exact coord_mem V 2

include hC in
theorem equation_translationCoord :
    (W.baseChange (HomRing V)).toProjective.Equation (translationCoord V r s t) := by
  subst hC
  have h := equation_coord (translationChange r s t • W)
  change ((translationChange r s t • W).map
    (algebraMap R (HomRing (translationChange r s t • W)))).toProjective.Equation
      (coord (translationChange r s t • W)) at h
  rw [← _root_.WeierstrassCurve.map_variableChange, translationChange_map] at h
  exact (equation_translationTriple _ _ _ _ _).mp h

theorem mem_span_translationCoord (i : Fin 3) :
    coord V i ∈ Ideal.span (Set.range (translationCoord V r s t)) := by
  rw [translationCoord, span_translationTriple]
  exact Ideal.subset_span ⟨i, rfl⟩

/-- The actual Proj morphism given by the triangular coordinate transformation. -/
def translationHom : scheme V ⟶ scheme W :=
  linearHom W (translationCoord V r s t) (translationCoord_mem V r s t)
    (equation_translationCoord W V r s t hC) (mem_span_translationCoord V r s t)

@[reassoc (attr := simp)] theorem translationHom_toSpec :
    translationHom W V r s t hC ≫ toSpec W = toSpec V := linearHom_toSpec ..

section Points

variable {A : Type u} [CommRing A] (ρ : R →+* A) (P : Fin 3 → A)
    (hP : IsUnimodularSol (V.map ρ) P)

include hC hP in
theorem isUnimodularSol_translation :
    IsUnimodularSol (W.map ρ) (translationTriple (ρ r) (ρ s) (ρ t) P) := by
  constructor
  · apply (equation_translationTriple _ _ _ _ _).mp
    rw [← translationChange_map, _root_.WeierstrassCurve.map_variableChange, hC]
    exact hP.equation
  · rw [span_translationTriple]
    exact hP.span_eq_top

@[reassoc] theorem ptHom_translationHom :
    ptHom V ρ P hP ≫ translationHom W V r s t hC =
      ptHom W ρ (translationTriple (ρ r) (ρ s) (ρ t) P)
        (isUnimodularSol_translation W V r s t hC ρ P hP) := by
  rw [translationHom, ptHom_linearHom]
  refine ptHom_congr W _ _ _ rfl ?_ _
  funext i
  fin_cases i
  · change evalHom V ρ P hP.equation
      (coord V 0 + algebraMap R _ r * coord V 2) = P 0 + ρ r * P 2
    rw [map_add, map_mul, evalHom_coord, evalHom_algebraMap, evalHom_coord]
  · change evalHom V ρ P hP.equation
      (coord V 1 + algebraMap R _ s * coord V 0 + algebraMap R _ t * coord V 2) =
        P 1 + ρ s * P 0 + ρ t * P 2
    rw [map_add, map_add, map_mul, map_mul, evalHom_coord, evalHom_algebraMap,
      evalHom_coord, evalHom_algebraMap, evalHom_coord]
  · exact evalHom_coord V ρ P hP.equation 2

end Points

include hC in
theorem translationChange_reverse : translationChange (-r) (-s) (r * s - t) • V = W := by
  rw [← translationChange_inverse, ← hC, inv_smul_smul]

theorem translationHom_hom_inv_id :
    translationHom W V r s t hC ≫
      translationHom V W (-r) (-s) (r * s - t) (translationChange_reverse W V r s t hC) =
        𝟙 (scheme V) := by
  have hp {A : Type u} [CommRing A] (ρ : R →+* A) (P : Fin 3 → A)
      (hP : IsUnimodularSol (V.map ρ) P) :
      ptHom V ρ P hP ≫ translationHom W V r s t hC ≫
        translationHom V W (-r) (-s) (r * s - t) (translationChange_reverse W V r s t hC) =
          ptHom V ρ P hP := by
    rw [ptHom_translationHom_assoc, ptHom_translationHom]
    refine ptHom_congr V _ _ _ rfl ?_ _
    rw [map_neg, map_neg, map_sub, map_mul]
    exact translationTriple_inverse _ _ _ P
  apply scheme_hom_ext V
  · rw [Category.comp_id]
    exact hp _ _ (isUnimodularSol_origin (equation_originZ_originW V))
  · rw [Category.comp_id]
    exact hp _ _ _

theorem translationHom_inv_hom_id :
    translationHom V W (-r) (-s) (r * s - t) (translationChange_reverse W V r s t hC) ≫
      translationHom W V r s t hC = 𝟙 (scheme W) := by
  have hp {A : Type u} [CommRing A] (ρ : R →+* A) (P : Fin 3 → A)
      (hP : IsUnimodularSol (W.map ρ) P) :
      ptHom W ρ P hP ≫
        translationHom V W (-r) (-s) (r * s - t) (translationChange_reverse W V r s t hC) ≫
          translationHom W V r s t hC = ptHom W ρ P hP := by
    rw [ptHom_translationHom_assoc, ptHom_translationHom]
    refine ptHom_congr W _ _ _ rfl ?_ _
    rw [map_neg, map_neg, map_sub, map_mul]
    exact translationTriple_inverse' _ _ _ P
  apply scheme_hom_ext W
  · rw [Category.comp_id]
    exact hp _ _ (isUnimodularSol_origin (equation_originZ_originW W))
  · rw [Category.comp_id]
    exact hp _ _ _

/-- The actual projective scheme isomorphism given by the equation translation. -/
def translationIso : scheme V ≅ scheme W where
  hom := translationHom W V r s t hC
  inv := translationHom V W (-r) (-s) (r * s - t) (translationChange_reverse W V r s t hC)
  hom_inv_id := translationHom_hom_inv_id W V r s t hC
  inv_hom_id := translationHom_inv_hom_id W V r s t hC

/-- The same isomorphism commutes with the literal maps to Spec R. -/
def translationOverIso : schemeOver V ≅ schemeOver W where
  hom := Over.homMk (translationIso W V r s t hC).hom (translationHom_toSpec W V r s t hC)
  inv := Over.homMk (translationIso W V r s t hC).inv
    (translationHom_toSpec V W (-r) (-s) (r * s - t) (translationChange_reverse W V r s t hC))
  hom_inv_id := Over.OverMorphism.ext (translationHom_hom_inv_id W V r s t hC)
  inv_hom_id := Over.OverMorphism.ext (translationHom_inv_hom_id W V r s t hC)

end RHLean.Geometry.NativeCM.SchemeTheory.WeierstrassCurve

namespace RHLean.Geometry.NativeCM.Weierstrass

open SchemeTheory.WeierstrassCurve

variable {K : Type u} [Field K] [CharZero K]

/-- The normalized equation and W are isomorphic as schemes over K itself. -/
def shortModelSchemeIso (W : _root_.WeierstrassCurve K) :
    schemeOver (shortModel W) ≅ schemeOver W :=
  translationOverIso W (shortModel W) (-W.b₂ / 12) (-W.a₁ / 2)
    ((W.a₁ * W.b₂ - 12 * W.a₃) / 24) (shortChange_spec W)

open NumberField IntermediateField EllipticSeed

/-- The algebraic scheme comparison and the actual rescaled analytic equation
use the same integral seed W and the same original period scale C.u. -/
theorem normalized_seed_scheme_comparison
    {E : Type} [Field E] [NumberField E] [IsCMField E]
    (G : NativeGeometricHost E) (τ : E →+* ℂ)
    (M : IntermediateField ℚ ℂ) [NumberField M]
    (W : _root_.WeierstrassCurve (𝓞 M)) (C : _root_.WeierstrassCurve.VariableChange ℂ)
    (hC : C • W.baseChange ℂ = latticeCurve (periodPair G τ)) :
    Nonempty (schemeOver (shortModel (W.baseChange M)) ≅ schemeOver (W.baseChange M)) ∧
      (shortModel (W.baseChange M)).baseChange ℂ = latticeCurve (rescaledPeriods G τ C) :=
  ⟨⟨shortModelSchemeIso (W.baseChange M)⟩,
    rescaled_model_defined_over_same_field G τ M W C hC⟩

end RHLean.Geometry.NativeCM.Weierstrass

end
