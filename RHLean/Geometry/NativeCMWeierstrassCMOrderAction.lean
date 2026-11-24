import RHLean.Geometry.NativeCMWeierstrassCMGlobal
import RHLean.Geometry.NativeCMSerreSchemeAction

/-!
# The literal quadratic order acts by finite-field scheme morphisms

The constructed CM generator and the actual integral coordinate equivalence
OK = Z + Z w define all scalar endomorphisms. Their action at the fixed
complex embedding is multiplication by the original embedded scalar on the
same u⁻¹-scaled period lattice. Geometric-point detection proves the ring
laws as equalities of finite-field scheme morphisms. This supplies the
genuine OAct input of the represented Serre construction on the generic
fibre, rather than assuming that input.

The integer-power monoid-hom lemma follows Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/
PowObjGeometricallyConnected.lean, `isMonHom_zpow`. The remaining scalar
construction is a native derivation from the actual generator and lattice.
The source archive states no license; attribution is retained without
assigning one. Integral extension of the action is still separate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open NumberField AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace RHLean.Geometry.NativeCM.EllipticSeed

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
    (G : NativeGeometricHost E) (τ : E →+* ℂ)
    (C : _root_.WeierstrassCurve.VariableChange ℂ)

/-- Multiplication by any element of the actual quadratic order on the
actual rescaled lattice curve. -/
def rescaledOrderAction (a : OK G) :
    (Weierstrass.latticeCurve (rescaledPeriods G τ C)).toAffine.Point →+
      (Weierstrass.latticeCurve (rescaledPeriods G τ C)).toAffine.Point :=
  Weierstrass.latticeIsogeny (embed G τ a) (rescaledPeriods_multiplier G τ C a)

@[simp] theorem rescaledOrderAction_latticePoint (a : OK G) (z : ℂ) :
    rescaledOrderAction G τ C a (Weierstrass.latticePoint (rescaledPeriods G τ C) z) =
      Weierstrass.latticePoint (rescaledPeriods G τ C) (embed G τ a * z) :=
  Weierstrass.latticeIsogeny_latticePoint _ z

theorem rescaledOrderAction_wK : rescaledOrderAction G τ C (wK G) = rescaledCMAction G τ C :=
  rfl

theorem rescaledOrderAction_one
    (P : (Weierstrass.latticeCurve (rescaledPeriods G τ C)).toAffine.Point) :
    rescaledOrderAction G τ C 1 P = P := by
  obtain ⟨z, rfl⟩ := Weierstrass.latticePoint_surjective (rescaledPeriods G τ C) P
  rw [rescaledOrderAction_latticePoint, map_one, _root_.one_mul]

theorem rescaledOrderAction_mul (a b : OK G)
    (P : (Weierstrass.latticeCurve (rescaledPeriods G τ C)).toAffine.Point) :
    rescaledOrderAction G τ C (a * b) P =
      rescaledOrderAction G τ C b (rescaledOrderAction G τ C a P) := by
  obtain ⟨z, rfl⟩ := Weierstrass.latticePoint_surjective (rescaledPeriods G τ C) P
  rw [rescaledOrderAction_latticePoint, rescaledOrderAction_latticePoint,
    rescaledOrderAction_latticePoint, map_mul]
  congr 1
  ring

theorem rescaledOrderAction_add (a b : OK G)
    (P : (Weierstrass.latticeCurve (rescaledPeriods G τ C)).toAffine.Point) :
    rescaledOrderAction G τ C (a + b) P =
      rescaledOrderAction G τ C a P + rescaledOrderAction G τ C b P := by
  obtain ⟨z, rfl⟩ := Weierstrass.latticePoint_surjective (rescaledPeriods G τ C) P
  rw [rescaledOrderAction_latticePoint, rescaledOrderAction_latticePoint,
    rescaledOrderAction_latticePoint, map_add, add_mul]
  exact (Weierstrass.latticePointHom (rescaledPeriods G τ C)).map_add _ _

/-- The original integral order coordinates give the same action as the
actual lattice multiplier, including both integer signs. -/
theorem rescaledOrderAction_coordinates (a : OK G)
    (P : (Weierstrass.latticeCurve (rescaledPeriods G τ C)).toAffine.Point) :
    rescaledOrderAction G τ C a P =
      ((coordEquiv G).symm a).1 • P +
        ((coordEquiv G).symm a).2 • rescaledCMAction G τ C P := by
  let m := (coordEquiv G).symm a
  have ha : a = (m.1 : OK G) + (m.2 : OK G) * wK G :=
    ((coordEquiv G).apply_symm_apply a).symm.trans (coordEquiv_apply G m)
  obtain ⟨z, rfl⟩ := Weierstrass.latticePoint_surjective (rescaledPeriods G τ C) P
  rw [rescaledOrderAction_latticePoint, rescaledCMAction_latticePoint]
  have he : embed G τ a * z = (m.1 : ℂ) * z + (m.2 : ℂ) * (omega G τ * z) := by
    rw [ha, map_add, map_mul, map_intCast, map_intCast]
    change ((m.1 : ℂ) + (m.2 : ℂ) * omega G τ) * z = _
    ring
  have h := congrArg (Weierstrass.latticePointHom (rescaledPeriods G τ C)) he
  simpa only [map_add, ← zsmul_eq_mul, map_zsmul,
    Weierstrass.latticePointHom_apply] using! h

end RHLean.Geometry.NativeCM.EllipticSeed

namespace RHLean.Geometry.NativeCM.Weierstrass

open EllipticSeed SchemeTheory SchemeTheory.WeierstrassCurve SerreScheme

private theorem isMonHom_intPower {S : Scheme.{0}} {A B : Over S}
    [GrpObj A] [GrpObj B] [IsCommMonObj B]
    (f : A ⟶ B) [IsMonHom f] (n : ℤ) : IsMonHom (f ^ n) :=
  SerreScheme.isMonHom_of_mul_comp _ fun _ _ _ => by
    simp only [GrpObj.comp_zpow, MonObj.mul_comp, mul_zpow]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
    (G : NativeGeometricHost E) {F : Type} [Field F]
    (V : _root_.WeierstrassCurve F) [V.IsElliptic]
    (f : schemeOver V ⟶ schemeOver V)

/-- All scalars are explicit integer combinations of actual morphisms. -/
def orderSchemeMorphism (a : OK G) : schemeOver V ⟶ schemeOver V :=
  (𝟙 (schemeOver V)) ^ ((coordEquiv G).symm a).1 * f ^ ((coordEquiv G).symm a).2

theorem isMonHom_orderSchemeMorphism [IsMonHom f] (a : OK G) :
    IsMonHom (orderSchemeMorphism G V f a) := by
  have := isMonHom_intPower (𝟙 (schemeOver V)) ((coordEquiv G).symm a).1
  have := isMonHom_intPower f ((coordEquiv G).symm a).2
  exact SerreScheme.isMonHom_mul _ _

variable (τ : E →+* ℂ) (C : _root_.WeierstrassCurve.VariableChange ℂ) [Algebra F ℂ]
    (hVC : V.baseChange ℂ = latticeCurve (rescaledPeriods G τ C))
    (hf : ∀ P : (latticeCurve (rescaledPeriods G τ C)).toAffine.Point,
      ofAffinePoint V ℂ ((pointCongr hVC).symm P) ≫ f =
        ofAffinePoint V ℂ ((pointCongr hVC).symm (rescaledCMAction G τ C P)))

include hf in
theorem orderSchemeMorphism_points (a : OK G)
    (P : (latticeCurve (rescaledPeriods G τ C)).toAffine.Point) :
    ofAffinePoint V ℂ ((pointCongr hVC).symm P) ≫ orderSchemeMorphism G V f a =
      ofAffinePoint V ℂ ((pointCongr hVC).symm (rescaledOrderAction G τ C a P)) := by
  classical
  have hz (n : ℤ) (Q : (V.baseChange ℂ).toAffine.Point) :
      ofAffinePoint V ℂ (n • Q) = ofAffinePoint V ℂ Q ^ n :=
    (affinePointMulEquiv V ℂ).map_zpow (Multiplicative.ofAdd Q) n
  rw [orderSchemeMorphism, MonObj.comp_mul, GrpObj.comp_zpow, Category.comp_id,
    GrpObj.comp_zpow, hf, ← hz, ← hz, ← ofAffinePoint_add, ← map_zsmul, ← map_zsmul,
    ← map_add, ← rescaledOrderAction_coordinates]

/-- The original quadratic order acts by actual finite-field scheme
morphisms. The one, multiplication and addition laws are proved over F. -/
def schemeOrderAction [IsMonHom f] : OAct (OK G) (schemeOver V) where
  act := orderSchemeMorphism G V f
  hom := isMonHom_orderSchemeMorphism G V f
  one := by
    apply GeometricPoints.over_hom_ext_of_embedded_points (K := ℂ)
    intro x
    obtain ⟨P, rfl⟩ := (affinePointEquiv V ℂ).surjective x
    obtain ⟨Q, rfl⟩ := (pointCongr hVC).symm.surjective P
    rw [orderSchemeMorphism_points G V f τ C hVC hf, rescaledOrderAction_one,
      Category.comp_id]
  mul a b := by
    apply GeometricPoints.over_hom_ext_of_embedded_points (K := ℂ)
    intro x
    obtain ⟨P, rfl⟩ := (affinePointEquiv V ℂ).surjective x
    obtain ⟨Q, rfl⟩ := (pointCongr hVC).symm.surjective P
    rw [← Category.assoc, orderSchemeMorphism_points G V f τ C hVC hf,
      orderSchemeMorphism_points G V f τ C hVC hf,
      orderSchemeMorphism_points G V f τ C hVC hf, rescaledOrderAction_mul]
  add a b := by
    apply GeometricPoints.over_hom_ext_of_embedded_points (K := ℂ)
    intro x
    obtain ⟨P, rfl⟩ := (affinePointEquiv V ℂ).surjective x
    obtain ⟨Q, rfl⟩ := (pointCongr hVC).symm.surjective P
    rw [MonObj.comp_mul, orderSchemeMorphism_points G V f τ C hVC hf,
      orderSchemeMorphism_points G V f τ C hVC hf,
      orderSchemeMorphism_points G V f τ C hVC hf, rescaledOrderAction_add,
      map_add, ofAffinePoint_add]

theorem schemeOrderAction_wK [IsMonHom f] :
    (schemeOrderAction G V f τ C hVC hf).act (wK G) = f := by
  apply GeometricPoints.over_hom_ext_of_embedded_points (K := ℂ)
  intro x
  obtain ⟨P, rfl⟩ := (affinePointEquiv V ℂ).surjective x
  obtain ⟨Q, rfl⟩ := (pointCongr hVC).symm.surjective P
  change _ ≫ orderSchemeMorphism G V f (wK G) = _
  rw [orderSchemeMorphism_points G V f τ C hVC hf, rescaledOrderAction_wK, hf]

/-- Exact multiplication on the original period parameter for every order
element, with no change to the original coordinate scale. -/
theorem schemeOrderAction_latticePoint [IsMonHom f] (a : OK G) (z : ℂ) :
    ofAffinePoint V ℂ ((pointCongr hVC).symm (latticePoint (rescaledPeriods G τ C) z)) ≫
        (schemeOrderAction G V f τ C hVC hf).act a =
      ofAffinePoint V ℂ ((pointCongr hVC).symm
        (latticePoint (rescaledPeriods G τ C) (embed G τ a * z))) := by
  change _ ≫ orderSchemeMorphism G V f a = _
  rw [orderSchemeMorphism_points G V f τ C hVC hf, rescaledOrderAction_latticePoint]

/-- The generic-fibre Serre scalar action is supplied on the normalized
original W over a proved finite number field. -/
theorem exists_cm_scheme_order_action
    (M : IntermediateField ℚ ℂ) [NumberField M]
    (W : _root_.WeierstrassCurve (𝓞 M)) [W.IsElliptic] (w : 𝓞 M)
    (hC : C • W.baseChange ℂ = latticeCurve (periodPair G τ))
    (hw : ((w : M) : ℂ) = omega G τ) :
    ∃ (F : IntermediateField ℚ ℂ) (_ : NumberField F) (hMF : M ≤ F)
      (V : _root_.WeierstrassCurve F) (_ : V.IsElliptic)
      (hVC : V.baseChange ℂ = latticeCurve (rescaledPeriods G τ C))
      (a : OAct (OK G) (schemeOver V)),
      V = shortModel ((W.baseChange M).map (IntermediateField.inclusion hMF).toRingHom) ∧
      ∀ c : OK G, ∀ z : ℂ,
        ofAffinePoint V ℂ ((pointCongr hVC).symm (latticePoint (rescaledPeriods G τ C) z)) ≫
            a.act c =
          ofAffinePoint V ℂ ((pointCongr hVC).symm
            (latticePoint (rescaledPeriods G τ C) (embed G τ c * z))) := by
  obtain ⟨F, hF, hMF, V, hV, α, A, D, hα, hshort, hID, hVC, f,
    hnorm, -, -, -, -, -, -, hf, -, hpoint, -⟩ :=
    exists_cm_scheme_generator G τ M W w C hC hw
  let _ : NumberField F := hF
  let _ : V.IsElliptic := hV
  let _ : IsMonHom f := hf
  exact ⟨F, hF, hMF, V, hV, hVC, schemeOrderAction G V f τ C hVC hpoint, hnorm,
    schemeOrderAction_latticePoint G V f τ C hVC hpoint⟩

end RHLean.Geometry.NativeCM.Weierstrass

end
