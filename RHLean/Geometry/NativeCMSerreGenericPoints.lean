import RHLean.Geometry.NativeCMWeierstrassCMOrderAction
import RHLean.Geometry.NativeCMSerreSchemeTensor
import RHLean.Geometry.NativeCMSerrePeriods

/-!
# The genuine generic-fibre tensor and its original complex periods

The proved scheme order action is compared with the original analytic
torus using the specified homothety z ↦ u⁻¹z. The resulting equivalence is
linear for the actual scheme point action. Tensoring it with the original
projective trace module identifies the represented scheme points, and
retains the exact original integral tensor kernel and full coefficient
action.

This is native glue of the already attributed normalized CM morphism,
elliptic period, and represented Serre constructions. It does not extend
the action over the integers or identify an arithmetic tangent lattice.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open NumberField AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Classical TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

namespace RHLean.Geometry.NativeCM.Weierstrass

open EllipticSeed SchemeTheory SchemeTheory.WeierstrassCurve SerreScheme

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
    (G : NativeGeometricHost E) (τ : E →+* ℂ)
    {F : Type} [Field F] [Algebra F ℂ]
    (V : _root_.WeierstrassCurve F) [V.IsElliptic]
    (C : _root_.WeierstrassCurve.VariableChange ℂ)
    (hVC : V.baseChange ℂ = latticeCurve (rescaledPeriods G τ C))

/-- The normalized equation has the original torus as its point group;
the actual inverse coordinate scale occurs explicitly in the map. -/
def genericTorusPointEquiv :
    Torus G τ ≃+ Additive (specOver F ℂ ⟶ schemeOver V) :=
  (torusPointEquiv G τ).trans ((rescaledPointEquiv G τ C).symm.trans
    ((pointCongr hVC).symm.trans (affinePointAddEquiv V ℂ)))

theorem genericTorusPointEquiv_mk (z : ℂ) :
    Additive.toMul (genericTorusPointEquiv G τ V C hVC
      (QuotientAddGroup.mk' (period G τ).range z)) =
        ofAffinePoint V ℂ ((pointCongr hVC).symm
          (latticePoint (rescaledPeriods G τ C) ((C.u : ℂ)⁻¹ * z))) := by
  change ofAffinePoint V ℂ ((pointCongr hVC).symm
    (latticeIsogeny (C.u : ℂ)⁻¹ _
      (torusPointEquiv G τ (QuotientAddGroup.mk' (period G τ).range z)))) = _
  rw [torusPointEquiv_mk, latticeIsogeny_latticePoint]

variable (a : OAct (OK G) (schemeOver V))
    (hact : ∀ c : OK G, ∀ z : ℂ,
      ofAffinePoint V ℂ ((pointCongr hVC).symm (latticePoint (rescaledPeriods G τ C) z)) ≫
          a.act c =
        ofAffinePoint V ℂ ((pointCongr hVC).symm
          (latticePoint (rescaledPeriods G τ C) (embed G τ c * z))))

/-- Linearity is proved against composition with the genuine scheme
endomorphisms, rather than supplied by a transported module definition. -/
def genericTorusPointLinearEquiv :
    Torus G τ ≃ₗ[OK G] Pts a (specOver F ℂ) :=
  { genericTorusPointEquiv G τ V C hVC with
    map_smul' := by
      intro c x
      obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective (period G τ).range x
      apply Pts.ext
      change Additive.toMul (genericTorusPointEquiv G τ V C hVC
          (c • QuotientAddGroup.mk' (period G τ).range z)) =
        Additive.toMul (genericTorusPointEquiv G τ V C hVC
          (QuotientAddGroup.mk' (period G τ).range z)) ≫ a.act c
      rw [torus_smul_mk, genericTorusPointEquiv_mk, genericTorusPointEquiv_mk, hact]
      congr 3
      ring }

theorem genericTorusPointLinearEquiv_mk (z : ℂ) :
    Pts.hom (genericTorusPointLinearEquiv G τ V C hVC a hact
      (QuotientAddGroup.mk' (period G τ).range z)) =
        ofAffinePoint V ℂ ((pointCongr hVC).symm
          (latticePoint (rescaledPeriods G τ C) ((C.u : ℂ)⁻¹ * z))) :=
  genericTorusPointEquiv_mk G τ V C hVC z

end RHLean.Geometry.NativeCM.Weierstrass

namespace RHLean.Geometry.NativeCM.TraceFrame

open EllipticSeed SchemeTheory SchemeTheory.WeierstrassCurve SerreScheme Weierstrass

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
    {G : NativeGeometricHost E} {D : TraceLattice G} {ε : ℤˣ}
    (P : TraceFrame D ε) (τ : E →+* ℂ)
    {F : Type} [Field F] [Algebra F ℂ]
    (V : _root_.WeierstrassCurve F) [V.IsElliptic]
    (C : _root_.WeierstrassCurve.VariableChange ℂ)
    (hVC : V.baseChange ℂ = latticeCurve (rescaledPeriods G τ C))
    (a : OAct (OK G) (schemeOver V))
    (hact : ∀ c : OK G, ∀ z : ℂ,
      ofAffinePoint V ℂ ((pointCongr hVC).symm (latticePoint (rescaledPeriods G τ C) z)) ≫
          a.act c =
        ofAffinePoint V ℂ ((pointCongr hVC).symm
          (latticePoint (rescaledPeriods G τ C) (embed G τ c * z))))

def genericPointEquiv : D.La ⊗[OK G] Torus G τ ≃ₗ[OK G]
    Pts (P.schemeAct a) (specOver F ℂ) :=
  ((genericTorusPointLinearEquiv G τ V C hVC a hact).lTensor D.La).trans
    ((P.schemeIsTensor a).equiv (specOver F ℂ))

theorem genericPointEquiv_tmul (m : D.La) (z : ℂ) :
    Pts.hom (P.genericPointEquiv τ V C hVC a hact
      (m ⊗ₜ[OK G] QuotientAddGroup.mk' (period G τ).range z)) =
        ofAffinePoint V ℂ ((pointCongr hVC).symm
          (latticePoint (rescaledPeriods G τ C) ((C.u : ℂ)⁻¹ * z))) ≫
            (P.schemeIsTensor a).tmul m := by
  change Pts.hom ((P.schemeIsTensor a).equiv (specOver F ℂ)
    ((genericTorusPointLinearEquiv G τ V C hVC a hact).lTensor D.La
      (m ⊗ₜ[OK G] QuotientAddGroup.mk' (period G τ).range z))) = _
  rw [LinearEquiv.lTensor_tmul, IsTensor.hom_equiv_tmul, genericTorusPointLinearEquiv_mk]

/-- On every point tensor, full coefficient multiplication is the actual
scheme coefficient endomorphism. -/
theorem genericPointEquiv_coefficient (c : 𝓞 E) (t : D.La ⊗[OK G] Torus G τ) :
    Pts.hom (P.genericPointEquiv τ V C hVC a hact (c • t)) =
      Pts.hom (P.genericPointEquiv τ V C hVC a hact t) ≫
        (P.schemeCoefficientAct a).act c := by
  have := (P.schemeCoefficientAct a).hom c
  induction t using TensorProduct.inductionOn with
  | tmul m x =>
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective (period G τ).range x
    simp only [← TensorProduct.smul_tmul', genericPointEquiv_tmul,
      Category.assoc, schemeCoefficientAct_tmul]
  | add t u ht hu =>
    simp only [smul_add, map_add, Pts.hom_add, MonObj.mul_comp, ht, hu]

variable [Algebra (OK G) ℂ] (hemb : algebraMap (OK G) ℂ = embed G τ)

/-- This exponential takes values in actual points of the represented
scheme on the same module, with the original unscaled period kernel. -/
def genericExponential : ℂ ⊗[OK G] D.La →ₗ[OK G]
    Pts (P.schemeAct a) (specOver F ℂ) :=
  (P.genericPointEquiv τ V C hVC a hact).toLinearMap.comp
    (serreExponential G τ hemb D.La)

theorem genericExponential_surjective :
    Function.Surjective (P.genericExponential τ V C hVC a hact hemb) :=
  (P.genericPointEquiv τ V C hVC a hact).surjective.comp
    (serreExponential_surjective G τ hemb D.La)

theorem genericExponential_ker (t : ℂ ⊗[OK G] D.La) :
    P.genericExponential τ V C hVC a hact hemb t = 0 ↔
      ∃ m : D.La, t = 1 ⊗ₜ[OK G] m := by
  change P.genericPointEquiv τ V C hVC a hact (serreExponential G τ hemb D.La t) = 0 ↔ _
  rw [LinearEquiv.map_eq_zero_iff, serreExponential_ker]

theorem genericExponential_tmul (z : ℂ) (m : D.La) :
    Pts.hom (P.genericExponential τ V C hVC a hact hemb (z ⊗ₜ[OK G] m)) =
      ofAffinePoint V ℂ ((pointCongr hVC).symm
        (latticePoint (rescaledPeriods G τ C) ((C.u : ℂ)⁻¹ * z))) ≫
          (P.schemeIsTensor a).tmul m := by
  change Pts.hom (P.genericPointEquiv τ V C hVC a hact
    (serreExponential G τ hemb D.La (z ⊗ₜ[OK G] m))) = _
  rw [serreExponential_tmul, genericPointEquiv_tmul]

/-- The whole O_E action is retained as actual scheme postcomposition. -/
theorem genericExponential_coefficient (c : 𝓞 E) (t : ℂ ⊗[OK G] D.La) :
    Pts.hom (P.genericExponential τ V C hVC a hact hemb
      ((moduleScalar D c).baseChange ℂ t)) =
      Pts.hom (P.genericExponential τ V C hVC a hact hemb t) ≫
        (P.schemeCoefficientAct a).act c := by
  have := (P.schemeCoefficientAct a).hom c
  induction t using TensorProduct.inductionOn with
  | tmul z m =>
    simp only [LinearMap.baseChange_tmul, genericExponential_tmul,
      Category.assoc, schemeCoefficientAct_tmul, moduleScalar]
  | add t u ht hu =>
    simp only [map_add, Pts.hom_add, MonObj.mul_comp, ht, hu]

end RHLean.Geometry.NativeCM.TraceFrame

end
