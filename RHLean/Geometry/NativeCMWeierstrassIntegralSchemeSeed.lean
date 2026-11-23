import RHLean.Geometry.NativeCMWeierstrassIntegralTangent
import RHLean.Geometry.NativeCMWeierstrassSeedPoints

/-!
# The same CM equation as a genuine integral group scheme

The previously constructed Delta-one equation is now the actual smooth,
proper, geometrically connected projective Weierstrass group scheme over
O_M. Its specified integral dual-number tangent generator is [epsilon,-1,0].
The existing exact complex point exponential is identified with this
scheme's complex points by the proved algebraic point equivalence.

All witnesses W, C, the CM generator, the period lattice, and the nontrivial
u^12 discriminant scale are retained. This does not yet assert an algebraic
scheme morphism for the CM action, a polarizing line bundle, or a mean
logarithmic arithmetic tangent norm.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory
open CartesianMonoidalCategory MonObj

namespace RHLean.Geometry.NativeCM.SchemeTheory

open WeierstrassCurve WeierstrassLie

section ComplexPoints

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
    (G : NativeGeometricHost E) (τ : E →+* ℂ)
    {R : Type} [CommRing R] [_root_.IsReduced R] [Algebra R ℂ]
    (W : _root_.WeierstrassCurve R) [W.IsElliptic]
    (C : _root_.WeierstrassCurve.VariableChange ℂ)
    (hC : C • W.baseChange ℂ =
      RHLean.Geometry.NativeCM.Weierstrass.latticeCurve (EllipticSeed.periodPair G τ))

/-- The already proved elliptic exponential, on the complex points of
the actual integral group scheme. -/
def schemeExponential : ℂ →+ Additive (specOver R ℂ ⟶ schemeOver W) :=
  (affinePointAddEquiv W ℂ).toAddMonoidHom.comp
    (EllipticSeed.equationExponential G τ (W.baseChange ℂ) C hC)

theorem schemeExponential_surjective :
    Function.Surjective (schemeExponential G τ W C hC) :=
  (affinePointAddEquiv W ℂ).surjective.comp
    (EllipticSeed.equationExponential_surjective G τ (W.baseChange ℂ) C hC)

/-- The exact original quadratic-order period kernel is unchanged. -/
theorem schemeExponential_kernel (z : ℂ) :
    schemeExponential G τ W C hC z = 0 ↔ z ∈ EllipticSeed.lattice G τ := by
  change affinePointAddEquiv W ℂ
    (EllipticSeed.equationExponential G τ (W.baseChange ℂ) C hC z) = 0 ↔ _
  rw [AddEquiv.map_eq_zero_iff]
  exact EllipticSeed.equationExponential_ker G τ (W.baseChange ℂ) C hC z

/-- This equivalence joins the constructed analytic seed to the actual
complex points of the integral group scheme. -/
def torusSchemePointEquiv :
    EllipticSeed.Torus G τ ≃+ Additive (specOver R ℂ ⟶ schemeOver W) :=
  (EllipticSeed.equationPointEquiv G τ (W.baseChange ℂ) C hC).trans
    (affinePointAddEquiv W ℂ)

end ComplexPoints

/-- A single actual CM equation supplies its integral group scheme,
literal Lie generator, and exact complex period comparison together. -/
theorem exists_integral_group_scheme_seed
    {E : Type} [Field E] [NumberField E] [IsCMField E]
    (G : NativeGeometricHost E) (τ : E →+* ℂ) :
    ∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M)
      (W : _root_.WeierstrassCurve (𝓞 M)) (w : 𝓞 M)
      (C : _root_.WeierstrassCurve.VariableChange ℂ) (hΔ : W.Δ = 1),
      let _ : W.IsElliptic := ⟨hΔ.symm ▸ isUnit_one⟩
      (∀ a : E, τ a ∈ M) ∧ ((w : M) : ℂ) = EllipticSeed.omega G τ ∧
      IsCommMonObj (schemeOver W) ∧
      SmoothOfRelativeDimension 1 (toSpec W) ∧ IsProper (toSpec W) ∧
      GeometricallyConnected (toSpec W) ∧
      IsLieBasis ![integralVector W] ∧
      (integralVector W).left = ptHom W (algebraMap (𝓞 M) (DualNumber (𝓞 M)))
        ![DualNumber.eps, -1, 0] (isUnimodularSol_origin (equation_inr W 1)) ∧
      (C.u : ℂ) ^ 12 *
        (RHLean.Geometry.NativeCM.Weierstrass.latticeCurve (EllipticSeed.periodPair G τ)).Δ = 1 ∧
      ∃ hC : C • W.baseChange ℂ =
          RHLean.Geometry.NativeCM.Weierstrass.latticeCurve (EllipticSeed.periodPair G τ),
        Function.Surjective (schemeExponential G τ W C hC) ∧
        (∀ z, schemeExponential G τ W C hC z = 0 ↔ z ∈ EllipticSeed.lattice G τ) ∧
        Nonempty (EllipticSeed.Torus G τ ≃+ Additive (specOver (𝓞 M) ℂ ⟶ schemeOver W)) := by
  obtain ⟨M, hM, W, w, C, hhost, hw, hΔ, hu, hC, -⟩ :=
    RHLean.Geometry.NativeCM.Weierstrass.exists_integral_point_uniformization G τ
  let _ : NumberField M := hM
  let _ : W.IsElliptic := ⟨hΔ.symm ▸ isUnit_one⟩
  refine ⟨M, hM, W, w, C, hΔ, hhost, hw, inferInstance, inferInstance,
    inferInstance, inferInstance, integralVector_isLieBasis W, rfl, hu, hC, ?_⟩
  exact ⟨schemeExponential_surjective G τ W C hC,
    schemeExponential_kernel G τ W C hC, ⟨torusSchemePointEquiv G τ W C hC⟩⟩

end RHLean.Geometry.NativeCM.SchemeTheory

end
