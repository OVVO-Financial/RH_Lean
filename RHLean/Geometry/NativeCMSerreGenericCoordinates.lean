import RHLean.Geometry.NativeCMSerreGenericPoints
import RHLean.Geometry.NativeCMSerreSchemeBundle

/-!
# Actual complex coordinates of the represented Serre bundle maps

Each original trace-frame coordinate and each of the four signed bundle
maps is compared with the actual generic equation exponential. Their
complex linear forms are derived from the original integral pairings.
The same nontrivial inverse coordinate scale appears in the equation
point formula. Integral tensor periods map to periods of that same seed.

These are direct native consequences of the proved point tensor and
scheme morphism formulas. They add no representability, derivative or
metric premise.
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

/-- The actual generic equation exponential, with the original periods. -/
def genericSeedExponential : ℂ →+ Additive (specOver F ℂ ⟶ schemeOver V) :=
  (genericTorusPointEquiv G τ V C hVC).toAddMonoidHom.comp
    (QuotientAddGroup.mk' (period G τ).range)

theorem genericSeedExponential_apply (z : ℂ) :
    Additive.toMul (genericSeedExponential G τ V C hVC z) =
      ofAffinePoint V ℂ ((pointCongr hVC).symm
        (latticePoint (rescaledPeriods G τ C) ((C.u : ℂ)⁻¹ * z))) :=
  genericTorusPointEquiv_mk G τ V C hVC z

theorem genericSeedExponential_add (z w : ℂ) :
    Additive.toMul (genericSeedExponential G τ V C hVC (z + w)) =
      Additive.toMul (genericSeedExponential G τ V C hVC z) *
        Additive.toMul (genericSeedExponential G τ V C hVC w) :=
  congrArg Additive.toMul (map_add (genericSeedExponential G τ V C hVC) z w)

theorem genericSeedExponential_zero :
    Additive.toMul (genericSeedExponential G τ V C hVC 0) = 1 :=
  congrArg Additive.toMul (map_zero (genericSeedExponential G τ V C hVC))

theorem genericSeedExponential_ker (z : ℂ) :
    Additive.toMul (genericSeedExponential G τ V C hVC z) = 1 ↔ z ∈ lattice G τ := by
  change genericTorusPointEquiv G τ V C hVC
    (QuotientAddGroup.mk' (period G τ).range z) = 0 ↔ _
  rw [AddEquiv.map_eq_zero_iff]
  change (z : ℂ ⧸ (period G τ).range) = 0 ↔ z ∈ (period G τ).range
  exact QuotientAddGroup.eq_zero_iff

variable (a : OAct (OK G) (schemeOver V))
    (hact : ∀ c : OK G, ∀ z : ℂ,
      ofAffinePoint V ℂ ((pointCongr hVC).symm (latticePoint (rescaledPeriods G τ C) z)) ≫
          a.act c =
        ofAffinePoint V ℂ ((pointCongr hVC).symm
          (latticePoint (rescaledPeriods G τ C) (embed G τ c * z))))

include hact in
theorem genericSeedExponential_action (c : OK G) (z : ℂ) :
    Additive.toMul (genericSeedExponential G τ V C hVC z) ≫ a.act c =
      Additive.toMul (genericSeedExponential G τ V C hVC (embed G τ c * z)) := by
  rw [genericSeedExponential_apply, hact, genericSeedExponential_apply]
  congr 3
  ring

end RHLean.Geometry.NativeCM.Weierstrass

namespace RHLean.Geometry.NativeCM.TraceFrame

open EllipticSeed SchemeTheory SchemeTheory.WeierstrassCurve SerreScheme Weierstrass

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
    {G : NativeGeometricHost E} {D : TraceLattice G} {ε : ℤˣ}
    (P : TraceFrame D ε) [Algebra (OK G) ℂ]

/-- Scalar extension of the original integral Hermitian dual coordinate. -/
def complexCoefficient (i : Fin P.n) : ℂ ⊗[OK G] D.La →ₗ[ℂ] ℂ :=
  LinearMap.liftBaseChange ℂ ((Algebra.linearMap (OK G) ℂ).comp (P.coefficient i))

variable (τ : E →+* ℂ) (hemb : algebraMap (OK G) ℂ = embed G τ)

include hemb in
theorem complexCoefficient_tmul (i : Fin P.n) (z : ℂ) (m : D.La) :
    P.complexCoefficient i (z ⊗ₜ[OK G] m) = z * embed G τ (kLin D ε m (P.y i)) := by
  change z * algebraMap (OK G) ℂ (P.coefficient i m) = _
  rw [hemb, coefficient_apply]

def complexBundleFirst (k : Fin P.n × Fin P.n) : ℂ ⊗[OK G] D.La →ₗ[ℂ] ℂ :=
  embed G τ (kLin D ε (P.x k.1) (P.x k.2)) • P.complexCoefficient k.1

def complexBundleSecond (k : Fin P.n × Fin P.n) : ℂ ⊗[OK G] D.La →ₗ[ℂ] ℂ :=
  embed G τ (wK G) • P.complexCoefficient k.2

def complexBundleMap (k : (Fin P.n × Fin P.n) × Fin 4) : ℂ ⊗[OK G] D.La →ₗ[ℂ] ℂ :=
  ![P.complexBundleFirst τ k.1 + P.complexBundleSecond τ k.1,
    P.complexBundleFirst τ k.1, P.complexBundleSecond τ k.1, 0] k.2

variable {F : Type} [Field F] [Algebra F ℂ]
    (V : _root_.WeierstrassCurve F) [V.IsElliptic]
    (C : _root_.WeierstrassCurve.VariableChange ℂ)
    (hVC : V.baseChange ℂ = latticeCurve (rescaledPeriods G τ C))
    (a : OAct (OK G) (schemeOver V))
    (hact : ∀ c : OK G, ∀ z : ℂ,
      ofAffinePoint V ℂ ((pointCongr hVC).symm (latticePoint (rescaledPeriods G τ C) z)) ≫
          a.act c =
        ofAffinePoint V ℂ ((pointCongr hVC).symm
          (latticePoint (rescaledPeriods G τ C) (embed G τ c * z))))

/-- The trace coordinate is the actual seed equation coordinate of the
actual represented tensor exponential. -/
theorem genericExponential_coordinate (i : Fin P.n) (t : ℂ ⊗[OK G] D.La) :
    Pts.hom (P.genericExponential τ V C hVC a hact hemb t) ≫ P.schemeCoordinate a i =
      Additive.toMul (genericSeedExponential G τ V C hVC (P.complexCoefficient i t)) := by
  induction t using TensorProduct.inductionOn with
  | tmul z m =>
    rw [genericExponential_tmul, Category.assoc, tmul_schemeCoordinate,
      ← genericSeedExponential_apply, genericSeedExponential_action G τ V C hVC a hact,
      complexCoefficient_tmul P τ hemb]
    congr 1
    ring
  | add t u ht hu =>
    rw [map_add, Pts.hom_add, MonObj.mul_comp, ht, hu, map_add,
      genericSeedExponential_add]

theorem genericExponential_bundleFirst (k : Fin P.n × Fin P.n)
    (t : ℂ ⊗[OK G] D.La) :
    Pts.hom (P.genericExponential τ V C hVC a hact hemb t) ≫ P.schemeBundleFirst a k =
      Additive.toMul (genericSeedExponential G τ V C hVC (P.complexBundleFirst τ k t)) := by
  rw [schemeBundleFirst, ← Category.assoc, genericExponential_coordinate,
    genericSeedExponential_action G τ V C hVC a hact]
  rfl

theorem genericExponential_bundleSecond (k : Fin P.n × Fin P.n)
    (t : ℂ ⊗[OK G] D.La) :
    Pts.hom (P.genericExponential τ V C hVC a hact hemb t) ≫ P.schemeBundleSecond a k =
      Additive.toMul (genericSeedExponential G τ V C hVC (P.complexBundleSecond τ k t)) := by
  rw [schemeBundleSecond, (P.isLinearHom_schemeCoordinate a k.2).comm,
    ← Category.assoc, genericExponential_coordinate,
    genericSeedExponential_action G τ V C hVC a hact]
  rfl

/-- The four actual pullbacks have exactly the four derived linear forms
[first + second, first, second, zero]. -/
theorem genericExponential_bundleMap (k : (Fin P.n × Fin P.n) × Fin 4)
    (t : ℂ ⊗[OK G] D.La) :
    Pts.hom (P.genericExponential τ V C hVC a hact hemb t) ≫ P.schemeBundleMap a k =
      Additive.toMul (genericSeedExponential G τ V C hVC (P.complexBundleMap τ k t)) := by
  rcases k with ⟨ij, k⟩
  fin_cases k
  · change _ ≫ (P.schemeBundleFirst a ij * P.schemeBundleSecond a ij) =
      Additive.toMul (genericSeedExponential G τ V C hVC
        (P.complexBundleFirst τ ij t + P.complexBundleSecond τ ij t))
    rw [MonObj.comp_mul, genericExponential_bundleFirst, genericExponential_bundleSecond,
      genericSeedExponential_add]
  · exact P.genericExponential_bundleFirst τ hemb V C hVC a hact ij t
  · exact P.genericExponential_bundleSecond τ hemb V C hVC a hact ij t
  · change _ ≫ (1 : P.schemeObj a ⟶ schemeOver V) =
      Additive.toMul (genericSeedExponential G τ V C hVC 0)
    rw [MonObj.comp_one, genericSeedExponential_zero]

/-- The original integral tensor periods go to actual periods under every
one of the scheme bundle maps. -/
include hemb hact in
theorem complexBundleMap_period (k : (Fin P.n × Fin P.n) × Fin 4) (m : D.La) :
    P.complexBundleMap τ k (1 ⊗ₜ[OK G] m) ∈ lattice G τ := by
  have ht : P.genericExponential τ V C hVC a hact hemb (1 ⊗ₜ[OK G] m) = 0 :=
    (P.genericExponential_ker τ V C hVC a hact hemb _).mpr ⟨m, rfl⟩
  have h := P.genericExponential_bundleMap τ hemb V C hVC a hact k (1 ⊗ₜ[OK G] m)
  rw [ht, Pts.hom_zero, MonObj.one_comp] at h
  exact (genericSeedExponential_ker G τ V C hVC _).mp h.symm

include hemb hact in
theorem scaled_complexBundleMap_period (k : (Fin P.n × Fin P.n) × Fin 4) (m : D.La) :
    (C.u : ℂ)⁻¹ * P.complexBundleMap τ k (1 ⊗ₜ[OK G] m) ∈
      (rescaledPeriods G τ C).lattice := by
  rw [rescaledPeriods_mem, mul_inv_cancel_left₀ C.u.ne_zero, periodPair_lattice]
  exact P.complexBundleMap_period τ hemb V C hVC a hact k m

end RHLean.Geometry.NativeCM.TraceFrame

end
