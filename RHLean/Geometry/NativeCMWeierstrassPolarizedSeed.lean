import RHLean.Geometry.NativeCMWeierstrassPolarizedOrigin
import RHLean.Geometry.NativeCMWeierstrassThetaMetric

/-!
# One integral polarized seed with the exact exponential and first jet

The integral equation, origin polarization, original period kernel and
literal integral tangent are joined on the same witnesses. The sigma
comparison at every infinite place retains the original coordinate-change
scale. This native join consumes the proved constructions, rather than
assuming a principal polarization or changing the integral seed.

The order action over the finite field extension is constructed separately.
Its extension over the integers, the global analytic atlas/curvature join,
and the integral ideal-isogeny family remain distinct obligations.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open NumberField Filter PeriodPair AlgebraicGeometry CategoryTheory
open scoped Topology

namespace RHLean.Geometry.NativeCM.WeierstrassPolarizedSeed

open SchemeTheory SchemeTheory.WeierstrassCurve SchemeTheory.WeierstrassLie
open WeierstrassTangent

/-- The same integral seed has all four actual origin-polarization
properties, its original exponential and period kernel, and the exact
integral dual-number first jet. -/
theorem exists_integral_polarized_seed_with_exact_period
    {E : Type} [Field E] [NumberField E] [IsCMField E]
    (G : NativeGeometricHost E) (τ : E →+* ℂ) :
    ∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M)
      (W : _root_.WeierstrassCurve (𝓞 M)) (w : 𝓞 M)
      (C : _root_.WeierstrassCurve.VariableChange ℂ) (hΔ : W.Δ = 1),
      let _ : W.IsElliptic := ⟨hΔ.symm ▸ isUnit_one⟩
      (∀ a : E, τ a ∈ M) ∧ ((w : M) : ℂ) = EllipticSeed.omega G τ ∧
      IsLieBasis ![integralVector W] ∧
      (originLB W).IsLB ∧
      (Rigidified (schemeOver W) (originLB W) ∧
        Sym (schemeOver W) (originLB W) ∧
        RelAmple (schemeOver W) (originLB W) ∧
        KTriv (schemeOver W) (originLB W)) ∧
      (C.u : ℂ) ^ 12 *
        (Weierstrass.latticeCurve (EllipticSeed.periodPair G τ)).Δ = 1 ∧
      ∃ hC : C • W.baseChange ℂ =
          Weierstrass.latticeCurve (EllipticSeed.periodPair G τ),
        Function.Surjective (schemeExponential G τ W C hC) ∧
        (∀ z, schemeExponential G τ W C hC z = 0 ↔ z ∈ EllipticSeed.lattice G τ) ∧
        (∀ᶠ z in 𝓝 (0 : ℂ), z = 0 ∨
          ∃ h : (W.baseChange ℂ).toAffine.Nonsingular
              (affineX (EllipticSeed.periodPair G τ) C z)
              (affineY (EllipticSeed.periodPair G τ) C z),
            EllipticSeed.equationExponential G τ (W.baseChange ℂ) C hC z =
              .some _ _ h ∧
            originZ (EllipticSeed.periodPair G τ) C z =
              -affineX (EllipticSeed.periodPair G τ) C z /
                affineY (EllipticSeed.periodPair G τ) C z ∧
            originW (EllipticSeed.periodPair G τ) C z =
              -1 / affineY (EllipticSeed.periodPair G τ) C z) ∧
        let P : Fin 3 → DualNumber ℂ :=
          ![TrivSqZeroExt.inr (deriv (fun z =>
              originZ (EllipticSeed.periodPair G τ) C ((C.u : ℂ) * z)) 0), -1,
            TrivSqZeroExt.inr (deriv (fun z =>
              originW (EllipticSeed.periodPair G τ) C ((C.u : ℂ) * z)) 0)]
        ∃ h : IsUnimodularSol
            (W.map ((algebraMap ℂ (DualNumber ℂ)).comp (algebraMap (𝓞 M) ℂ))) P,
          spMap (dualMap (algebraMap (𝓞 M) ℂ)) ≫ (integralVector W).left =
            ptHom W ((algebraMap ℂ (DualNumber ℂ)).comp (algebraMap (𝓞 M) ℂ)) P h := by
  obtain ⟨M, hM, W, w, C, hΔ, hhost, hw, hLie, hu,
    hC, hsurj, hker, hcoords, hjet⟩ :=
    exists_integral_group_scheme_seed_with_exact_tangent G τ
  let _ : NumberField M := hM
  let _ : W.IsElliptic := ⟨hΔ.symm ▸ isUnit_one⟩
  exact ⟨M, hM, W, w, C, hΔ, hhost, hw, hLie, originLB_isLB W,
    originLB_polarisation W, hu, hC, hsurj, hker, hcoords, hjet⟩

/-- The sigma automorphy form of the same integral equation gives the
actual place profile, and its logarithm is the exact lattice period. -/
theorem exact_sigma_period_at_every_place
    {M : Type} [Field M] (W : _root_.WeierstrassCurve (𝓞 M)) (hΔ : W.Δ = 1) :
    ∀ v : InfinitePlace M,
      let L := AllPlaceTangentPeriod.lattice W hΔ v
      let C := AllPlaceTangentPeriod.coordinateChange W hΔ v
      0 < Real.pi * (Weierstrass.latticeForm L (C.u : ℂ) (C.u : ℂ)).re ∧
      Real.pi * (Weierstrass.latticeForm L (C.u : ℂ) (C.u : ℂ)).re =
        AllPlaceTangentPeriod.placeProfile W hΔ v ∧
      -Real.log (Real.pi * (Weierstrass.latticeForm L (C.u : ℂ) (C.u : ℂ)).re) =
        PeriodArithmetic.latticeLogPeriod L := by
  intro v
  exact ⟨WeierstrassTheta.integral_direction_length_pos _ _,
    WeierstrassTheta.automorphy_tangent_eq_placeProfile W hΔ v,
    WeierstrassTheta.neg_log_automorphy_tangent W hΔ v⟩

end RHLean.Geometry.NativeCM.WeierstrassPolarizedSeed
