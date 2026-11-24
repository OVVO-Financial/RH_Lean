import RHLean.Geometry.NativeCMWeierstrassThetaDescent
import RHLean.Geometry.NativeCMWeierstrassOriginDivisor

/-!
# Sigma frames on the actual two-chart origin line bundle

The points are the actual equation exponential followed by the proved
projective scheme-point map. Analytic regularity and nonvanishing of both
frames are proved on the literal algebraic chart inverse images. Evaluating
the canonical algebraic section gives sigma times these frames, and the
actual transition units give their compatibility. Thus the sigma metric
descends through the actual origin-bundle atlas, with its original sign.

This native join does not assert the general theta-uniformization theorem
or assign the arithmetic class-group mean to a metric. Holomorphy and the
differential comparison for every regular section are separate local-ring
statements used in the final Lie-norm identification.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open Filter Complex PeriodPair AlgebraicGeometry CategoryTheory
open scoped Topology ComplexConjugate Real

namespace RHLean.Geometry.NativeCM.SchemeTheory.SectionPoints

variable {X : Scheme.{0}} (L : LB X) (s : L.Sec) (x : Sp ℂ ⟶ X)

theorem evalPt_sec_compat (i j : L.ι) (h : ⊤ ≤ x ⁻¹ᵁ (L.U i ⊓ L.U j)) :
    evalPt x (L.U i) (h.trans (x.preimage_mono inf_le_left)) (s.f i) =
      evalPt x (L.U i ⊓ L.U j) h (L.g i j : Γ(X, L.U i ⊓ L.U j)) *
        evalPt x (L.U j) (h.trans (x.preimage_mono inf_le_right)) (s.f j) := by
  have hc : resG X inf_le_left (s.f i) =
      (L.g i j : Γ(X, L.U i ⊓ L.U j)) * resG X inf_le_right (s.f j) := s.compat i j
  have e := congrArg (evalPt x (L.U i ⊓ L.U j) h) hc
  rw [map_mul, evalPt_res, evalPt_res] at e
  exact e

end RHLean.Geometry.NativeCM.SchemeTheory.SectionPoints

namespace RHLean.Geometry.NativeCM.WeierstrassTheta

open SchemeTheory SchemeTheory.WeierstrassCurve SchemeTheory.SectionPoints
open Weierstrass WeierstrassTangent AllPlaceTangentPeriod

section PointCoordinates

variable {R : Type} [CommRing R] [Algebra R ℂ] (W : WeierstrassCurve R)

theorem point_coordinate_ne_zero (P : Fin 3 → ℂ)
    (hP : IsUnimodularSol (W.baseChange ℂ) P) (i : Fin 3)
    (h : ⊤ ≤ (ptOver W P hP).left ⁻¹ᵁ coordOpen W i) : P i ≠ 0 := by
  have he : (ptOver W P hP).left ⁻¹ᵁ coordOpen W i =
      PrimeSpectrum.basicOpen (P i) :=
    ptHom_preimage_coordOpen W (algebraMap R ℂ) P hP i
  have hb : ⊤ ≤ PrimeSpectrum.basicOpen (P i) := he ▸ h
  intro hz
  rw [hz, PrimeSpectrum.basicOpen_zero] at hb
  exact hb (show IsLocalRing.closedPoint ℂ ∈
    (⊤ : TopologicalSpace.Opens (Sp ℂ)) from trivial)

theorem affinePoint_origin_coordinates_ne_zero {x y : ℂ}
    (hp : (W.baseChange ℂ).toAffine.Nonsingular x y)
    (h : ⊤ ≤ (ptOver W ![x, y, 1] (isUnimodularSol_some hp.1)).left ⁻¹ᵁ
      originOpen W) : x ≠ 0 ∧ y ≠ 0 := by
  let p := (ptOver W ![x, y, 1] (isUnimodularSol_some hp.1)).left
  have hy : y ≠ 0 := point_coordinate_ne_zero W _ _ 1
    (h.trans (p.preimage_mono (originOpen_le W)))
  have ha : ⊤ ≤ p ⁻¹ᵁ coordOpen W 2 := by
    change ⊤ ≤ ptHom W (algebraMap R ℂ) ![x, y, 1]
      (isUnimodularSol_some hp.1) ⁻¹ᵁ coordOpen W 2
    rw [ptHom_preimage_coordOpen]
    exact (PrimeSpectrum.basicOpen_one (R := ℂ)).ge
  have hb : ⊤ ≤ p ⁻¹ᵁ (originOpen W ⊓ coordOpen W 2) :=
    fun q hq => ⟨h hq, ha hq⟩
  have hu := (isUnit_ratioOn_one_zero (W := W) inf_le_left inf_le_right).map
    (evalPt p (originOpen W ⊓ coordOpen W 2) hb)
  have e := evalPt_ptHom_ratioOn_mul (algebraMap R ℂ) ![x, y, 1]
    (isUnimodularSol_some hp.1)
    (inf_le_left.trans (originOpen_le W)) hb 0
  change evalPt p (originOpen W ⊓ coordOpen W 2) hb
      (ratioOn W _ 1 (inf_le_left.trans (originOpen_le W)) 0) * y = x at e
  exact ⟨fun hx => mul_ne_zero hu.ne_zero hy (e.trans hx), hy⟩

end PointCoordinates

section ActualAtlas

variable {R : Type} [CommRing R] [Algebra R ℂ] (W : WeierstrassCurve R)
  (L : PeriodPair) (C : WeierstrassCurve.VariableChange ℂ)
  (hC : C • W.baseChange ℂ = latticeCurve L)

/-- The original analytic equation point, as a point of the actual scheme. -/
def analyticPoint (z : ℂ) : specOver R ℂ ⟶ schemeOver W :=
  ofAffinePoint W ℂ (exponential L (W.baseChange ℂ) C hC z)

theorem analyticPoint_of_mem {z : ℂ} (hz : z ∈ L.lattice) :
    analyticPoint W L C hC z = zeroOver W ℂ := by
  rw [analyticPoint, (exponential_ker L (W.baseChange ℂ) C hC z).mpr hz,
    ofAffinePoint_zero]

theorem analyticPoint_of_notMem {z : ℂ} (hz : z ∉ L.lattice) :
    ∃ hp : (W.baseChange ℂ).toAffine.Nonsingular (affineX L C z) (affineY L C z),
      analyticPoint W L C hC z = ptOver W ![affineX L C z, affineY L C z, 1]
        (isUnimodularSol_some hp.1) := by
  obtain ⟨hp, he⟩ := exponential_coordinates L (W.baseChange ℂ) C hC hz
  exact ⟨hp, by rw [analyticPoint, he, ofAffinePoint_some]⟩

theorem analyticPoint_affine_iff (z : ℂ) :
    (⊤ ≤ (analyticPoint W L C hC z).left ⁻¹ᵁ coordOpen W 2) ↔ z ∉ L.lattice := by
  by_cases hz : z ∈ L.lattice
  · rw [analyticPoint_of_mem W L C hC hz, zeroOver_left,
      Scheme.Hom.comp_preimage, zero_preimage_coordOpen_two]
    change (⊤ ≤ (⊥ : TopologicalSpace.Opens (Sp ℂ))) ↔ z ∉ L.lattice
    exact ⟨fun h => False.elim (h (show
      IsLocalRing.closedPoint ℂ ∈ (⊤ : TopologicalSpace.Opens (Sp ℂ))
      from trivial)), fun h => False.elim (h hz)⟩
  · obtain ⟨hp, he⟩ := analyticPoint_of_notMem W L C hC hz
    rw [he]
    have ha : ⊤ ≤ (ptOver W ![affineX L C z, affineY L C z, 1]
        (isUnimodularSol_some hp.1)).left ⁻¹ᵁ coordOpen W 2 := by
      change ⊤ ≤ ptHom W (algebraMap R ℂ) _ _ ⁻¹ᵁ coordOpen W 2
      rw [ptHom_preimage_coordOpen]
      exact (PrimeSpectrum.basicOpen_one (R := ℂ)).ge
    exact ⟨fun _ => hz, fun _ => ha⟩

theorem analyticPoint_origin_coordinates_ne_zero {z : ℂ} (hz : z ∉ L.lattice)
    (h : ⊤ ≤ (analyticPoint W L C hC z).left ⁻¹ᵁ originOpen W) :
    affineX L C z ≠ 0 ∧ affineY L C z ≠ 0 := by
  obtain ⟨hp, he⟩ := analyticPoint_of_notMem W L C hC hz
  rw [he] at h
  exact affinePoint_origin_coordinates_ne_zero W hp h

/-- The two frames are indexed by the literal origin-bundle atlas. -/
def atlasFrame : (originLB W).ι → ℂ → ℂ
  | true => globalOriginFrame L C
  | false => affineFrame L

theorem atlasFrame_analytic (i : (originLB W).ι) {z : ℂ}
    (h : ⊤ ≤ (analyticPoint W L C hC z).left ⁻¹ᵁ (originLB W).U i) :
    AnalyticAt ℂ (atlasFrame W L C i) z := by
  cases i with
  | false =>
    have hz := (analyticPoint_affine_iff W L C hC z).mp h
    exact ((differentiable_canonicalSigma L).analyticAt z).inv
      ((canonicalSigma_eq_zero_iff L).not.mpr hz)
  | true =>
    by_cases hz : z ∈ L.lattice
    · exact globalOriginFrame_analytic_at_lattice L C hz
    · exact globalOriginFrame_analytic_of_notMem L C hz
        (analyticPoint_origin_coordinates_ne_zero W L C hC hz h).2

theorem atlasFrame_ne_zero (i : (originLB W).ι) {z : ℂ}
    (h : ⊤ ≤ (analyticPoint W L C hC z).left ⁻¹ᵁ (originLB W).U i) :
    atlasFrame W L C i z ≠ 0 := by
  cases i with
  | false => exact affineFrame_ne_zero L ((analyticPoint_affine_iff W L C hC z).mp h)
  | true =>
    by_cases hz : z ∈ L.lattice
    · exact globalOriginFrame_ne_zero_at_lattice L C hz
    · obtain ⟨hx, hy⟩ := analyticPoint_origin_coordinates_ne_zero W L C hC hz h
      exact globalOriginFrame_ne_zero_of_notMem L C hz hx hy

theorem atlasFrame_differentiableOn (i : (originLB W).ι) :
    DifferentiableOn ℂ (atlasFrame W L C i)
      {z | ⊤ ≤ (analyticPoint W L C hC z).left ⁻¹ᵁ (originLB W).U i} :=
  fun _ hz => (atlasFrame_analytic W L C hC i hz).differentiableAt.differentiableWithinAt

private theorem evalPt_congr_point {X : Scheme.{0}} {p q : Sp ℂ ⟶ X}
    (e : p = q) (U : X.Opens) (hp : ⊤ ≤ p ⁻¹ᵁ U) (hq : ⊤ ≤ q ⁻¹ᵁ U)
    (s : Γ(X, U)) : evalPt p U hp s = evalPt q U hq s := by
  subst q
  rfl

theorem atlas_section_factorization (i : (originLB W).ι) (z : ℂ)
    (h : ⊤ ≤ (analyticPoint W L C hC z).left ⁻¹ᵁ (originLB W).U i) :
    evalPt (analyticPoint W L C hC z).left ((originLB W).U i) h ((originSec W).f i) =
      canonicalSigma L z * atlasFrame W L C i z := by
  cases i with
  | false =>
    change evalPt (analyticPoint W L C hC z).left (coordOpen W 2) h
      (1 : Γ(scheme W, coordOpen W 2)) = _
    rw [map_one]
    exact affine_section_factorization L ((analyticPoint_affine_iff W L C hC z).mp h)
  | true =>
    change evalPt (analyticPoint W L C hC z).left (originOpen W) h
      (originParam W) = canonicalSigma L z * globalOriginFrame L C z
    by_cases hz : z ∈ L.lattice
    · have he : (analyticPoint W L C hC z).left =
          spMap (algebraMap R ℂ) ≫ zero W :=
        (congrArg Over.Hom.left (analyticPoint_of_mem W L C hC hz)).trans
          (zeroOver_left W ℂ)
      have hq : ⊤ ≤ (spMap (algebraMap R ℂ) ≫ zero W) ⁻¹ᵁ originOpen W := he ▸ h
      calc
        _ = evalPt (spMap (algebraMap R ℂ) ≫ zero W) (originOpen W) hq
            (originParam W) := evalPt_congr_point he _ h hq _
        _ = algebraMap R ℂ (evalPt (zero W) (originOpen W)
            (zero_preimage_originOpen W).ge (originParam W)) :=
          evalPt_spMap_comp (algebraMap R ℂ) (zero W) (originOpen W)
            (zero_preimage_originOpen W).ge hq _
        _ = _ := by
          rw [show evalPt (zero W) (originOpen W) (zero_preimage_originOpen W).ge
            (originParam W) = 0 from originValue_originParam W,
            map_zero, (canonicalSigma_eq_zero_iff L).mpr hz, zero_mul]
    · obtain ⟨hp, he⟩ := analyticPoint_of_notMem W L C hC hz
      have hxy := analyticPoint_origin_coordinates_ne_zero W L C hC hz h
      have he' := congrArg Over.Hom.left he
      have hq : ⊤ ≤ (ptOver W ![affineX L C z, affineY L C z, 1]
          (isUnimodularSol_some hp.1)).left ⁻¹ᵁ originOpen W := he' ▸ h
      calc
        _ = evalPt (ptOver W ![affineX L C z, affineY L C z, 1]
            (isUnimodularSol_some hp.1)).left (originOpen W) hq (originParam W) :=
          evalPt_congr_point he' _ h hq _
        _ = affineX L C z / affineY L C z := eval_originParam_of_affine W hp hxy.2 hq
        _ = _ := by
          change affineX L C z / affineY L C z = canonicalSigma L z * globalOriginFrame L C z
          rw [globalOriginFrame, ite_eq_right hz]
          rw [← mul_div_assoc, mul_comm (canonicalSigma L z),
            mul_div_cancel_right₀ _ ((canonicalSigma_eq_zero_iff L).not.mpr hz)]

theorem atlasFrame_compat (i j : (originLB W).ι) (z : ℂ)
    (h : ⊤ ≤ (analyticPoint W L C hC z).left ⁻¹ᵁ
      ((originLB W).U i ⊓ (originLB W).U j)) :
    atlasFrame W L C i z =
      evalPt (analyticPoint W L C hC z).left ((originLB W).U i ⊓ (originLB W).U j) h
        ((originLB W).g i j : Γ(scheme W, (originLB W).U i ⊓ (originLB W).U j)) *
          atlasFrame W L C j z := by
  have hi := h.trans ((analyticPoint W L C hC z).left.preimage_mono inf_le_left)
  have hj := h.trans ((analyticPoint W L C hC z).left.preimage_mono inf_le_right)
  by_cases hz : z ∈ L.lattice
  · have ei : i = true := by
      cases i
      · exact False.elim (((analyticPoint_affine_iff W L C hC z).mp hi) hz)
      · rfl
    have ej : j = true := by
      cases j
      · exact False.elim (((analyticPoint_affine_iff W L C hC z).mp hj) hz)
      · rfl
    subst i j
    change _ = evalPt _ _ h (1 : Γ(scheme W, _)) * _
    rw [map_one, one_mul]
  · apply mul_left_cancel₀ ((canonicalSigma_eq_zero_iff L).not.mpr hz)
    have e := evalPt_sec_compat (originLB W) (originSec W)
      (analyticPoint W L C hC z).left i j h
    rw [atlas_section_factorization W L C hC i z hi,
      atlas_section_factorization W L C hC j z hj] at e
    calc
      _ = _ := e
      _ = _ := by ring

omit [Algebra R ℂ] in
theorem atlasFrame_period (i : (originLB W).ι) {w : ℂ} (hw : w ∈ L.lattice) (z : ℂ) :
    atlasFrame W L C i (z + w) = atlasFrame W L C i z / multiplier L w z := by
  cases i with
  | false =>
    change (canonicalSigma L (z + w))⁻¹ = (canonicalSigma L z)⁻¹ / multiplier L w z
    rw [canonicalSigma_automorphy L hw]
    simp only [mul_inv, div_eq_mul_inv, mul_comm]
  | true => exact globalOriginFrame_period L C hw z

end ActualAtlas

end RHLean.Geometry.NativeCM.WeierstrassTheta
