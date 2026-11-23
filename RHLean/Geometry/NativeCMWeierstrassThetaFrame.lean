import RHLean.Geometry.NativeCMWeierstrassCanonicalTheta
import RHLean.Geometry.NativeCMAllPlaceTangentPeriod
import RHLean.Geometry.NativeCMWeierstrassSectionPoints

/-!+# The actual origin-section theta frame and its tangent normalization

The canonical sigma function is joined to the actual coordinate functions
of the same Weierstrass exponential. The quotient of the origin section by
sigma extends to an analytic unit at zero, with value -u⁻¹. The minus sign
comes from the literal origin section x/y; the integral tangent coordinate
is -x/y. Scheme-section evaluation retains that sign.

This is native glue between the attributed sigma, actual section and first
jet constructions. No abstract theta uniformization or assigned arithmetic
mean is used. The complete global analytic bundle identification is a
separate statement from this local section comparison.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open Filter Complex PeriodPair AlgebraicGeometry CategoryTheory
open scoped Topology ComplexConjugate Real

namespace RHLean.Geometry.NativeCM.WeierstrassTheta

open Weierstrass WeierstrassTangent PeriodMean

variable (L : PeriodPair) (C : WeierstrassCurve.VariableChange ℂ)

/-- The actual nonvanishing factor of canonical sigma at its simple origin zero. -/
def sigmaUnit (z : ℂ) : ℂ := sigmaProd L z * exp (-(sTwo L * z ^ 2 / 2))

theorem canonicalSigma_eq_mul_unit (z : ℂ) :
    canonicalSigma L z = z * sigmaUnit L z := by
  simp only [canonicalSigma, weierstrassSigma, sigmaUnit, mul_assoc]

@[simp] theorem sigmaUnit_zero : sigmaUnit L 0 = 1 := by simp [sigmaUnit]

theorem sigmaUnit_analytic : AnalyticAt ℂ (sigmaUnit L) 0 := by
  have := (differentiable_sigmaProd L).analyticAt (0 : ℂ)
  unfold sigmaUnit
  fun_prop

/-- An actual analytic extension of (x/y)/sigma near the origin. -/
def originFrame (z : ℂ) : ℂ :=
  regularX L C z / regularY L C z / sigmaUnit L z

theorem originFrame_analytic : AnalyticAt ℂ (originFrame L C) 0 :=
  ((regularX_analytic L C).div (regularY_analytic L C)
    (regularY_zero_ne L C)).div (sigmaUnit_analytic L) (by simp)

@[simp] theorem originFrame_zero : originFrame L C 0 = -(C.u : ℂ)⁻¹ := by
  rw [originFrame, regularX_zero, regularY_zero, sigmaUnit_zero, div_one]
  field_simp

theorem originFrame_zero_ne : originFrame L C 0 ≠ 0 := by
  rw [originFrame_zero]
  exact neg_ne_zero.mpr (inv_ne_zero (Units.ne_zero C.u))

/-- The sign is the actual origin section x/y, not the coordinate -x/y. -/
theorem origin_section_factorization :
    ∀ᶠ z in 𝓝 (0 : ℂ), -originZ L C z = canonicalSigma L z * originFrame L C z := by
  filter_upwards [(sigmaUnit_analytic L).continuousAt.eventually_ne
    (show sigmaUnit L 0 ≠ 0 by simp),
    (regularY_analytic L C).continuousAt.eventually_ne (regularY_zero_ne L C)] with z hz hy
  rw [canonicalSigma_eq_mul_unit, originFrame, originZ]
  field_simp
  ring

theorem affine_origin_section_factorization :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ),
      affineX L C z / affineY L C z = canonicalSigma L z * originFrame L C z := by
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds ((regularY_analytic L C).continuousAt.eventually_ne
      (regularY_zero_ne L C)),
    mem_nhdsWithin_of_mem_nhds (origin_section_factorization L C)] with z hz hy he
  have hy' : affineY L C z ≠ 0 := by
    intro h
    rw [regularY_eq L C hz, h, mul_zero] at hy
    exact hy rfl
  rw [originZ_eq L C hz hy', neg_div, neg_neg] at he
  exact he

/-- The affine frame has no zeros off the actual period lattice. -/
def affineFrame (z : ℂ) : ℂ := (canonicalSigma L z)⁻¹

theorem affineFrame_ne_zero {z : ℂ} (hz : z ∉ L.lattice) : affineFrame L z ≠ 0 :=
  inv_ne_zero ((canonicalSigma_eq_zero_iff L).not.mpr hz)

theorem affine_section_factorization {z : ℂ} (hz : z ∉ L.lattice) :
    (1 : ℂ) = canonicalSigma L z * affineFrame L z :=
  (mul_inv_cancel₀ ((canonicalSigma_eq_zero_iff L).not.mpr hz)).symm

/-- The transition between the two actual local frames is x/y. -/
theorem origin_affine_frame_transition :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ),
      originFrame L C z = (affineX L C z / affineY L C z) * affineFrame L z := by
  filter_upwards [affine_origin_section_factorization L C,
    eventually_notMem_lattice L 0] with z hz hzl
  rw [hz, affineFrame]
  have hσ := (canonicalSigma_eq_zero_iff L).not.mpr hzl
  field_simp

/-- The Hermitian factor is the one proved in canonical sigma's automorphy law. -/
theorem integral_direction_length :
    Real.pi * (latticeForm L (C.u : ℂ) (C.u : ℂ)).re =
      Real.pi * ‖(C.u : ℂ)‖ ^ 2 / ZLattice.covolume L.lattice := by
  rw [latticeForm_self, Complex.ofReal_re]
  change Real.pi * (‖(C.u : ℂ)‖ ^ 2 / latticeArea L) =
    Real.pi * ‖(C.u : ℂ)‖ ^ 2 / latticeArea L
  ring

theorem integral_direction_length_pos :
    0 < Real.pi * (latticeForm L (C.u : ℂ) (C.u : ℂ)).re := by
  rw [integral_direction_length]
  exact div_pos (mul_pos Real.pi_pos (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr
    (Units.ne_zero C.u)))) (ZLattice.covolume_pos _ _)

section ActualSections

open SchemeTheory SchemeTheory.SectionPoints SchemeTheory.WeierstrassCurve

variable {R : Type} [CommRing R] [Algebra R ℂ] (W : WeierstrassCurve R)
  {x y : ℂ} (hP : (W.baseChange ℂ).toAffine.Nonsingular x y)

/-- Evaluation of the same algebraic origin section at the actual projective point. -/
theorem eval_originParam_of_affine (hy : y ≠ 0)
    (hU : ⊤ ≤ (ptOver W ![x, y, 1] (isUnimodularSol_some hP.equation)).left ⁻¹ᵁ originOpen W) :
    evalPt (ptOver W ![x, y, 1] (isUnimodularSol_some hP.equation)).left
      (originOpen W) hU (originParam W) = x / y := by
  apply (eq_div_iff hy).mpr
  exact evalPt_ptHom_ratioOn_mul (algebraMap R ℂ) ![x, y, 1]
    (isUnimodularSol_some hP.equation) (originOpen_le W) hU 0

/-- The affine component of the canonical origin section evaluates to one. -/
theorem eval_originSec_affine
    (hU : ⊤ ≤ (ptOver W ![x, y, 1] (isUnimodularSol_some hP.equation)).left ⁻¹ᵁ coordOpen W 2) :
    evalPt (ptOver W ![x, y, 1] (isUnimodularSol_some hP.equation)).left
      (coordOpen W 2) hU ((originSec W).f false) = 1 := map_one _

end ActualSections

end RHLean.Geometry.NativeCM.WeierstrassTheta
