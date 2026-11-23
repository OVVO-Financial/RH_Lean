import RHLean.Geometry.NativeCMWeierstrassThetaMetric

/-!
# Translate the actual origin theta frame across every period

The origin frame is defined at every lattice zero by the actual sigma
derivative, and elsewhere by the literal ratio (x/y)/sigma. Its multiplier
law is proved, and analytic regularity at every lattice point follows from
the already constructed frame at zero. This carries the sign -u⁻¹ through
all lattice translates and supplies the explicit analytic descent data.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open Filter Complex PeriodPair
open scoped Topology ComplexConjugate Real

namespace RHLean.Geometry.NativeCM.WeierstrassTheta

open Weierstrass WeierstrassTangent

variable (L : PeriodPair) (C : WeierstrassCurve.VariableChange ℂ)

theorem multiplier_analytic (w z : ℂ) : AnalyticAt ℂ (multiplier L w) z := by
  unfold multiplier latticeForm
  fun_prop

theorem deriv_canonicalSigma_ne_zero {z : ℂ} (hz : z ∈ L.lattice) :
    deriv (canonicalSigma L) z ≠ 0 := by
  rw [(hasDerivAt_canonicalSigma' L z).deriv,
    (weierstrassSigma_eq_zero_iff L).mpr hz, mul_zero, sub_zero]
  exact mul_ne_zero (deriv_weierstrassSigma_ne_zero L hz) (exp_ne_zero _)

theorem deriv_canonicalSigma_add {w z : ℂ} (hw : w ∈ L.lattice) (hz : z ∈ L.lattice) :
    deriv (canonicalSigma L) (z + w) = multiplier L w z * deriv (canonicalSigma L) z := by
  have h₁ := (differentiable_canonicalSigma L (z + w)).hasDerivAt.comp_add_const
  have h₂ := (multiplier_analytic L w z).differentiableAt.hasDerivAt.fun_mul
    (differentiable_canonicalSigma L z).hasDerivAt
  rw [funext (canonicalSigma_automorphy L hw)] at h₁
  simpa only [(canonicalSigma_eq_zero_iff L).mpr hz, mul_zero, zero_add] using h₁.unique h₂

theorem affineX_periodic {w : ℂ} (hw : w ∈ L.lattice) (z : ℂ) :
    affineX L C (z + w) = affineX L C z := by
  simp only [affineX, L.weierstrassP_add_coe z ⟨w, hw⟩]

theorem affineY_periodic {w : ℂ} (hw : w ∈ L.lattice) (z : ℂ) :
    affineY L C (z + w) = affineY L C z := by
  simp only [affineY, L.weierstrassP_add_coe z ⟨w, hw⟩,
    L.derivWeierstrassP_add_coe z ⟨w, hw⟩]

def globalOriginFrame (z : ℂ) : ℂ :=
  if z ∈ L.lattice then -(C.u : ℂ)⁻¹ / deriv (canonicalSigma L) z
  else (affineX L C z / affineY L C z) / canonicalSigma L z

@[simp] theorem globalOriginFrame_zero : globalOriginFrame L C 0 = -(C.u : ℂ)⁻¹ := by
  simp [globalOriginFrame, (hasDerivAt_canonicalSigma_zero L).deriv]

theorem globalOriginFrame_period {w : ℂ} (hw : w ∈ L.lattice) (z : ℂ) :
    globalOriginFrame L C (z + w) = globalOriginFrame L C z / multiplier L w z := by
  by_cases hz : z ∈ L.lattice
  · rw [globalOriginFrame, ite_eq_left (add_mem hz hw), globalOriginFrame, ite_eq_left hz,
      deriv_canonicalSigma_add L hw hz]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  · rw [globalOriginFrame, ite_eq_right (add_notMem_lattice hz hw), globalOriginFrame, ite_eq_right hz,
      affineX_periodic L C hw, affineY_periodic L C hw, canonicalSigma_automorphy L hw]
    simp only [div_eq_mul_inv, mul_inv]
    ring

theorem globalOriginFrame_eq_originFrame :
    globalOriginFrame L C =ᶠ[𝓝 (0 : ℂ)] originFrame L C := by
  filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds 0,
    (regularY_analytic L C).continuousAt.eventually_ne (regularY_zero_ne L C),
    (sigmaUnit_analytic L).continuousAt.eventually_ne (show sigmaUnit L 0 ≠ 0 by simp)]
    with z hz hy hs
  by_cases hz0 : z = 0
  · subst z
    rw [globalOriginFrame_zero, originFrame_zero]
  · have hzl : z ∉ L.lattice := fun h => hz ⟨h, hz0⟩
    rw [globalOriginFrame, ite_eq_right hzl, originFrame, canonicalSigma_eq_mul_unit,
      regularX_eq L C hz0, regularY_eq L C hz0]
    have hy' : affineY L C z ≠ 0 := by
      intro h
      rw [regularY_eq L C hz0, h, mul_zero] at hy
      exact hy rfl
    field_simp

theorem globalOriginFrame_analytic_zero : AnalyticAt ℂ (globalOriginFrame L C) 0 :=
  (originFrame_analytic L C).congr (globalOriginFrame_eq_originFrame L C).symm

theorem globalOriginFrame_analytic_at_lattice {w : ℂ} (hw : w ∈ L.lattice) :
    AnalyticAt ℂ (globalOriginFrame L C) w := by
  have h := ((globalOriginFrame_analytic_zero L C).div (multiplier_analytic L w 0)
    (multiplier_ne_zero L w 0)).comp_sub w
  simp only [zero_add] at h
  apply h.congr
  exact Filter.Eventually.of_forall fun z => by
    have e := globalOriginFrame_period L C hw (z - w)
    rw [sub_add_cancel] at e
    exact e.symm

theorem globalOriginFrame_ne_zero_at_lattice {w : ℂ} (hw : w ∈ L.lattice) :
    globalOriginFrame L C w ≠ 0 := by
  rw [globalOriginFrame, ite_eq_left hw]
  exact div_ne_zero (neg_ne_zero.mpr (inv_ne_zero (Units.ne_zero C.u)))
    (deriv_canonicalSigma_ne_zero L hw)

theorem globalOriginFrame_analytic_of_notMem {z : ℂ} (hz : z ∉ L.lattice)
    (hy : affineY L C z ≠ 0) : AnalyticAt ℂ (globalOriginFrame L C) z := by
  have hp := L.analyticOnNhd_weierstrassP z hz
  have hd := L.analyticOnNhd_derivWeierstrassP z hz
  have hx : AnalyticAt ℂ (affineX L C) z := by unfold affineX; fun_prop
  have hY : AnalyticAt ℂ (affineY L C) z := by unfold affineY; fun_prop
  apply ((hx.div hY hy).div ((differentiable_canonicalSigma L).analyticAt z)
    ((canonicalSigma_eq_zero_iff L).not.mpr hz)).congr
  filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with y hy
  exact (ite_eq_right hy).symm

theorem globalOriginFrame_ne_zero_of_notMem {z : ℂ} (hz : z ∉ L.lattice)
    (hx : affineX L C z ≠ 0) (hy : affineY L C z ≠ 0) :
    globalOriginFrame L C z ≠ 0 := by
  rw [globalOriginFrame, ite_eq_right hz]
  exact div_ne_zero (div_ne_zero hx hy) ((canonicalSigma_eq_zero_iff L).not.mpr hz)

theorem globalOriginFrame_affine_transition {z : ℂ} (hz : z ∉ L.lattice) :
    globalOriginFrame L C z = (affineX L C z / affineY L C z) * affineFrame L z := by
  rw [globalOriginFrame, ite_eq_right hz, affineFrame, div_eq_mul_inv]

end RHLean.Geometry.NativeCM.WeierstrassTheta
