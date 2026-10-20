import «research.MERTENS_EXPONENT_LOG_LIMSUP»
import RHLean.Analysis.StrongMertensZetaKernel
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Analytic reciprocal supplied by zero confinement

This is the first analytic step of the Mertens converse. It uses the existing
actual zeta function and the existing regularized reciprocal, with value zero
at the zeta pole. Zero confinement supplies holomorphy, including the removable
point at one. No estimate on the Mertens function is assumed or concluded here.
The subsequent growth estimate and inversion are separate obligations.
-/

noncomputable section

namespace RHLean.Analysis.MertensExponent

open Complex Filter Set
open scoped Topology

/-- The open half-plane corresponding to an exponent. -/
def exponentHalfPlane (a : ℝ) : Set ℂ := {s | a < s.re}

theorem exponentHalfPlane_isOpen (a : ℝ) : IsOpen (exponentHalfPlane a) :=
  isOpen_lt continuous_const continuous_re

/-- Strip confinement gives nonvanishing on the entire right half-plane.
The pole is excluded explicitly, regardless of the totalized value of zeta. -/
theorem zeta_ne_zero_of_strip {a : ℝ} (ha : 0 ≤ a)
    (hstrip : ZerosInSymmetricStrip a) {s : ℂ}
    (hs : a < s.re) (_hs1 : s ≠ 1) : riemannZeta s ≠ 0 := by
  by_cases hge : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re hge
  intro hz
  have hzero : NontrivialZetaZero s :=
    ⟨hz, ha.trans_lt hs, lt_of_not_ge hge⟩
  exact (not_le_of_gt hs) (hstrip s hzero).2

/-- Away from the pole, the existing regularization is the literal inverse. -/
theorem regularizedReciprocal_eq_inv {s : ℂ} (hs : s ≠ 1) :
    nativeInvZetaRegularized s = (riemannZeta s)⁻¹ := by
  exact Function.update_of_ne hs 0 (fun z => (riemannZeta z)⁻¹)

/-- Differentiability of the regularized reciprocal away from the pole. -/
theorem regularizedReciprocal_differentiableAt_off_pole {s : ℂ}
    (hs : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    DifferentiableAt ℂ nativeInvZetaRegularized s := by
  apply ((differentiableAt_riemannZeta hs).inv hz).congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hs] with z hz1
  exact regularizedReciprocal_eq_inv hz1

/-- Zero confinement produces an actual holomorphic reciprocal on the whole
open half-plane, including the removable point at one when it is present. -/
theorem regularizedReciprocal_differentiableAt_of_strip {a : ℝ}
    (ha : 0 ≤ a) (hstrip : ZerosInSymmetricStrip a) {s : ℂ}
    (hs : a < s.re) : DifferentiableAt ℂ nativeInvZetaRegularized s := by
  by_cases hs1 : s = 1
  · subst s
    have hH : exponentHalfPlane a ∈ 𝓝 (1 : ℂ) :=
      (exponentHalfPlane_isOpen a).mem_nhds hs
    have hc : ContinuousAt nativeInvZetaRegularized (1 : ℂ) :=
      (nativeInvZetaRegularized_continuousOn
        (K := exponentHalfPlane a)
        (fun z hz hz1 => zeta_ne_zero_of_strip ha hstrip hz hz1)).continuousAt hH
    apply (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      ?_ hc).differentiableAt
    filter_upwards [mem_nhdsWithin_of_mem_nhds hH, self_mem_nhdsWithin] with z hz hz1
    have hz1' : z ≠ (1 : ℂ) := by simpa using! hz1
    exact regularizedReciprocal_differentiableAt_off_pole hz1'
      (zeta_ne_zero_of_strip ha hstrip hz hz1')
  · exact regularizedReciprocal_differentiableAt_off_pole hs1
      (zeta_ne_zero_of_strip ha hstrip hs hs1)

/-- Open-set form for contour deformation. -/
theorem regularizedReciprocal_holomorphic_of_strip {a : ℝ}
    (ha : 0 ≤ a) (hstrip : ZerosInSymmetricStrip a) :
    DifferentiableOn ℂ nativeInvZetaRegularized (exponentHalfPlane a) := by
  intro s hs
  exact (regularizedReciprocal_differentiableAt_of_strip ha hstrip hs).differentiableWithinAt

/-- The regularized reciprocal still agrees with the genuine Mobius L-series
on its original half-plane of absolute convergence. -/
theorem regularizedReciprocal_eq_mellin_classical {s : ℂ}
    (hs : 1 < s.re) : nativeInvZetaRegularized s = mertensMellinContinuation s := by
  have hs1 : s ≠ 1 := by intro h; subst s; norm_num at hs
  rw [regularizedReciprocal_eq_inv hs1]
  have hmul := reciprocal_identity_classical hs
  exact (eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hmul)).symm

end RHLean.Analysis.MertensExponent
