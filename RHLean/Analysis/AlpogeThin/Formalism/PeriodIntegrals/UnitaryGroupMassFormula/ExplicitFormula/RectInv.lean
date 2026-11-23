import Mathlib

/-!
# Reconstructed same-host thin-source dependency

Mathematical source: Levent Alpöge (with Claude).
Source: src/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectInv.lean.
Pinned source: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectInv.lean

This local proof reconstruction adapts the module/namespace boundary to native
RH_Lean. No upstream compiled artifact or terminal RH theorem is imported.
The source archive/mirror states no license; this notice preserves attribution
without assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace RHLean.Analysis.AlpogeThin

namespace PI.EF.PK

open Complex MeasureTheory intervalIntegral Real

lemma vert_inv_right (c d b : ℝ) (w : ℂ) (hb : w.re < b) :
    I • ∫ y : ℝ in c..d, 1 / (((b : ℂ) + y * I) - w) =
      Complex.log (((b : ℂ) + d * I) - w) - Complex.log (((b : ℂ) + c * I) - w) := by
  have hz : ∀ y : ℝ, ((b : ℂ) + y * I - w) ∈ Complex.slitPlane := fun y => by
    rw [Complex.mem_slitPlane_iff]
    left
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
    linarith
  have hne : ∀ y : ℝ, ((b : ℂ) + y * I - w) ≠ 0 := fun y => Complex.slitPlane_ne_zero (hz y)
  have hd : ∀ y : ℝ, HasDerivAt (fun y : ℝ => Complex.log ((b : ℂ) + y * I - w))
      (I * (1 / ((b : ℂ) + y * I - w))) y := by
    intro y
    have h1 : HasDerivAt (fun y : ℝ => (b : ℂ) + y * I - w) I y := by
      simpa using (((hasDerivAt_id y).ofReal_comp.mul_const I).const_add (b : ℂ)).sub_const w
    have h2 := h1.clog_real (hz y)
    convert h2 using 1
    rw [one_div, div_eq_mul_inv]
  rw [smul_eq_mul, ← intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hd y)]
  exact (continuous_const.mul (continuous_const.div (by fun_prop) hne)).intervalIntegrable _ _

end PI.EF.PK

end RHLean.Analysis.AlpogeThin
