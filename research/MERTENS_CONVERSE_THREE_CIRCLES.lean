import Mathlib.Analysis.Complex.Hadamard
import Mathlib

/-!
# A quantitative three-circle interpolation lemma

This general complex-analytic lemma is derived from Mathlib's three-lines
 theorem by composing with the exponential. It is used on a constructed
local logarithm, not directly on a reciprocal with unknown growth.
-/

noncomputable section

namespace RHLean.Analysis.MertensExponent

open Complex Set Filter
open Complex.HadamardThreeLines
open scoped Topology

/-- A convenient, slightly weakened three-circle estimate on the whole
closed inner disk. The constants are at least one, so no boundary norm
positivity or attained supremum is required. -/
theorem threeCircle_power_bound {f : ℂ → ℂ} {r₀ r R A B : ℝ}
    (hr₀ : 0 < r₀) (hr₀r : r₀ < r) (hrR : r < R)
    (hA : 1 ≤ A) (hB : 1 ≤ B)
    (hf : ∀ z : ℂ, ‖z‖ ≤ R → DifferentiableAt ℂ f z)
    (hinner : ∀ z : ℂ, ‖z‖ ≤ r₀ → ‖f z‖ ≤ B)
    (houter : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ A)
    {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖f z‖ ≤ B * A ^ ((Real.log r - Real.log r₀) / (Real.log R - Real.log r₀)) := by
  have hr : 0 < r := hr₀.trans hr₀r
  have hR : 0 < R := hr.trans hrR
  have hlogs : Real.log r₀ < Real.log R := Real.log_lt_log hr₀ (hr₀r.trans hrR)
  have hden : 0 < Real.log R - Real.log r₀ := sub_pos.mpr hlogs
  have htheta0 : 0 ≤ (Real.log r - Real.log r₀) / (Real.log R - Real.log r₀) :=
    div_nonneg (sub_nonneg.mpr (Real.log_le_log hr₀ hr₀r.le)) hden.le
  by_cases hsmall : ‖z‖ ≤ r₀
  · exact (hinner z hsmall).trans (le_mul_of_one_le_right (by linarith)
      (Real.one_le_rpow hA htheta0))
  have hzpos : 0 < ‖z‖ := hr₀.trans (lt_of_not_ge hsmall)
  have hz0 : z ≠ 0 := norm_pos_iff.mp hzpos
  let g : ℂ → ℂ := fun w => f (Complex.exp w)
  have hexp (w : ℂ) (hw : w.re ≤ Real.log R) : ‖Complex.exp w‖ ≤ R := by
    rw [Complex.norm_exp]
    exact (Real.exp_le_exp.mpr hw).trans_eq (Real.exp_log hR)
  have hclosure : closure (verticalStrip (Real.log r₀) (Real.log R)) ⊆
      verticalClosedStrip (Real.log r₀) (Real.log R) := by
    apply closure_minimal
    · intro w hw
      exact ⟨hw.1.le, hw.2.le⟩
    · exact isClosed_Icc.preimage continuous_re
  have hdiff : DiffContOnCl ℂ g (verticalStrip (Real.log r₀) (Real.log R)) := by
    apply DifferentiableOn.diffContOnCl
    intro w hw
    have hd := (hf (Complex.exp w) (hexp w (hclosure hw).2)).comp w
      Complex.differentiable_exp.differentiableAt
    exact hd.differentiableWithinAt
  have hbounded : BddAbove ((norm ∘ g) ''
      verticalClosedStrip (Real.log r₀) (Real.log R)) := by
    refine ⟨A, ?_⟩
    rintro y ⟨w, hw, rfl⟩
    exact houter (Complex.exp w) (hexp w hw.2)
  have hleft : ∀ w ∈ Complex.re ⁻¹' {Real.log r₀}, ‖g w‖ ≤ B := by
    intro w hw
    apply hinner
    change w.re = Real.log r₀ at hw
    rw [Complex.norm_exp, hw, Real.exp_log hr₀]
  have hright : ∀ w ∈ Complex.re ⁻¹' {Real.log R}, ‖g w‖ ≤ A := by
    intro w hw
    apply houter
    change w.re = Real.log R at hw
    rw [Complex.norm_exp, hw, Real.exp_log hR]
  have hpoint : Complex.log z ∈ verticalClosedStrip (Real.log r₀) (Real.log R) := by
    change Real.log r₀ ≤ (Complex.log z).re ∧ (Complex.log z).re ≤ Real.log R
    rw [Complex.log_re]
    exact ⟨Real.log_le_log hr₀ (lt_of_not_ge hsmall).le,
      Real.log_le_log hzpos (hz.trans hrR.le)⟩
  have hthree := norm_le_interp_of_mem_verticalClosedStrip'
    hlogs hpoint hdiff hbounded hleft hright
  simp only [g, Complex.exp_log hz0, Complex.log_re] at hthree
  have htheta : 0 ≤ (Real.log ‖z‖ - Real.log r₀) / (Real.log R - Real.log r₀) :=
    div_nonneg (sub_nonneg.mpr (Real.log_le_log hr₀ (lt_of_not_ge hsmall).le)) hden.le
  have htheta_le : (Real.log ‖z‖ - Real.log r₀) / (Real.log R - Real.log r₀) ≤
      (Real.log r - Real.log r₀) / (Real.log R - Real.log r₀) := by
    exact div_le_div_of_nonneg_right
      (sub_le_sub_right (Real.log_le_log hzpos hz) _) hden.le
  have hBpow : B ^ (1 - (Real.log ‖z‖ - Real.log r₀) / (Real.log R - Real.log r₀)) ≤ B := by
    simpa only [Real.rpow_one] using! Real.rpow_le_rpow_of_exponent_le hB
      (show 1 - (Real.log ‖z‖ - Real.log r₀) / (Real.log R - Real.log r₀) ≤ 1 by linarith)
  exact hthree.trans (mul_le_mul hBpow
    (Real.rpow_le_rpow_of_exponent_le hA htheta_le)
    (Real.rpow_nonneg (by linarith) _) (by linarith))

/-- The interpolation exponent is strictly between zero and one. -/
theorem threeCircle_exponent_mem_Ioo {r₀ r R : ℝ}
    (hr₀ : 0 < r₀) (hr₀r : r₀ < r) (hrR : r < R) :
    (Real.log r - Real.log r₀) / (Real.log R - Real.log r₀) ∈ Set.Ioo (0 : ℝ) 1 := by
  have hnum : 0 < Real.log r - Real.log r₀ :=
    sub_pos.mpr (Real.log_lt_log hr₀ hr₀r)
  have hden : 0 < Real.log R - Real.log r₀ :=
    sub_pos.mpr (Real.log_lt_log hr₀ (hr₀r.trans hrR))
  refine ⟨div_pos hnum hden, ?_⟩
  apply (div_lt_one hden).mpr
  exact sub_lt_sub_right (Real.log_lt_log (hr₀.trans hr₀r) hrR) _

end RHLean.Analysis.MertensExponent
