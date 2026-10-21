import Mathlib
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles

/-!
# A residue-free vertical contour shift

This is a general analytic theorem. It does not assume any arithmetic bound.
Integrable endpoint lines and vanishing horizontal sides yield equality of
the full vertical integrals by the finite rectangle theorem and an actual
improper-integral limit.
-/

noncomputable section

namespace RHLean.Analysis.MertensExponent

open Complex Filter Set MeasureTheory
open scoped Topology Interval
local notation "I" => Complex.I

/-- Uniform norm control that tends to zero makes a bounded horizontal
segment tend to zero. The height may be any function of the limit parameter. -/
theorem horizontalIntegral_tendsto_zero_of_bound
    {f : ℂ → ℂ} {l r : ℝ} (hlr : l ≤ r) {y B : ℝ → ℝ}
    (hB : Tendsto B atTop (𝓝 0))
    (hbound : ∀ᶠ T : ℝ in atTop, ∀ x ∈ Set.Icc l r,
      ‖f ((x : ℂ) + (y T : ℂ) * I)‖ ≤ B T) :
    Tendsto (fun T : ℝ => HIntegral f l r (y T)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun T : ℝ => B T * |r - l|) atTop (𝓝 0) := by
    simpa only [zero_mul] using! hB.mul_const |r - l|
  apply squeeze_zero_norm' _ hlim
  filter_upwards [hbound] with T hT
  unfold HIntegral
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro x hx
  have hx' : x ∈ Set.Ioc l r := by simpa only [Set.uIoc_of_le hlr] using! hx
  exact hT x ⟨hx'.1.le, hx'.2⟩

/-- Shift the full vertical integral across a closed strip. There is no
unproved contour-shift assumption: finite rectangles and their limits are
assembled in this theorem. -/
theorem verticalIntegral_eq_of_holomorphic_and_horizontal_limits
    {f : ℂ → ℂ} {l r : ℝ} (hlr : l ≤ r)
    (hf : ∀ z : ℂ, l ≤ z.re → z.re ≤ r → DifferentiableAt ℂ f z)
    (hil : Integrable (fun t : ℝ => f ((l : ℂ) + t * I)))
    (hir : Integrable (fun t : ℝ => f ((r : ℂ) + t * I)))
    (hplus : Tendsto (fun T : ℝ => HIntegral f l r T) atTop (𝓝 0))
    (hminus : Tendsto (fun T : ℝ => HIntegral f l r (-T)) atTop (𝓝 0)) :
    VerticalIntegral' f l = VerticalIntegral' f r := by
  have hfOn : HolomorphicOn f {z : ℂ | l ≤ z.re ∧ z.re ≤ r} := by
    intro z hz
    exact (hf z hz.1 hz.2).differentiableWithinAt
  have hrect (T : ℝ) :
      HIntegral f l r (-T) - HIntegral f l r T +
        VIntegral f r (-T) T - VIntegral f l (-T) T = 0 := by
    have hsub : Rectangle ((l : ℂ) + (-T : ℝ) * I) ((r : ℂ) + T * I) ⊆
        {z : ℂ | l ≤ z.re ∧ z.re ≤ r} := by
      intro z hz
      have hreal := (Complex.mem_reProdIm.mp hz).1
      simpa [Set.uIcc_of_le hlr] using! hreal
    have h := hfOn.vanishesOnRectangle hsub
    simpa [RectangleIntegral] using! h
  have heq (T : ℝ) : VIntegral f l (-T) T - VIntegral f r (-T) T =
      HIntegral f l r (-T) - HIntegral f l r T := by
    have h := hrect T
    linear_combination -h
  have hl : Tendsto (fun T : ℝ => VIntegral f l (-T) T)
      atTop (𝓝 (VerticalIntegral f l)) := by
    simpa only [VIntegral, VerticalIntegral] using!
      (intervalIntegral_tendsto_integral hil tendsto_neg_atTop_atBot tendsto_id).const_smul I
  have hr : Tendsto (fun T : ℝ => VIntegral f r (-T) T)
      atTop (𝓝 (VerticalIntegral f r)) := by
    simpa only [VIntegral, VerticalIntegral] using!
      (intervalIntegral_tendsto_integral hir tendsto_neg_atTop_atBot tendsto_id).const_smul I
  have hzero : VerticalIntegral f l - VerticalIntegral f r = 0 := by
    exact tendsto_nhds_unique ((hl.sub hr).congr heq)
      (by simpa only [sub_zero] using! hminus.sub hplus)
  exact congrArg (fun z : ℂ => (1 / (2 * Real.pi * I)) • z) (sub_eq_zero.mp hzero)

end RHLean.Analysis.MertensExponent
