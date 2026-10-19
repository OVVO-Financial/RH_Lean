import «research.MERTENS_CONVERSE_KERNEL»
import RHLean.Analysis.StrongMertensSmoothing

/-!
# Quantitative inversion inside a zero-free half-plane

The original smoothed Mobius transform is shifted from its classical Perron
line to an arbitrary interior line. Every horizontal limit and vertical
integrability assertion is supplied by the proved kernel bound. This file
therefore contains an inversion estimate, not an assumed Perron criterion.
-/

noncomputable section

namespace RHLean.Analysis.MertensExponent

open Complex Filter Set MeasureTheory
open scoped Topology
local notation "I" => Complex.I

/-- The integrable height majorant also tends to zero at positive infinity. -/
theorem converseHeightWeight_tendsto_zero {q : ℝ} (hq : 0 < q) :
    Tendsto (converseHeightWeight q) atTop (𝓝 0) := by
  have hpos : 0 < 1 + q / 2 := by linarith
  have h := (_root_.tendsto_rpow_neg_atTop hpos).comp
    (tendsto_atTop_add_const_left atTop (1 : ℝ) tendsto_id)
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  simp only [Function.comp_apply, converseHeightWeight, abs_of_nonneg ht]
  congr 1
  ring

/-- Equality of actual integrands on a vertical line preserves its integral. -/
theorem verticalIntegral_congr_line {f g : ℂ → ℂ} {u : ℝ}
    (h : ∀ t : ℝ, f ((u : ℂ) + t * I) = g ((u : ℂ) + t * I)) :
    VerticalIntegral' f u = VerticalIntegral' g u := by
  have hi : (∫ t : ℝ, f ((u : ℂ) + t * I)) =
      ∫ t : ℝ, g ((u : ℂ) + t * I) := integral_congr_ae (Filter.Eventually.of_forall h)
  simp only [VerticalIntegral', VerticalIntegral, hi]

/-- The true smoothed Mobius transform has power growth on every interior
line. The smoothing loss is the arbitrarily small positive exponent q. -/
theorem smoothedMobius_bound_of_strip
    {a σ q : ℝ} (ha : 0 ≤ a) (haσ : a < σ) (hσ : σ < 1)
    (hstrip : ZerosInSymmetricStrip a) (hq : 0 < q) (hq1 : q ≤ 1)
    {ν : ℝ → ℝ} (hdiff : ContDiff ℝ 1 ν)
    (hsupp : Function.support ν ⊆ Set.Icc (1 / 2) 2)
    (hnonneg : ∀ x > 0, 0 ≤ ν x)
    (hmass : ∫ x in Set.Ioi (0 : ℝ), ν x / x = 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε X : ℝ, 0 < ε → ε < 1 → 3 < X →
      ‖nativeSmoothedMobius ν ε X‖ ≤ C * ε ^ (-q) * X ^ σ := by
  obtain ⟨K, hK, hbound⟩ := regularizedSmoothedIntegrand_bound
    ha haσ hσ hstrip hq hq1 hdiff hsupp
  refine ⟨converseIntegralConstant q * K,
    mul_pos (converseIntegralConstant_pos q) hK, ?_⟩
  intro ε X hε hε1 hX3
  have hX : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hlog : 1 < Real.log X := logt_gt_one hX3.le
  have hlog0 : 0 < Real.log X := by linarith
  let c : ℝ := 1 + (Real.log X)⁻¹
  have hc1 : 1 < c := by dsimp [c]; exact lt_add_of_pos_right _ (inv_pos.mpr hlog0)
  have hc2 : c ≤ 2 := by
    have hinv : (Real.log X)⁻¹ ≤ 1 := by
      simpa only [one_div, inv_one] using! one_div_le_one_div_of_le zero_lt_one hlog.le
    dsimp [c]
    linarith
  have hσc : σ ≤ c := (hσ.trans hc1).le
  let f : ℂ → ℂ := regularizedSmoothedIntegrand ν ε X
  have hcoef0 : 0 ≤ K * ε ^ (-q) := mul_nonneg hK.le (Real.rpow_nonneg hε.le _)
  have hlineBound (u : ℝ) (huσ : σ ≤ u) (hu2 : u ≤ 2) (t : ℝ) :
      ‖f ((u : ℂ) + t * I)‖ ≤
        (K * ε ^ (-q) * X ^ u) * converseHeightWeight q t := by
    have h := hbound ε X hε hε1 hX ((u : ℂ) + t * I)
      (by simpa using! huσ) (by simpa using! hu2)
    simpa only [f, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero, add_zero, Complex.add_im, Complex.mul_im, mul_one, zero_add] using! h
  have hlineContinuous (u : ℝ) (hau : a < u) :
      Continuous (fun t : ℝ => f ((u : ℂ) + t * I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hd := regularizedSmoothedIntegrand_differentiableAt ha hstrip hdiff hsupp
      hnonneg hmass hε hε1 hX (s := (u : ℂ) + t * I) (by simpa using! hau)
    have hpath : ContinuousAt (fun v : ℝ => (u : ℂ) + (v : ℂ) * I) t := by
      fun_prop
    exact ContinuousAt.comp (f := fun v : ℝ => (u : ℂ) + (v : ℂ) * I)
      (g := regularizedSmoothedIntegrand ν ε X) (x := t) hd.continuousAt hpath
  have hil : Integrable (fun t : ℝ => f ((σ : ℂ) + t * I)) :=
    integrable_vertical_of_heightBound hq (hlineContinuous σ haσ)
      (hlineBound σ le_rfl (by linarith))
  have hir : Integrable (fun t : ℝ => f ((c : ℂ) + t * I)) :=
    integrable_vertical_of_heightBound hq (hlineContinuous c (haσ.trans_le hσc))
      (hlineBound c hσc hc2)
  have hheight (t x : ℝ) (hx : x ∈ Set.Icc σ c) :
      ‖f ((x : ℂ) + t * I)‖ ≤
        (K * ε ^ (-q) * X ^ (2 : ℝ)) * converseHeightWeight q t := by
    have hx2 : x ≤ 2 := hx.2.trans hc2
    exact (hlineBound x hx.1 hx2 t).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hX1 hx2) hcoef0)
        (converseHeightWeight_nonneg q t))
  have hB : Tendsto
      (fun T : ℝ => (K * ε ^ (-q) * X ^ (2 : ℝ)) * converseHeightWeight q T)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using!
      (converseHeightWeight_tendsto_zero hq).const_mul (K * ε ^ (-q) * X ^ (2 : ℝ))
  have hplus : Tendsto (fun T : ℝ => HIntegral f σ c T) atTop (𝓝 0) := by
    apply horizontalIntegral_tendsto_zero_of_bound hσc hB
    exact Filter.Eventually.of_forall (fun T x hx => hheight T x hx)
  have hminus : Tendsto (fun T : ℝ => HIntegral f σ c (-T)) atTop (𝓝 0) := by
    apply horizontalIntegral_tendsto_zero_of_bound hσc hB
    apply Filter.Eventually.of_forall
    intro T x hx
    simpa only [converseHeightWeight, abs_neg] using! hheight (-T) x hx
  have hshift : VerticalIntegral' f σ = VerticalIntegral' f c := by
    apply verticalIntegral_eq_of_holomorphic_and_horizontal_limits hσc
      (fun z hz _ => regularizedSmoothedIntegrand_differentiableAt
        ha hstrip hdiff hsupp hnonneg hmass hε hε1 hX (haσ.trans_le hz))
      hil hir hplus hminus
  have hclassical : nativeSmoothedMobius ν ε X = VerticalIntegral' f c := by
    change VerticalIntegral' (nativeSmoothedMobiusIntegrand ν ε X) c = VerticalIntegral' f c
    apply verticalIntegral_congr_line
    intro t
    symm
    apply regularizedSmoothedIntegrand_eq_native
    intro heq
    have hreal := congrArg Complex.re heq
    have hcEq : c = 1 := by simpa using! hreal
    linarith
  rw [hclassical, ← hshift]
  have h := verticalIntegral_norm_le_heightBound hq
    (mul_nonneg hcoef0 (Real.rpow_nonneg hX.le σ))
    (hlineBound σ le_rfl (by linarith))
  simpa only [mul_assoc] using! h

end RHLean.Analysis.MertensExponent
