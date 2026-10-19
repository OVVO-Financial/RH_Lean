import «research.MERTENS_CONVERSE_LOG_INTERPOLATION»
import «research.MERTENS_CONVERSE_ZETA_BOUNDS»

/-!
# Reciprocal zeta has subpower growth inside a zero-free half-plane

All constants are uniform over the stated interior vertical strip. The proof
constructs normalized local logarithms of the actual zeta function, bounds
those logarithms by Borel-Caratheodory and three-circle interpolation, and
then absorbs the stretched logarithm into an arbitrary positive power.
No bound on Mertens sums or inverse transforms is a hypothesis of this file.
-/

noncomputable section

namespace RHLean.Analysis.MertensExponent

open Complex Filter Set
open scoped Topology
local notation "I" => Complex.I

/-- A stretched-log bound, with exponent strictly less than one, uniformly
on any closed vertical strip strictly inside the zero-free half-plane. -/
theorem reciprocal_stretchedLog_of_strip {a σ : ℝ}
    (ha : 0 ≤ a) (haσ : a < σ) (hσ : σ < 1)
    (hstrip : ZerosInSymmetricStrip a) :
    ∃ θ C K : ℝ, 0 < θ ∧ θ < 1 ∧ 0 < C ∧ 1 ≤ K ∧
      ∀ s : ℂ, σ ≤ s.re → s.re ≤ 2 → 4 ≤ |s.im| →
        ‖(riemannZeta s)⁻¹‖ ≤ K * Real.exp (C * (Real.log |s.im|) ^ θ) := by
  let r : ℝ := (2 - σ) / 4
  let R₁ : ℝ := (2 - (a + σ) / 2) / 4
  let b : ℝ := (3 * a + σ) / 4
  let R₂ : ℝ := (2 - b) / 4
  let R₃ : ℝ := (2 - (7 * a + σ) / 8) / 4
  have hσ0 : 0 < σ := ha.trans_lt haσ
  have hr : (1 : ℝ) / 16 < r := by dsimp [r]; linarith
  have hr₁ : r < R₁ := by dsimp [r, R₁]; linarith
  have h12 : R₁ < R₂ := by dsimp [R₁, R₂, b]; linarith
  have h23 : R₂ < R₃ := by dsimp [R₂, R₃, b]; linarith
  have h34 : R₃ < (3 : ℝ) / 4 := by dsimp [R₃]; linarith
  have hsmall : (1 : ℝ) / 8 ≤ R₂ := by dsimp [R₂, b]; linarith
  have hR₂half : R₂ ≤ (1 : ℝ) / 2 := by dsimp [R₂, b]; linarith
  have hb : 0 < b := by dsimp [b]; linarith
  let D : ℝ := 8 + 8 / b
  have hD : 1 ≤ D := by
    dsimp [D]
    have hquot : 0 ≤ (8 : ℝ) / b := div_nonneg (by norm_num) hb.le
    linarith
  obtain ⟨E, hE, hEbound⟩ := zeta_bounded_right_halfPlane
    (u := (3 : ℝ) / 2) (by norm_num)
  obtain ⟨K₀, hK₀, hKbound⟩ := strongMertens_inv_zeta_bdd_on_vertical_line_gt_one
    (sigma0 := 2) (by norm_num)
  let K : ℝ := K₀ + 1
  have hK : 1 ≤ K := by dsimp [K]; linarith
  obtain ⟨C, hC, hlocal⟩ := reciprocal_stretchedLog_of_local_data
    hr hr₁ h12 h23 h34 (by norm_num : (3 : ℝ) / 4 < 1)
    hsmall hD hE hK
  let θ : ℝ := logInterpolationExponent r R₁
  have hθ : θ ∈ Set.Ioo (0 : ℝ) 1 :=
    threeCircle_exponent_mem_Ioo (by norm_num) hr hr₁
  refine ⟨θ, C, K, hθ.1, hθ.2, hC, hK, ?_⟩
  intro s hsσ hs2 hsT
  let t := s.im
  let F : ℂ → ℂ := fun w => riemannZeta (zetaDiscPoint t w)
  have hF : AnalyticOnNhd ℂ F (Metric.closedBall (0 : ℂ) (3 / 4)) := by
    intro w hw
    have hwnorm : ‖w‖ ≤ (3 : ℝ) / 4 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using! hw
    have hne := zetaDiscPoint_ne_one hsT hwnorm
    have haff : AnalyticAt ℂ (zetaDiscPoint t) w := by
      unfold zetaDiscPoint
      exact analyticAt_const.add (analyticAt_const.mul analyticAt_id)
    exact (analyticAt_riemannZeta hne).comp haff
  have hFne : ∀ w ∈ Metric.closedBall (0 : ℂ) R₃, F w ≠ 0 := by
    intro w hw
    have hwnorm : ‖w‖ ≤ R₃ := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using! hw
    have hwsmall : ‖w‖ ≤ (3 : ℝ) / 4 := hwnorm.trans h34.le
    apply zeta_ne_zero_of_strip ha hstrip _ (zetaDiscPoint_ne_one hsT hwsmall)
    rw [zetaDiscPoint_re]
    have hwr := (neg_le_abs w.re).trans (Complex.abs_re_le_norm w)
    dsimp [R₃] at hwnorm
    linarith
  have hFinv0 : ‖(F 0)⁻¹‖ ≤ K := by
    have h := hKbound t
    simpa only [F, zetaDiscPoint, mul_zero, add_zero] using!
      h.trans (show K₀ ≤ K by dsimp [K]; linarith)
  have hFinner : ∀ w : ℂ, ‖w‖ ≤ (1 : ℝ) / 8 → ‖F w‖ ≤ E := by
    intro w hw
    apply hEbound
    rw [zetaDiscPoint_re]
    have hwr := (neg_le_abs w.re).trans (Complex.abs_re_le_norm w)
    linarith
  have hFouter : ∀ w : ℂ, ‖w‖ ≤ R₂ → ‖F w‖ ≤ D * |t| := by
    intro w hw
    apply zeta_norm_le_on_shifted_disk hb hsT (hw.trans hR₂half)
    rw [zetaDiscPoint_re]
    have hwr := (neg_le_abs w.re).trans (Complex.abs_re_le_norm w)
    dsimp [R₂] at hw
    linarith
  let w : ℂ := (((s.re - 2) / 4 : ℝ) : ℂ)
  have hw : ‖w‖ ≤ r := by
    change ‖(((s.re - 2) / 4 : ℝ) : ℂ)‖ ≤ r
    rw [Complex.norm_real, Real.norm_eq_abs]
    apply abs_le.mpr
    dsimp [r]
    constructor <;> linarith
  have heq : zetaDiscPoint t w = s := by
    apply Complex.ext
    · simp only [zetaDiscPoint_re, w, Complex.ofReal_re]
      ring
    · simp only [zetaDiscPoint_im, w, Complex.ofReal_im, mul_zero, add_zero, t]
  have hlog : 1 ≤ Real.log |t| :=
    (logt_gt_one (by dsimp [t]; linarith : 3 ≤ |t|)).le
  have h := hlocal |t| hlog F hF hFne hFinv0 hFinner hFouter w hw
  simpa only [F, heq, t, θ] using! h

/-- A stretched logarithm with exponent below one is absorbed by every
positive power. This is an asymptotic estimate, not a finite-height test. -/
theorem exp_stretchedLog_eventually_le_rpow {θ C η : ℝ}
    (hθ : θ < 1) (hη : 0 < η) :
    ∀ᶠ T : ℝ in atTop,
      Real.exp (C * (Real.log T) ^ θ) ≤ T ^ η := by
  have hlim : Tendsto (fun T : ℝ => C * (Real.log T) ^ (θ - 1)) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := C)).mul
      ((_root_.tendsto_rpow_neg_atTop (sub_pos.mpr hθ)).comp Real.tendsto_log_atTop)
    simpa only [mul_zero, neg_sub] using! h
  filter_upwards [hlim.eventually (gt_mem_nhds hη),
    eventually_ge_atTop (3 : ℝ)] with T hsmall hT
  have hTpos : 0 < T := by linarith
  have hlog : 0 < Real.log T := zero_lt_one.trans (logt_gt_one hT)
  have hpow : (Real.log T) ^ θ = (Real.log T) ^ (θ - 1) * Real.log T := by
    calc
      (Real.log T) ^ θ = (Real.log T) ^ ((θ - 1) + 1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hlog, Real.rpow_one]
  rw [Real.rpow_def_of_pos hTpos]
  apply Real.exp_le_exp.mpr
  rw [hpow]
  have h := mul_le_mul_of_nonneg_right hsmall.le hlog.le
  nlinarith

/-- Uniform subpower control of the actual regularized reciprocal on every
closed interior strip. The constant may depend on the strip and eta, but not
on s or its height. The pole's removable value is handled explicitly. -/
theorem regularizedReciprocal_subpower_of_strip {a σ η : ℝ}
    (ha : 0 ≤ a) (haσ : a < σ) (hσ : σ < 1)
    (hstrip : ZerosInSymmetricStrip a) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, σ ≤ s.re → s.re ≤ 2 →
      ‖nativeInvZetaRegularized s‖ ≤ C * (1 + |s.im|) ^ η := by
  obtain ⟨θ, D, K, _hθ0, hθ1, hD, hK, hlarge⟩ :=
    reciprocal_stretchedLog_of_strip ha haσ hσ hstrip
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp
    (exp_stretchedLog_eventually_le_rpow (C := D) hθ1 hη)
  let U : ℝ := max 4 T₀
  let box : Set ℂ := (Set.Icc σ 2) ×ℂ (Set.Icc (-U) U)
  have hbox : IsCompact box := isCompact_Icc.reProdIm isCompact_Icc
  have hcontinuous : ContinuousOn nativeInvZetaRegularized box := by
    apply (regularizedReciprocal_holomorphic_of_strip ha hstrip).continuousOn.mono
    intro s hs
    have hreal := (Complex.mem_reProdIm.mp hs).1.1
    exact haσ.trans_le hreal
  obtain ⟨B, hB⟩ := hbox.exists_bound_of_continuousOn hcontinuous
  let C : ℝ := |B| + K + 1
  have hC : 0 < C := by dsimp [C]; have := abs_nonneg B; linarith
  have hKC : K ≤ C := by dsimp [C]; have := abs_nonneg B; linarith
  have hBC : B ≤ C := by dsimp [C]; have := le_abs_self B; linarith
  refine ⟨C, hC, ?_⟩
  intro s hsσ hs2
  by_cases ht : U ≤ |s.im|
  · have ht4 : 4 ≤ |s.im| := (le_max_left _ _).trans ht
    have htT₀ : T₀ ≤ |s.im| := (le_max_right _ _).trans ht
    have hs1 : s ≠ 1 := by intro h; subst s; norm_num at ht4
    rw [regularizedReciprocal_eq_inv hs1]
    calc
      ‖(riemannZeta s)⁻¹‖ ≤ K * Real.exp (D * (Real.log |s.im|) ^ θ) :=
        hlarge s hsσ hs2 ht4
      _ ≤ K * |s.im| ^ η :=
        mul_le_mul_of_nonneg_left (hT₀ _ htT₀) (by linarith)
      _ ≤ C * (1 + |s.im|) ^ η := mul_le_mul hKC
        (Real.rpow_le_rpow (abs_nonneg _) (by linarith) hη.le)
        (Real.rpow_nonneg (abs_nonneg _) _) hC.le
  · have htU : |s.im| ≤ U := (lt_of_not_ge ht).le
    have hsbox : s ∈ box := by
      apply Complex.mem_reProdIm.mpr
      exact ⟨⟨hsσ, hs2⟩, abs_le.mp htU⟩
    exact ((hB s hsbox).trans hBC).trans
      (le_mul_of_one_le_right hC.le
        (Real.one_le_rpow (by have := abs_nonneg s.im; linarith) hη.le))

end RHLean.Analysis.MertensExponent
