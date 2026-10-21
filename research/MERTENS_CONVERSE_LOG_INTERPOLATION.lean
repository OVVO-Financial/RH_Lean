import «research.MERTENS_CONVERSE_RECIPROCAL»
import «research.MERTENS_CONVERSE_THREE_CIRCLES»

/-!
# Local logarithms and subpower reciprocal growth

This is an independent complex-analytic interpolation theorem. Its hypotheses
are local nonvanishing and explicit polynomial norm bounds. The logarithm is
constructed by the existing analytic primitive theorem; it is not postulated.
The constants in the conclusion are uniform over the height parameter and the
analytic function whenever the displayed local data are uniform.
-/

noncomputable section

namespace RHLean.Analysis.MertensExponent

open Complex Filter Set
open scoped Topology

-- The historical StrongPNT disk helpers are replaced by the pinned PNT+
-- Borel-Caratheodory theorem. These helpers preserve their exact old interface.
private def ballDR (R : ℝ) : Set ℂ := Metric.ball (0 : ℂ) R

private theorem lem_ballDR (R : ℝ) (hR : 0 < R) :
    closure (ballDR R) = Metric.closedBall (0 : ℂ) R := by
  unfold ballDR
  exact closure_ball 0 (ne_of_gt hR)

private theorem lem_BCI (R M : ℝ) (hR : 0 < R) (hM : 0 < M)
    (f : ℂ → ℂ)
    (hAnalytic : AnalyticOn ℂ f (closure (ballDR R)))
    (hZero : f 0 = 0)
    (hRe : ∀ w : ℂ, w ∈ closure (ballDR R) → (f w).re ≤ M)
    (r : ℝ) (_hr : 0 < r) (hrR : r < R)
    (z : ℂ) (hz : ‖z‖ ≤ r) :
    ‖f z‖ ≤ (2 * r / (R - r)) * M := by
  have hc : closure (ballDR R) = Metric.closedBall (0 : ℂ) R :=
    lem_ballDR R hR
  have ha : AnalyticOn ℂ f (Metric.ball 0 R) := by
    apply hAnalytic.mono
    rw [hc]
    exact Metric.ball_subset_closedBall
  have hb : ∀ w ∈ Metric.ball (0 : ℂ) R, (f w).re ≤ M := by
    intro w hw
    exact hRe w (by rw [hc]; exact Metric.ball_subset_closedBall hw)
  have hpoint : z ∈ Metric.closedBall (0 : ℂ) r := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  have hbc := borelCaratheodory' hM hR hrR ha hZero hb hpoint
  convert hbc using 1
  ring

/-- The exponent in the three-circle estimate. -/
def logInterpolationExponent (r R : ℝ) : ℝ :=
  (Real.log r - Real.log (1 / 16)) / (Real.log R - Real.log (1 / 16))

/-- Two Borel-Caratheodory estimates, followed by three-circle interpolation,
turn a polynomial bound for a nonvanishing analytic function into a stretched
logarithmic bound for its reciprocal on an interior disk. -/
theorem reciprocal_stretchedLog_of_local_data
    {r R₁ R₂ R₃ R₄ D E K : ℝ}
    (hr : (1 : ℝ) / 16 < r) (hr₁ : r < R₁)
    (h12 : R₁ < R₂) (h23 : R₂ < R₃) (h34 : R₃ < R₄)
    (h4 : R₄ < 1) (hsmall : (1 : ℝ) / 8 ≤ R₂)
    (hD : 1 ≤ D) (hE : 1 ≤ E) (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ Real.log T →
      ∀ F : ℂ → ℂ,
        AnalyticOnNhd ℂ F (Metric.closedBall (0 : ℂ) R₄) →
        (∀ z ∈ Metric.closedBall (0 : ℂ) R₃, F z ≠ 0) →
        ‖(F 0)⁻¹‖ ≤ K →
        (∀ z : ℂ, ‖z‖ ≤ (1 : ℝ) / 8 → ‖F z‖ ≤ E) →
        (∀ z : ℂ, ‖z‖ ≤ R₂ → ‖F z‖ ≤ D * T) →
        ∀ z : ℂ, ‖z‖ ≤ r →
          ‖(F z)⁻¹‖ ≤ K * Real.exp
            (C * (Real.log T) ^ logInterpolationExponent r R₁) := by
  have hr0 : 0 < r := lt_trans (by norm_num) hr
  have hR10 : 0 < R₁ := hr0.trans hr₁
  have hR20 : 0 < R₂ := hR10.trans h12
  have hR30 : 0 < R₃ := hR20.trans h23
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hE0 : 0 < E := lt_of_lt_of_le zero_lt_one hE
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  let θ := logInterpolationExponent r R₁
  have hθ : θ ∈ Set.Ioo (0 : ℝ) 1 :=
    threeCircle_exponent_mem_Ioo (by norm_num) hr hr₁
  let A₀ : ℝ := (2 * R₁ / (R₂ - R₁)) * (D + K + 1)
  have hgap : 0 < R₂ - R₁ := sub_pos.mpr h12
  have hA₀ : 0 < A₀ := by dsimp [A₀]; positivity
  let H : ℝ := A₀ + 1
  have hH : 1 ≤ H := by dsimp [H]; linarith
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  let B : ℝ := 2 * (E + K) + 1
  have hB : 1 ≤ B := by dsimp [B]; linarith
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  let C : ℝ := B * H ^ θ
  have hC : 0 < C := mul_pos hB0 (Real.rpow_pos_of_pos hH0 θ)
  refine ⟨C, hC, ?_⟩
  intro T hT F hF hne hinv0 hinner houter z hz
  have hL0 : 0 < Real.log T := zero_lt_one.trans_le hT
  have hTpos : 0 < T := by
    by_contra hnot
    have hnonpos : T ≤ 0 := le_of_not_gt hnot
    have hF0 : F 0 ≠ 0 := hne 0 (by simpa using! hR30.le)
    have hout0 := houter 0 (by simpa using! hR20.le)
    have hprod : D * T ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hD0.le hnonpos
    exact (not_le_of_gt (norm_pos_iff.mpr hF0)) (hout0.trans hprod)
  -- PNT+ proves the modern analytic-log theorem on the larger open disk.
  obtain ⟨J, hJopen, hJ0, _hJderiv, hJreOpen⟩ :=
    LogOfAnalyticFunction' hR20 h23 h34 hF hne
  have hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) R₂) :=
    hJopen.mono (Metric.closedBall_subset_ball h23)
  have hJre (w : ℂ) (hw : w ∈ Metric.closedBall (0 : ℂ) R₂) :
      Real.log ‖F w‖ - Real.log ‖F 0‖ = (J w).re :=
    hJreOpen w (Metric.closedBall_subset_ball h23 hw)
  have hJanalytic (S : ℝ) (hS : 0 < S) (hSR : S ≤ R₂) :
      AnalyticOn ℂ J (closure (ballDR S)) := by
    rw [lem_ballDR S hS]
    exact hJ.analyticOn.mono (Metric.closedBall_subset_closedBall hSR)
  have hFnonzero (w : ℂ) (hw : ‖w‖ ≤ R₂) : F w ≠ 0 := by
    apply hne
    simpa only [Metric.mem_closedBall, dist_zero_right] using! hw.trans h23.le
  have hFzero : F 0 ≠ 0 := hFnonzero 0 (by simpa using! hR20.le)
  have hlogInv0 : -Real.log ‖F 0‖ ≤ Real.log K := by
    rw [← Real.log_inv]
    apply Real.log_le_log (inv_pos.mpr (norm_pos_iff.mpr hFzero))
    simpa only [norm_inv] using! hinv0
  have hJsmallRe : ∀ w : ℂ, ‖w‖ ≤ (1 : ℝ) / 8 → (J w).re ≤ E + K := by
    intro w hw
    have hwR : ‖w‖ ≤ R₂ := hw.trans hsmall
    rw [← hJre w (by simpa only [Metric.mem_closedBall, dist_zero_right] using! hwR)]
    have hlogF := Real.log_le_log (norm_pos_iff.mpr (hFnonzero w hwR)) (hinner w hw)
    have hlogE := Real.log_le_self hE0.le
    have hlogK := Real.log_le_self hK0.le
    linarith
  have hJsmall : ∀ w : ℂ, ‖w‖ ≤ (1 : ℝ) / 16 → ‖J w‖ ≤ B := by
    intro w hw
    have hbound := lem_BCI ((1 : ℝ) / 8) (E + K)
      (by norm_num) (by linarith) J
      (hJanalytic _ (by norm_num) hsmall) hJ0
      (by
        intro v hv
        rw [lem_ballDR _ (by norm_num)] at hv
        exact hJsmallRe v (by simpa only [Metric.mem_closedBall, dist_zero_right] using! hv))
      ((1 : ℝ) / 16) (by norm_num) (by norm_num) w hw
    norm_num only at hbound
    dsimp [B]
    linarith
  have hJlargeRe : ∀ w : ℂ, ‖w‖ ≤ R₂ →
      (J w).re ≤ (D + K + 1) * Real.log T := by
    intro w hw
    rw [← hJre w (by simpa only [Metric.mem_closedBall, dist_zero_right] using! hw)]
    have hlogF := Real.log_le_log (norm_pos_iff.mpr (hFnonzero w hw)) (houter w hw)
    rw [Real.log_mul hD0.ne' hTpos.ne'] at hlogF
    have hlogD := Real.log_le_self hD0.le
    have hlogK := Real.log_le_self hK0.le
    have hDK : D + K ≤ (D + K) * Real.log T :=
      le_mul_of_one_le_right (by linarith) hT
    nlinarith
  have hJlarge : ∀ w : ℂ, ‖w‖ ≤ R₁ → ‖J w‖ ≤ H * Real.log T := by
    intro w hw
    have hbound := lem_BCI R₂ ((D + K + 1) * Real.log T)
      hR20 (mul_pos (by linarith) hL0) J
      (hJanalytic R₂ hR20 le_rfl) hJ0
      (by
        intro v hv
        rw [lem_ballDR R₂ hR20] at hv
        exact hJlargeRe v (by simpa only [Metric.mem_closedBall, dist_zero_right] using! hv))
      R₁ hR10 h12 w hw
    have hA : ‖J w‖ ≤ A₀ * Real.log T := by
      dsimp [A₀]
      nlinarith [hbound]
    exact hA.trans (mul_le_mul_of_nonneg_right (by dsimp [H]; linarith) hL0.le)
  have hA1 : 1 ≤ H * Real.log T := one_le_mul_of_one_le_of_one_le hH hT
  have hnormJ : ‖J z‖ ≤ C * (Real.log T) ^ θ := by
    have h := threeCircle_power_bound (by norm_num : (0 : ℝ) < 1 / 16)
      hr hr₁ hA1 hB
      (fun w hw => (hJ w (by
        simpa only [Metric.mem_closedBall, dist_zero_right] using! hw.trans h12.le)).differentiableAt)
      hJsmall hJlarge hz
    change ‖J z‖ ≤ B * (H * Real.log T) ^ θ at h
    rw [Real.mul_rpow hH0.le hL0.le] at h
    simpa only [C, mul_assoc] using! h
  have hzR : ‖z‖ ≤ R₂ := (hz.trans hr₁.le).trans h12.le
  have hlogInv : Real.log ‖(F z)⁻¹‖ ≤ ‖J z‖ + Real.log K := by
    rw [norm_inv, Real.log_inv]
    have hrelation := hJre z (by
      simpa only [Metric.mem_closedBall, dist_zero_right] using! hzR)
    have hnegRe : -(J z).re ≤ ‖J z‖ :=
      (neg_le_abs _).trans (Complex.abs_re_le_norm _)
    linarith
  have hlogFinal : Real.log ‖(F z)⁻¹‖ ≤ C * (Real.log T) ^ θ + Real.log K := by
    linarith
  have hexp := Real.exp_le_exp.mpr hlogFinal
  rw [Real.exp_log (norm_pos_iff.mpr (inv_ne_zero (hFnonzero z hzR))),
    Real.exp_add, Real.exp_log hK0] at hexp
  simpa only [mul_comm] using! hexp

end RHLean.Analysis.MertensExponent
