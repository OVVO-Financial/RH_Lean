import RHLean.Analysis.StrongMertensLogNineBoundsCore

set_option maxHeartbeats 4000000

noncomputable section

open Filter Finset Topology Asymptotics Complex Real MeasureTheory
open scoped BigOperators ArithmeticFunction.Moebius LSeries.notation

namespace RHLean.Analysis

local notation "zetaC" => riemannZeta

theorem nativeMertensHorizontal_logNine_bound_for
    (corridor : StrongMertensLogNineCorridor) {f : ℝ → ℝ}
    (hsupp : Function.support f ⊆ Set.Icc (1 / 2) 2)
    (hnonneg : ∀ x > 0, 0 ≤ f x)
    (hmass : ∫ x in Set.Ioi (0 : ℝ), f x / x = 1)
    (hdiff : ContDiff ℝ 1 f) :
    ∃ C > 0,
      ∀ {eps X T : ℝ}, eps ∈ Set.Ioo (0 : ℝ) 1 → 3 < X → 3 < T →
        let sigmaLeft := strongMertensLogNineShift corridor.A T
        ‖nativeMertensContourM2 f eps X T sigmaLeft‖ +
          ‖nativeMertensContourM4 f eps X T sigmaLeft‖ ≤
            C * X * (1 + (Real.log T) ^ 10) / (eps * T ^ 2) := by
  obtain ⟨Cright, hCright, hRight⟩ := ZetaInvBound2
  obtain ⟨Cm, hCm, hMel⟩ := MellinOfSmooth1b hdiff hsupp
  let Cz : ℝ := corridor.invConst + Cright / corridor.A + 1
  have hCz : 0 < Cz := by
    dsimp [Cz]
    positivity
  let Cpoint : ℝ := 2 * Cz * Cm * Real.exp 1
  have hCpoint : 0 < Cpoint := by
    dsimp [Cpoint]
    positivity
  let C : ℝ := 4 * Cpoint / Real.pi
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro eps X T heps hX hT
  simp only []
  let sigmaLeft : ℝ := strongMertensLogNineShift corridor.A T
  let sigmaMid : ℝ := 1 + corridor.A / (Real.log T) ^ 9
  let sigmaRight : ℝ := 1 + (Real.log X)⁻¹
  have hlogT : 1 < Real.log T := logt_gt_one hT.le
  have hlogX : 1 < Real.log X := logt_gt_one hX.le
  have hlogTpos : 0 < Real.log T := by linarith
  have hApos : 0 < corridor.A := corridor.A_mem.1
  have hsigLeftPos : 0 < sigmaLeft := by
    dsimp [sigmaLeft]
    exact corridor.shift_pos T hT.le
  have hsigLeftHalf : (1 : ℝ) / 2 ≤ sigmaLeft := by
    have hpow : (1 : ℝ) ≤ (Real.log T) ^ 9 := one_le_pow₀ hlogT.le
    have hden : 0 < (Real.log T) ^ 9 := by positivity
    have hfrac : corridor.A / (Real.log T) ^ 9 ≤ (1 : ℝ) / 2 := by
      calc
        corridor.A / (Real.log T) ^ 9 ≤ corridor.A / 1 := by
          rw [div_le_div_iff₀ hden (by norm_num)]
          exact mul_le_mul_of_nonneg_left hpow hApos.le
        _ = corridor.A := by ring
        _ ≤ (1 : ℝ) / 2 := corridor.A_mem.2
    dsimp [sigmaLeft, strongMertensLogNineShift]
    linarith
  have hsigMidGt : 1 < sigmaMid := by
    dsimp [sigmaMid]
    have : 0 < corridor.A / (Real.log T) ^ 9 := by positivity
    linarith
  have hsigRightLe2 : sigmaRight ≤ 2 := by
    dsimp [sigmaRight]
    have hinv : (Real.log X)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hlogX.le
    linarith
  have hsigOrder : sigmaLeft ≤ sigmaRight := by
    dsimp [sigmaLeft, sigmaRight, strongMertensLogNineShift]
    positivity
  have hlog7le10 : (Real.log T) ^ 7 ≤ (Real.log T) ^ 10 := by
    calc
      (Real.log T) ^ 7 = (Real.log T) ^ 7 * 1 := by ring
      _ ≤ (Real.log T) ^ 7 * (Real.log T) ^ 3 := by
        apply mul_le_mul_of_nonneg_left (one_le_pow₀ hlogT.le 3)
        positivity
      _ = (Real.log T) ^ 10 := by ring
  have hu0pos : 0 < corridor.A / (Real.log T) ^ 9 := by positivity
  have hu0le1 : corridor.A / (Real.log T) ^ 9 ≤ 1 := by
    have hpow : (1 : ℝ) ≤ (Real.log T) ^ 9 := one_le_pow₀ hlogT.le
    have hden : 0 < (Real.log T) ^ 9 := by positivity
    calc
      corridor.A / (Real.log T) ^ 9 ≤ corridor.A / 1 := by
        rw [div_le_div_iff₀ hden (by norm_num)]
        exact mul_le_mul_of_nonneg_left hpow hApos.le
      _ = corridor.A := by ring
      _ ≤ (1 : ℝ) / 2 := corridor.A_mem.2
      _ ≤ 1 := by norm_num
  have hpoint : ∀ sigma ∈ Set.Icc sigmaLeft sigmaRight,
      ‖nativeSmoothedMobiusIntegrand f eps X (sigma - T * I)‖ ≤
        Cpoint * X * (1 + (Real.log T) ^ 10) / (eps * T ^ 2) := by
    intro sigma hsigma
    let s : ℂ := (sigma : ℂ) - T * I
    have hsre : s.re = sigma := by simp [s]
    have hsim : s.im = -T := by simp [s]
    have hsigmaHalf : (1 : ℝ) / 2 ≤ sigma :=
      hsigLeftHalf.trans hsigma.1
    have hsigma2 : sigma ≤ 2 := hsigma.2.trans hsigRightLe2
    have hM := hMel (1 / 2) (by norm_num) s
      (by rw [hsre]; exact hsigmaHalf)
      (by rw [hsre]; exact hsigma2) eps heps.1 heps.2
    have hnormT : T ^ 2 ≤ ‖s‖ ^ 2 := by
      have hnsq : ‖s‖ ^ 2 = s.re ^ 2 + s.im ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        ring
      rw [hnsq, hsre, hsim]
      nlinarith [sq_nonneg sigma]
    have hinvnorm : (‖s‖ ^ 2)⁻¹ ≤ (T ^ 2)⁻¹ := by
      apply inv_anti₀ (by positivity)
      exact hnormT
    have hXs : ‖(X : ℂ) ^ s‖ ≤ Real.exp 1 * X := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith), hsre]
      calc
        X ^ sigma ≤ X ^ sigmaRight :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) hsigma.2
        _ = Real.exp 1 * X := by
          dsimp [sigmaRight]
          rw [Real.rpow_add (by linarith), Real.rpow_one,
            Real.rpow_inv_log (by linarith) (by linarith)]
          ring
    have hz : 1 / ‖zetaC s‖ ≤ Cz * (1 + (Real.log T) ^ 10) := by
      by_cases hleft : sigma < sigmaMid
      · have hwindow : sigma ∈ Set.Ico
            (1 - corridor.A / (Real.log |-T|) ^ 9)
            (1 + corridor.A / (Real.log |-T|) ^ 9) := by
          rw [abs_neg, abs_of_pos (by linarith : 0 < T)]
          constructor
          · simpa [sigmaLeft, strongMertensLogNineShift] using hsigma.1
          · simpa [sigmaMid] using hleft
        have hzi := corridor.inv_window_large sigma (-T) (by simpa using hT) hwindow
        have hzi' : 1 / ‖zetaC s‖ ≤ corridor.invConst * (Real.log T) ^ 7 := by
          simpa [s, sub_eq_add_neg, abs_of_pos (by linarith : 0 < T),
            Real.rpow_natCast] using hzi
        calc
          1 / ‖zetaC s‖ ≤ corridor.invConst * (Real.log T) ^ 7 := hzi'
          _ ≤ corridor.invConst * (Real.log T) ^ 10 := by gcongr
          _ ≤ Cz * (1 + (Real.log T) ^ 10) := by
            dsimp [Cz]
            have hp : 0 ≤ (Real.log T) ^ 10 := by positivity
            have hcr : 0 ≤ Cright / corridor.A := by positivity
            nlinarith [corridor.invConst_pos.le]
      · have hmidle : sigmaMid ≤ sigma := le_of_not_gt hleft
        have hsIoc : sigma ∈ Set.Ioc (1 : ℝ) 2 :=
          ⟨hsigMidGt.trans_le hmidle, hsigma2⟩
        have hzr := hRight hsIoc (-T) (by simpa using hT)
        have hgap : corridor.A / (Real.log T) ^ 9 ≤ sigma - 1 := by
          dsimp [sigmaMid] at hmidle
          linarith
        have hpowbase : (sigma - 1) ^ (-(3 : ℝ) / 4) ≤
            (corridor.A / (Real.log T) ^ 9)⁻¹ := by
          calc
            (sigma - 1) ^ (-(3 : ℝ) / 4)
                ≤ (corridor.A / (Real.log T) ^ 9) ^ (-(3 : ℝ) / 4) := by
                  apply Real.rpow_le_rpow_of_nonpos hu0pos.le hgap
                  norm_num
            _ ≤ (corridor.A / (Real.log T) ^ 9) ^ (-1 : ℝ) := by
                  apply Real.rpow_le_rpow_of_exponent_ge hu0pos.le hu0le1
                  norm_num
            _ = (corridor.A / (Real.log T) ^ 9)⁻¹ := by
                  rw [Real.rpow_neg_one]
        have hquarter : (Real.log T) ^ ((1 : ℝ) / 4) ≤ Real.log T :=
          Real.rpow_le_self hlogT.le (by norm_num)
        have hu0inv : (corridor.A / (Real.log T) ^ 9)⁻¹ =
            (Real.log T) ^ 9 / corridor.A := by
          field_simp [ne_of_gt hApos, ne_of_gt hlogTpos]
        have hzr' : 1 / ‖zetaC s‖ ≤
            (Cright / corridor.A) * (Real.log T) ^ 10 := by
          have h0 := hzr
          simp only [s, abs_neg, abs_of_pos (by linarith : 0 < T)] at h0
          calc
            1 / ‖zetaC s‖ ≤ Cright * (sigma - 1) ^ (-(3 : ℝ) / 4) *
                (Real.log T) ^ ((1 : ℝ) / 4) := h0
            _ ≤ Cright * ((corridor.A / (Real.log T) ^ 9)⁻¹) * Real.log T := by
                gcongr
            _ = (Cright / corridor.A) * (Real.log T) ^ 10 := by
                rw [hu0inv]
                field_simp
                ring
        calc
          1 / ‖zetaC s‖ ≤ (Cright / corridor.A) * (Real.log T) ^ 10 := hzr'
          _ ≤ Cz * (1 + (Real.log T) ^ 10) := by
            dsimp [Cz]
            have hp : 0 ≤ (Real.log T) ^ 10 := by positivity
            have hci : 0 ≤ corridor.invConst := corridor.invConst_pos.le
            nlinarith [show 0 ≤ Cright / corridor.A by positivity]
    rw [nativeSmoothedMobiusIntegrand_norm_eq]
    calc
      1 / ‖zetaC s‖ * ‖mellin (fun x => (Smooth1 f eps x : ℂ)) s‖ *
          ‖(X : ℂ) ^ s‖
        ≤ (Cz * (1 + (Real.log T) ^ 10)) *
            (Cm * (eps * ‖s‖ ^ 2)⁻¹) * (Real.exp 1 * X) := by gcongr
      _ ≤ Cpoint * X * (1 + (Real.log T) ^ 10) / (eps * T ^ 2) := by
        dsimp [Cpoint]
        rw [mul_inv]
        gcongr
        ring_nf
  have hHolo := strongMertensSmoothedIntegrand_holomorphicOn_punctured_box
    corridor heps.1 heps.2 hsupp hnonneg hmass hdiff
    (X := X) (T := T) (by linarith : 0 < X) hT.le
  have hHorizontalMaps : Set.MapsTo
      (fun sigma : ℝ => (sigma : ℂ) - T * I)
      (Set.Icc sigmaLeft sigmaRight)
      (((Set.Icc (strongMertensLogNineShift corridor.A T) 2) ×ℂ
        Set.Icc (-T) T) \ {(1 : ℂ)}) := by
    intro sigma hsigma
    constructor
    · rw [Complex.mem_reProdIm]
      constructor
      · simp only [sub_re, ofReal_re, mul_re, ofReal_ofNat, I_re, mul_zero,
          ofReal_im, I_im, zero_mul, zero_sub]
        exact ⟨hsigma.1, hsigma.2.trans hsigRightLe2⟩
      · simp only [sub_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one,
          I_re, mul_zero, zero_sub]
        exact ⟨le_rfl, by linarith⟩
    · intro heq
      have him := congrArg Complex.im heq
      simp only [sub_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one,
        I_re, mul_zero, zero_sub, one_im] at him
      linarith
  have hHorizontalContinuous : ContinuousOn
      (fun sigma : ℝ => nativeSmoothedMobiusIntegrand f eps X (sigma - T * I))
      (Set.Icc sigmaLeft sigmaRight) := by
    exact ContinuousOn.comp' hHolo.continuousOn (by fun_prop) hHorizontalMaps
  have hM2 : ‖nativeMertensContourM2 f eps X T sigmaLeft‖ ≤
      Cpoint / Real.pi * X * (1 + (Real.log T) ^ 10) / (eps * T ^ 2) := by
    unfold nativeMertensContourM2
    rw [norm_mul]
    have hpref : ‖(1 / (2 * (pi : ℂ) * I))‖ = 1 / (2 * Real.pi) := by
      rw [norm_div, norm_one, norm_mul, norm_mul, Complex.norm_ofNat,
        show ‖(pi : ℂ)‖ = Real.pi from
          (RCLike.norm_ofReal _).trans (abs_of_pos Real.pi_pos), norm_I]
      ring
    rw [hpref]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc
      ‖∫ sigma in sigmaLeft..sigmaRight,
          nativeSmoothedMobiusIntegrand f eps X (sigma - T * I)‖
        ≤ ∫ sigma in sigmaLeft..sigmaRight,
          ‖nativeSmoothedMobiusIntegrand f eps X (sigma - T * I)‖ :=
            intervalIntegral.norm_integral_le_integral_norm _
      _ ≤ (sigmaRight - sigmaLeft) *
          (Cpoint * X * (1 + (Real.log T) ^ 10) / (eps * T ^ 2)) := by
        rw [intervalIntegral.integral_of_le hsigOrder]
        calc
          ∫ sigma in Set.Ioc sigmaLeft sigmaRight,
              ‖nativeSmoothedMobiusIntegrand f eps X (sigma - T * I)‖
            ≤ ∫ _sigma in Set.Ioc sigmaLeft sigmaRight,
                (Cpoint * X * (1 + (Real.log T) ^ 10) / (eps * T ^ 2)) := by
              apply setIntegral_mono_on
              · exact hHorizontalContinuous.norm.integrableOn_compact isCompact_Icc
              · exact integrableOn_const (by simp)
              · exact measurableSet_Ioc
              · intro sigma hs
                exact hpoint sigma ⟨hs.1.le, hs.2.le⟩
          _ = (sigmaRight - sigmaLeft) *
              (Cpoint * X * (1 + (Real.log T) ^ 10) / (eps * T ^ 2)) := by
                rw [setIntegral_const, Real.volume_Ioc]
                simp [hsigOrder]
      _ ≤ 2 * (Cpoint * X * (1 + (Real.log T) ^ 10) / (eps * T ^ 2)) := by
        have hlen : sigmaRight - sigmaLeft ≤ 2 := by
          dsimp [sigmaLeft, sigmaRight, strongMertensLogNineShift]
          have hfrac : corridor.A / (Real.log T)^9 ≤ 1 := by
            apply (div_le_one (by positivity)).2
            nlinarith [corridor.A_mem.2, one_le_pow₀ hlogT.le 9]
          have hinv : (Real.log X)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hlogX.le
          linarith
        have hnonneg : 0 ≤ Cpoint * X * (1 + (Real.log T) ^ 10) /
            (eps * T ^ 2) := by positivity
        nlinarith
    _ = Cpoint / Real.pi * X * (1 + (Real.log T) ^ 10) /
          (eps * T ^ 2) := by field_simp; ring
  have hM4 : ‖nativeMertensContourM4 f eps X T sigmaLeft‖ ≤
      Cpoint / Real.pi * X * (1 + (Real.log T) ^ 10) / (eps * T ^ 2) := by
    have hXpos : 0 < X := by linarith
    have hconj : nativeMertensContourM4 f eps X T sigmaLeft =
        starRingEnd ℂ (nativeMertensContourM2 f eps X T sigmaLeft) := by
      unfold nativeMertensContourM2 nativeMertensContourM4
      simp only [map_mul, map_div₀, conj_I, conj_ofReal, conj_ofNat, map_one]
      rw [← integral_conj]
      congr 1
      apply intervalIntegral.integral_congr
      intro sigma hs
      rw [← nativeSmoothedMobiusIntegrand_conj hXpos]
      congr 1
      simp
    rw [hconj, RCLike.norm_conj]
    exact hM2
  dsimp [C]
  have hnonneg : 0 ≤ Cpoint / Real.pi * X * (1 + (Real.log T) ^ 10) /
      (eps * T ^ 2) := by positivity
  nlinarith [hM2, hM4]

/-- Canonical existential facade for the horizontal estimate. -/
theorem nativeMertensHorizontal_logNine_bound {f : ℝ → ℝ}
    (hsupp : Function.support f ⊆ Set.Icc (1 / 2) 2)
    (hnonneg : ∀ x > 0, 0 ≤ f x)
    (hmass : ∫ x in Set.Ioi (0 : ℝ), f x / x = 1)
    (hdiff : ContDiff ℝ 1 f) :
    ∃ A ∈ Set.Ioc (0 : ℝ) (1 / 2), ∃ C > 0,
      ∀ {eps X T : ℝ}, eps ∈ Set.Ioo (0 : ℝ) 1 → 3 < X → 3 < T →
        let sigmaLeft := strongMertensLogNineShift A T
        ‖nativeMertensContourM2 f eps X T sigmaLeft‖ +
          ‖nativeMertensContourM4 f eps X T sigmaLeft‖ ≤
            C * X * (1 + (Real.log T) ^ 10) / (eps * T ^ 2) := by
  let corridor : StrongMertensLogNineCorridor := strongMertensLogNineCorridor
  obtain ⟨C, hC, hBound⟩ :=
    nativeMertensHorizontal_logNine_bound_for corridor hsupp hnonneg hmass hdiff
  exact ⟨corridor.A, corridor.A_mem, C, hC, hBound⟩

/-- Shifted vertical bound using the uniform log-nine reciprocal estimate. -/

end RHLean.Analysis
