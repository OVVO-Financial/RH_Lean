import RHLean.Analysis.StrongMertensLogNineHorizontal

set_option maxHeartbeats 4000000

noncomputable section

open Filter Finset Topology Asymptotics Complex Real MeasureTheory
open scoped BigOperators ArithmeticFunction.Moebius LSeries.notation

namespace RHLean.Analysis

local notation "zetaC" => riemannZeta

-- `StrongPNT.PNT1_ComplexAnalysis` declares a root-level `def I := Complex.I`,
-- so with `Complex` open the bare token `I` resolves two ways.
local notation "I" => Complex.I

theorem nativeMertensM3_logNine_bound_for
    (corridor : StrongMertensLogNineCorridor) {f : ℝ → ℝ}
    (hsupp : Function.support f ⊆ Set.Icc (1 / 2) 2)
    (hnonneg : ∀ x > 0, 0 ≤ f x)
    (hmass : ∫ x in Set.Ioi (0 : ℝ), f x / x = 1)
    (hdiff : ContDiff ℝ 1 f) :
    ∃ C > 0,
      ∀ {eps X T : ℝ}, eps ∈ Set.Ioo (0 : ℝ) 1 → 3 < X → 3 < T →
        let sigmaLeft := strongMertensLogNineShift corridor.A T
        ‖nativeMertensContourM3 f eps X T sigmaLeft‖ ≤
          C * X * Real.exp (-corridor.A * Real.log X / (Real.log T)^9) *
            (1 + (Real.log T)^7) / eps := by
  obtain ⟨Cz, hCz, hInv, _hzero⟩ := nativeInvZeta_logNine_shift_uniform_for corridor
  obtain ⟨Cm, hCm, hMel⟩ := MellinOfSmooth1b hdiff hsupp
  refine ⟨4 * Cz * Cm, by positivity, ?_⟩
  intro eps X T heps hX hT
  simp only []
  let sigmaLeft : ℝ := strongMertensLogNineShift corridor.A T
  have hsigpos : 0 < sigmaLeft := by
    dsimp [sigmaLeft]
    exact corridor.shift_pos T hT.le
  have hpoint : ∀ t ∈ Set.Icc (-T) T,
      ‖nativeSmoothedMobiusIntegrand f eps X (sigmaLeft + t * I)‖ ≤
        Cz * (1 + (Real.log T)^7) *
          (Cm * (eps * (sigmaLeft^2 + t^2))⁻¹) * X^sigmaLeft := by
    intro t ht
    have habs : |t| ≤ T := abs_le.2 ht
    have hz := hInv hT habs
    let s : ℂ := (sigmaLeft : ℂ) + t * I
    have hsre : s.re = sigmaLeft := by simp [s]
    have hM := hMel sigmaLeft hsigpos s (by simp [s]) (by simp [s]; linarith) eps heps.1 heps.2
    have hnormsq : ‖s‖^2 = sigmaLeft^2 + t^2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp [s]
      ring
    rw [nativeSmoothedMobiusIntegrand_norm_eq,
      Complex.norm_cpow_eq_rpow_re_of_pos (by linarith), hsre]
    rwa [hnormsq] at hM ⊢
  have hHolo := strongMertensSmoothedIntegrand_holomorphicOn_punctured_box
    corridor heps.1 heps.2 hsupp hnonneg hmass hdiff
    (X := X) (T := T) (by linarith : 0 < X) hT.le
  have hVerticalMaps : Set.MapsTo
      (fun t : ℝ => (sigmaLeft : ℂ) + t * I)
      (Set.Icc (-T) T)
      (((Set.Icc (strongMertensLogNineShift corridor.A T) 2) ×ℂ
        Set.Icc (-T) T) \ {(1 : ℂ)}) := by
    intro t ht
    constructor
    · rw [Complex.mem_reProdIm]
      constructor
      · simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im,
          I_im, mul_one, sub_self, add_zero]
        exact ⟨le_rfl, by linarith [corridor.shift_lt_one T hT.le]⟩
      · simpa using ht
    · intro heq
      have hre := congrArg Complex.re heq
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im,
        I_im, mul_one, sub_self, add_zero, one_re] at hre
      exact (corridor.shift_lt_one T hT.le).ne hre
  have hVerticalContinuous : ContinuousOn
      (fun t : ℝ => nativeSmoothedMobiusIntegrand f eps X (sigmaLeft + t * I))
      (Set.Icc (-T) T) := by
    exact ContinuousOn.comp' hHolo.continuousOn (by fun_prop) hVerticalMaps
  unfold nativeMertensContourM3
  have hpref : ‖(1 / (2 * (Real.pi : ℂ) * I)) * I‖ = 1 / (2 * Real.pi) := by
    rw [show (1 / (2 * (Real.pi : ℂ) * I)) * I = 1 / (2 * (Real.pi : ℂ)) by field_simp,
      norm_div, norm_one, norm_mul, Complex.norm_ofNat,
      show ‖(Real.pi : ℂ)‖ = Real.pi from (RCLike.norm_ofReal _).trans (abs_of_pos Real.pi_pos)]
  rw [show (1 / (2 * (Real.pi : ℂ) * I)) * (I * ∫ t in Set.Icc (-T) T,
      nativeSmoothedMobiusIntegrand f eps X (sigmaLeft + t * I)) =
      ((1 / (2 * (Real.pi : ℂ) * I)) * I) *
        (∫ t in Set.Icc (-T) T,
          nativeSmoothedMobiusIntegrand f eps X (sigmaLeft + t * I)) by ring,
    norm_mul, hpref]
  calc
    1 / (2 * Real.pi) * ‖∫ t in Set.Icc (-T) T,
        nativeSmoothedMobiusIntegrand f eps X (sigmaLeft + t * I)‖
      ≤ 1 / (2 * Real.pi) * ∫ t in Set.Icc (-T) T,
          ‖nativeSmoothedMobiusIntegrand f eps X (sigmaLeft + t * I)‖ := by
        gcongr
        exact norm_integral_le_integral_norm _
    _ ≤ 1 / (2 * Real.pi) *
        (Cz * (1 + (Real.log T)^7) * Cm / eps * X^sigmaLeft *
          (Real.pi / sigmaLeft)) := by
        gcongr
        calc
          ∫ t in Set.Icc (-T) T,
              ‖nativeSmoothedMobiusIntegrand f eps X (sigmaLeft + t * I)‖
            ≤ ∫ t in Set.Icc (-T) T,
              (Cz * (1 + (Real.log T)^7) * Cm / eps * X^sigmaLeft) *
                (sigmaLeft^2 + t^2)⁻¹ := by
                apply setIntegral_mono_on
                · exact hVerticalContinuous.norm.integrableOn_compact isCompact_Icc
                · apply (ContinuousOn.const_mul (by
                    apply ContinuousOn.inv₀
                    · fun_prop
                    · intro t ht
                      positivity)).integrableOn_compact isCompact_Icc
                · exact measurableSet_Icc
                · intro t ht
                  have hp := hpoint t ht
                  simpa [mul_inv, div_eq_mul_inv] using hp
          _ ≤ (Cz * (1 + (Real.log T)^7) * Cm / eps * X^sigmaLeft) *
                (Real.pi / sigmaLeft) := by
                rw [← integral_const_mul]
                have hfull := integral_inv_sq_add_sq (ne_of_gt hsigpos)
                calc
                  ∫ t in Set.Icc (-T) T, (sigmaLeft^2+t^2)⁻¹
                    ≤ ∫ t : ℝ, (sigmaLeft^2+t^2)⁻¹ := by
                      apply integral_mono_measure_restrict
                      positivity
                  _ = Real.pi / sigmaLeft := by simpa [abs_of_pos hsigpos] using hfull
    _ ≤ 4 * Cz * Cm * X *
        Real.exp (-corridor.A * Real.log X / (Real.log T)^9) *
          (1 + (Real.log T)^7) / eps := by
      have hsigInv : sigmaLeft⁻¹ ≤ 2 := by
        have hhalf : (1 : ℝ) / 2 ≤ sigmaLeft := by
          dsimp [sigmaLeft, strongMertensLogNineShift]
          have hlogT : 1 < Real.log T := logt_gt_one hT.le
          have hfrac : corridor.A / (Real.log T)^9 ≤ 1/2 := by
            apply (div_le_iff₀ (by positivity)).2
            nlinarith [corridor.A_mem.2, one_le_pow₀ hlogT.le 9]
          linarith
        rw [inv_le_comm₀ hsigpos (by norm_num)]
        nlinarith
      have hXshift := LogNineContour.rpow_logNine_shift
        (A := corridor.A) (X := X) (T := T) (by linarith : 0 < X)
      dsimp [sigmaLeft, strongMertensLogNineShift] at hXshift
      rw [hXshift]
      field_simp
      nlinarith [Real.pi_pos]

/-- Canonical existential facade for the shifted vertical estimate. -/
theorem nativeMertensM3_logNine_bound {f : ℝ → ℝ}
    (hsupp : Function.support f ⊆ Set.Icc (1 / 2) 2)
    (hnonneg : ∀ x > 0, 0 ≤ f x)
    (hmass : ∫ x in Set.Ioi (0 : ℝ), f x / x = 1)
    (hdiff : ContDiff ℝ 1 f) :
    ∃ A ∈ Set.Ioc (0 : ℝ) (1 / 2), ∃ C > 0,
      ∀ {eps X T : ℝ}, eps ∈ Set.Ioo (0 : ℝ) 1 → 3 < X → 3 < T →
        let sigmaLeft := strongMertensLogNineShift A T
        ‖nativeMertensContourM3 f eps X T sigmaLeft‖ ≤
          C * X * Real.exp (-A * Real.log X / (Real.log T)^9) *
            (1 + (Real.log T)^7) / eps := by
  let corridor : StrongMertensLogNineCorridor := strongMertensLogNineCorridor
  obtain ⟨C, hC, hBound⟩ :=
    nativeMertensM3_logNine_bound_for corridor hsupp hnonneg hmass hdiff
  exact ⟨corridor.A, corridor.A_mem, C, hC, hBound⟩

end RHLean.Analysis
