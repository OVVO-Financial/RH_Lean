import Mathlib
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import PrimeNumberTheoremAnd.ZetaBounds
import StrongPNT.PNT5_Strong
import RHLean.Analysis.StrongMertensLogNineContour
import RHLean.Analysis.StrongMertensSmallHeight

/-!
# Quantitative boundary estimates for the shared log-nine Mertens contour

All contour legs consume the single corridor from
`StrongMertensLogNineCorridor`.  No theorem in this file reselects an analytic
width constant and no wide-strip reciprocal-zeta hypothesis is introduced.

The shifted vertical line is

  `sigma_T = 1 - A / log(T)^9`.

Large heights on this line use PNT+'s `ZetaInvBnd`; bounded heights use the
compact removable-zero estimate from `StrongMertensSmallHeight`.  On the
horizontal legs, each point is treated by a pointwise dichotomy:

* `sigma <= 1 + A/log(T)^9`: use the shared narrow `ZetaInvBnd` window;
* `sigma > 1 + A/log(T)^9`: use `ZetaInvBound2` on `Re s > 1`.

Thus there is no `NativeMertensHorizontalCompatible` side condition.
-/

set_option maxHeartbeats 4000000

noncomputable section

open Filter Finset Topology Asymptotics Complex Real MeasureTheory
open scoped BigOperators ArithmeticFunction.Moebius LSeries.notation

namespace RHLean.Analysis

local notation "zetaC" => riemannZeta

-- `StrongPNT.PNT1_ComplexAnalysis` declares a root-level `def I := Complex.I`,
-- so with `Complex` open the bare token `I` resolves two ways.
local notation "I" => Complex.I

/-- One uniform inverse-zeta estimate on the fixed shifted line for an
already-selected corridor. -/
theorem nativeInvZeta_logNine_shift_uniform_for
    (corridor : StrongMertensLogNineCorridor) :
    ∃ C > 0,
      (∀ {T t : ℝ}, 3 < T → |t| ≤ T →
        1 / ‖zetaC (strongMertensLogNineShift corridor.A T + t * I)‖ ≤
          C * (1 + (Real.log T) ^ 7)) ∧
      (∀ {T : ℝ}, 3 < T →
        ∀ s ∈ (((Set.Icc (strongMertensLogNineShift corridor.A T) 2) ×ℂ
          (Set.Icc (-T) T)) \ {(1 : ℂ)}), zetaC s ≠ 0) := by
  obtain ⟨M, hM, hSmall⟩ := strongMertens_inv_zeta_small_height_bdd corridor
  let C : ℝ := corridor.invConst + M + 1
  have hC : 0 < C := by
    dsimp [C]
    linarith [corridor.invConst_pos, hM]
  refine ⟨C, hC, ?_, ?_⟩
  · intro T t hT htT
    by_cases ht : 3 < |t|
    · have hlarge := corridor.inv_shift_large T t hT ht htT
      have hlogle : Real.log |t| ≤ Real.log T :=
        Real.log_le_log (by linarith) htT
      have hlognn : 0 ≤ Real.log |t| := Real.log_nonneg (by linarith)
      have hp7 : (Real.log |t|) ^ 7 ≤ (Real.log T) ^ 7 :=
        pow_le_pow_left₀ hlognn hlogle 7
      calc
        1 / ‖zetaC (strongMertensLogNineShift corridor.A T + t * I)‖
            ≤ corridor.invConst * (Real.log |t|) ^ (7 : ℝ) := hlarge
        _ = corridor.invConst * (Real.log |t|) ^ 7 := by
          rw [Real.rpow_natCast]
        _ ≤ corridor.invConst * (Real.log T) ^ 7 := by gcongr
        _ ≤ C * (1 + (Real.log T) ^ 7) := by
          dsimp [C]
          have hp : 0 ≤ (Real.log T) ^ 7 := by positivity
          nlinarith [corridor.invConst_pos.le, hM]
    · have hsmallt : |t| ≤ 3 := le_of_not_gt ht
      have hb := hSmall T hT.le t hsmallt
      calc
        1 / ‖zetaC (strongMertensLogNineShift corridor.A T + t * I)‖ ≤ M := hb
        _ ≤ C * (1 + (Real.log T) ^ 7) := by
          dsimp [C]
          have hp : 0 ≤ (Real.log T) ^ 7 := by positivity
          nlinarith [corridor.invConst_pos.le, hM]
  · intro T hT
    exact corridor.zero_free_box T hT.le

/-- Canonical existential facade.  Core contour assembly should use
`nativeInvZeta_logNine_shift_uniform_for` so all legs share the same corridor
object. -/
theorem nativeInvZeta_logNine_shift_uniform :
    ∃ A ∈ Set.Ioc (0 : ℝ) (1 / 2), ∃ C > 0,
      (∀ {T t : ℝ}, 3 < T → |t| ≤ T →
        1 / ‖zetaC (strongMertensLogNineShift A T + t * I)‖ ≤
          C * (1 + (Real.log T) ^ 7)) ∧
      (∀ {T : ℝ}, 3 < T →
        ∀ s ∈ (((Set.Icc (strongMertensLogNineShift A T) 2) ×ℂ
          (Set.Icc (-T) T)) \ {(1 : ℂ)}), zetaC s ≠ 0) := by
  let corridor : StrongMertensLogNineCorridor := strongMertensLogNineCorridor
  obtain ⟨C, hC, hInv, hZero⟩ := nativeInvZeta_logNine_shift_uniform_for corridor
  exact ⟨corridor.A, corridor.A_mem, C, hC, hInv, hZero⟩

/-! ## A tail integral already used by the strong-PNT contour -/

/-- A convenient quantitative tail bound for the logarithmic kernel.  This is
ported verbatim from the later PNT+ strong-PNT contour helper. -/
lemma nativeIntegralLogSqOverTSqBound : ∃ C > 0, ∀ T, 3 < T →
    ∫ t in Set.Ici T, (Real.log t)^2 / t^2 ≤ C / Real.sqrt T := by
  have h_log_sq_le_t_fourth_pow :
      ∃ C > 0, ∀ t : ℝ, 3 ≤ t → (Real.log t)^2 / t^2 ≤ C / t^(3/2 : ℝ) := by
    have h_log_sq_le_sqrt :
        ∃ C > 0, ∀ t : ℝ, 3 ≤ t → Real.log t ^ 2 ≤ C * t ^ (1 / 2 : ℝ) := by
      have h_log_le : ∃ C > 0, ∀ t : ℝ, 3 ≤ t →
          Real.log t ≤ C * t ^ (1 / 4 : ℝ) := by
        refine ⟨4, by norm_num, ?_⟩
        intro t ht
        have h := Real.log_le_sub_one_of_pos
          (by positivity : 0 < t ^ (1 / 4 : ℝ))
        rw [Real.log_rpow (by positivity)] at h
        linarith
      obtain ⟨C, hC, hCb⟩ := h_log_le
      refine ⟨C^2, sq_pos_of_pos hC, ?_⟩
      intro t ht
      have hsq := pow_le_pow_left₀ (Real.log_nonneg (by linarith)) (hCb t ht) 2
      rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast,
        ← Real.rpow_mul (by linarith)] at hsq
      norm_num at hsq ⊢
      exact hsq
    obtain ⟨C, hC, hCb⟩ := h_log_sq_le_sqrt
    refine ⟨C, hC, ?_⟩
    intro t ht
    rw [div_le_div_iff₀] <;> try positivity
    convert mul_le_mul_of_nonneg_right (hCb t ht)
      (Real.rpow_nonneg (by linarith : 0 ≤ t) (3 / 2)) using 1
    rw [mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add (by linarith)]
    norm_num
  obtain ⟨C, hC, hCb⟩ := h_log_sq_le_t_fourth_pow
  refine ⟨C * 2, by positivity, ?_⟩
  intro T hT
  have hint : ∫ t in Set.Ici T, t ^ (-3 / 2 : ℝ) = 2 / Real.sqrt T := by
    rw [MeasureTheory.integral_Ici_eq_integral_Ioi, integral_Ioi_rpow_of_lt] <;>
      norm_num
    · rw [Real.sqrt_eq_rpow, Real.rpow_neg] <;> ring_nf
      linarith
    · linarith
  have hCint : ∫ t in Set.Ici T, C / t^(3/2 : ℝ) = C * 2 / Real.sqrt T := by
    convert congrArg (fun x => C * x) hint using 1 <;> ring_nf
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun x hx => ?_
    rw [← Real.rpow_neg (by linarith [Set.mem_Ici.mp hx])]
    ring_nf
  refine (MeasureTheory.setIntegral_mono_on ?_ ?_ measurableSet_Ici
    (fun t ht => hCb t (by linarith [ht.out]))).trans (le_of_eq hCint)
  · have hInteg : IntegrableOn (fun t => C / t ^ (3 / 2 : ℝ)) (Set.Ici T) := by
      have := hCint
      contrapose! this
      rw [MeasureTheory.integral_undef this]
      positivity
    have hMeas : AEStronglyMeasurable (fun t => Real.log t ^ 2 / t ^ 2)
        (volume.restrict (Set.Ici T)) := by
      exact ((Real.measurable_log.pow_const 2).div
        (measurable_id.pow_const 2)).aestronglyMeasurable
    apply hInteg.mono' hMeas
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    rw [Real.norm_of_nonneg (by positivity)]
    exact hCb t (by linarith [ht.out])
  · have := hCint
    contrapose! this
    rw [MeasureTheory.integral_undef this]
    positivity

/-! ## Quantitative five-leg estimates -/

/-- Right-tail pointwise bound from `ZetaInvBound2`.  We deliberately enlarge
the fractional powers to ordinary logarithms so the existing log-square tail
integral can be reused. -/
theorem nativeMertensFarTail_pointwise {f : ℝ → ℝ}
    (hsupp : Function.support f ⊆ Set.Icc (1 / 2) 2)
    (hdiff : ContDiff ℝ 1 f) :
    ∃ C > 0, ∀ {eps X T : ℝ}, eps ∈ Set.Ioo (0 : ℝ) 1 →
      3 < X → 3 < T → ∀ t : ℝ, t ≤ -T →
      ‖nativeSmoothedMobiusIntegrand f eps X
          ((1 + (Real.log X)⁻¹) + t * I)‖ ≤
        C * (X * Real.log X / eps) * (Real.log (-t)) ^ 2 / (-t) ^ 2 := by
  obtain ⟨Cz, hCz, hZ⟩ := ZetaInvBound2
  obtain ⟨Cm, hCm, hMel⟩ := MellinOfSmooth1b hdiff hsupp
  refine ⟨8 * Cz * Cm * Real.exp 1, by positivity, ?_⟩
  intro eps X T heps hX hT t ht
  have hXpos : 0 < X := by linarith
  have htneg : t < 0 := by linarith
  have habs : |t| = -t := abs_of_neg htneg
  have hlogX : 1 < Real.log X := logt_gt_one hX.le
  have hlogt : 1 < Real.log (-t) := by
    apply logt_gt_one
    rw [← habs]
    linarith
  let sigma : ℝ := 1 + (Real.log X)⁻¹
  have hsigma : sigma ∈ Set.Ioc (1 : ℝ) 2 := by
    dsimp [sigma]
    constructor
    · positivity
    · have : (Real.log X)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hlogX.le
      linarith
  have hzb := hZ hsigma t (by rw [habs]; linarith)
  have hxfrac : ((Real.log X)⁻¹) ^ (-(3 : ℝ) / 4) ≤ Real.log X := by
    rw [Real.rpow_neg (by positivity), Real.inv_rpow (by positivity)]
    simpa only [inv_inv] using
      (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ Real.log X)
        (by norm_num : (3 : ℝ) / 4 ≤ 1))
  have htfrac : (Real.log |t|) ^ ((1 : ℝ) / 4) ≤ Real.log (-t) := by
    rw [habs]
    exact Real.rpow_le_self_of_one_le (by linarith) (by norm_num)
  have hzb' : 1 / ‖zetaC ((sigma : ℂ) + t * I)‖ ≤
      Cz * Real.log X * Real.log (-t) := by
    calc
      1 / ‖zetaC ((sigma : ℂ) + t * I)‖
          ≤ Cz * (((Real.log X)⁻¹) ^ (-(3 : ℝ) / 4)) *
              (Real.log |t|) ^ ((1 : ℝ) / 4) := by simpa [sigma] using hzb
      _ ≤ Cz * Real.log X * Real.log (-t) := by gcongr
  let s : ℂ := (sigma : ℂ) + t * I
  have hsre : s.re = sigma := by simp [s]
  have hMelS := hMel (1/2) (by norm_num) s (by
      rw [hsre]
      dsimp [sigma]
      linarith) (by
      rw [hsre]
      exact hsigma.2) eps heps.1 heps.2
  have hXs : ‖(X : ℂ) ^ s‖ = X * Real.exp 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hXpos, hsre]
    dsimp [sigma]
    rw [Real.rpow_add hXpos, Real.rpow_one,
      Real.rpow_inv_log (by linarith) (by linarith)]
  have hnorm2 : (-t) ^ 2 ≤ ‖s‖ ^ 2 := by
    have hnsq : ‖s‖ ^ 2 = s.re ^ 2 + s.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      ring
    rw [hnsq, hsre]
    have hsim : s.im = t := by simp [s]
    rw [hsim]
    nlinarith [sq_nonneg sigma]
  rw [nativeSmoothedMobiusIntegrand_norm_eq, hXs]
  have hinv : (‖s‖ ^ 2)⁻¹ ≤ ((-t) ^ 2)⁻¹ := by
    apply inv_anti₀ (by positivity)
    exact hnorm2
  calc
    1 / ‖zetaC s‖ *
        ‖mellin (fun x => (Smooth1 f eps x : ℂ)) s‖ *
        (X * Real.exp 1)
      ≤ (Cz * Real.log X * Real.log (-t)) *
          (Cm * (eps * ‖s‖ ^ 2)⁻¹) * (X * Real.exp 1) := by
        gcongr
    _ ≤ 8 * Cz * Cm * Real.exp 1 * (X * Real.log X / eps) *
          (Real.log (-t)) ^ 2 / (-t) ^ 2 := by
        have hlog_nonneg : 0 ≤ Real.log (-t) := by linarith
        have hlog_le_sq : Real.log (-t) ≤ (Real.log (-t)) ^ 2 := by
          nlinarith [sq_nonneg (Real.log (-t) - 1)]
        rw [mul_inv]
        gcongr
        ring_nf

/-- Lower far-tail bound. -/
theorem nativeMertensM1_logNine_bound {f : ℝ → ℝ}
    (hsupp : Function.support f ⊆ Set.Icc (1 / 2) 2)
    (hdiff : ContDiff ℝ 1 f) :
    ∃ C > 0, ∀ {eps X T : ℝ}, eps ∈ Set.Ioo (0 : ℝ) 1 →
      3 < X → 3 < T →
      ‖nativeMertensContourM1 f eps X T‖ ≤
        C * (X * Real.log X / (eps * Real.sqrt T)) := by
  obtain ⟨C1, hC1, hpw⟩ := nativeMertensFarTail_pointwise hsupp hdiff
  obtain ⟨C2, hC2, hint⟩ := nativeIntegralLogSqOverTSqBound
  refine ⟨C1 * C2 / (2 * Real.pi), by positivity, ?_⟩
  intro eps X T heps hX hT
  have hnormint :
      ‖∫ t in Set.Iic (-T), nativeSmoothedMobiusIntegrand f eps X
          ((1 + (Real.log X)⁻¹) + t * I)‖ ≤
        C1 * (X * Real.log X / eps) * (C2 / Real.sqrt T) := by
    calc
      ‖∫ t in Set.Iic (-T), nativeSmoothedMobiusIntegrand f eps X
          ((1 + (Real.log X)⁻¹) + t * I)‖
        ≤ ∫ t in Set.Iic (-T), ‖nativeSmoothedMobiusIntegrand f eps X
          ((1 + (Real.log X)⁻¹) + t * I)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t in Set.Iic (-T),
          C1 * (X * Real.log X / eps) * (Real.log (-t)) ^ 2 / (-t) ^ 2 := by
        apply integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall fun _ => norm_nonneg _
        · have hInt : IntegrableOn (fun t => (Real.log (-t))^2 / (-t)^2)
              (Set.Iic (-T)) := by
            have hpos := (nativeIntegralLogSqOverTSqBound.choose_spec.2 T hT)
            have : IntegrableOn (fun t => (Real.log t)^2 / t^2) (Set.Ici T) := by
              exact integrableOn_Ioi_rpow_of_lt (by norm_num) (by linarith) |>.mono'
                (((Real.measurable_log.pow_const 2).div
                  (measurable_id.pow_const 2)).aestronglyMeasurable)
                (by
                  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
                  simp only [Real.norm_eq_abs]
                  positivity)
            convert this.comp_neg using 1
          simpa only [mul_div_assoc] using hInt.const_mul (C1 * (X * Real.log X / eps))
        · filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
          exact hpw heps hX hT t ht
      _ = C1 * (X * Real.log X / eps) *
          (∫ t in Set.Ici T, (Real.log t)^2 / t^2) := by
        rw [← neg_neg T, ← integral_comp_neg_Iic]
        simp only [neg_neg, neg_sq]
        rw [← MeasureTheory.integral_const_mul]
      _ ≤ C1 * (X * Real.log X / eps) * (C2 / Real.sqrt T) := by
        apply mul_le_mul_of_nonneg_left (hint T hT)
        positivity
  unfold nativeMertensContourM1
  have hpref : ‖(1 / (2 * (pi : ℂ) * I)) * I‖ = 1 / (2 * Real.pi) := by
    rw [show (1 / (2 * (pi : ℂ) * I)) * I = 1 / (2 * (pi : ℂ)) by field_simp,
      norm_div, norm_one, norm_mul, Complex.norm_ofNat,
      show ‖(pi : ℂ)‖ = Real.pi from (RCLike.norm_ofReal _).trans (abs_of_pos Real.pi_pos)]
  rw [show (1 / (2 * (pi : ℂ) * I)) * (I * ∫ t in Set.Iic (-T),
      nativeSmoothedMobiusIntegrand f eps X ((1 + (Real.log X)⁻¹) + t * I)) =
      ((1 / (2 * (pi : ℂ) * I)) * I) *
        (∫ t in Set.Iic (-T), nativeSmoothedMobiusIntegrand f eps X
          ((1 + (Real.log X)⁻¹) + t * I)) by ring,
    norm_mul, hpref]
  calc
    1 / (2 * Real.pi) * ‖∫ t in Set.Iic (-T),
        nativeSmoothedMobiusIntegrand f eps X
          ((1 + (Real.log X)⁻¹) + t * I)‖
      ≤ 1 / (2 * Real.pi) *
          (C1 * (X * Real.log X / eps) * (C2 / Real.sqrt T)) := by
        gcongr
    _ = C1 * C2 / (2 * Real.pi) *
          (X * Real.log X / (eps * Real.sqrt T)) := by field_simp; ring

/-- Conjugation symmetry for the Mobius integrand. -/
theorem nativeSmoothedMobiusIntegrand_conj {f : ℝ → ℝ} {eps X : ℝ}
    (hX : 0 < X) (s : ℂ) :
    nativeSmoothedMobiusIntegrand f eps X (starRingEnd ℂ s) =
      starRingEnd ℂ (nativeSmoothedMobiusIntegrand f eps X s) := by
  unfold nativeSmoothedMobiusIntegrand
  simp only [map_mul, map_inv₀]
  congr 1
  · congr 1
    · exact riemannZeta_conj s
    · unfold mellin
      rw [← integral_conj]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      simp only [smul_eq_mul, map_mul, Complex.conj_ofReal]
      congr 1
      nth_rw 1 [← map_one (starRingEnd ℂ)]
      rw [← map_sub, Complex.cpow_conj, Complex.conj_ofReal]
      rw [Complex.arg_ofReal_of_nonneg hx.le]
      exact Real.pi_ne_zero.symm
  · rw [Complex.cpow_conj, Complex.conj_ofReal]
    rw [Complex.arg_ofReal_of_nonneg hX.le]
    exact Real.pi_ne_zero.symm

/-- Upper far-tail bound, by conjugation. -/
theorem nativeMertensM5_logNine_bound {f : ℝ → ℝ}
    (hsupp : Function.support f ⊆ Set.Icc (1 / 2) 2)
    (hdiff : ContDiff ℝ 1 f) :
    ∃ C > 0, ∀ {eps X T : ℝ}, eps ∈ Set.Ioo (0 : ℝ) 1 →
      3 < X → 3 < T →
      ‖nativeMertensContourM5 f eps X T‖ ≤
        C * (X * Real.log X / (eps * Real.sqrt T)) := by
  obtain ⟨C, hC, hM1⟩ := nativeMertensM1_logNine_bound hsupp hdiff
  refine ⟨C, hC, ?_⟩
  intro eps X T heps hX hT
  have hXpos : 0 < X := by linarith
  have hconj : nativeMertensContourM5 f eps X T =
      starRingEnd ℂ (nativeMertensContourM1 f eps X T) := by
    unfold nativeMertensContourM1 nativeMertensContourM5
    simp only [map_mul, map_div₀, conj_I, conj_ofReal, conj_ofNat, map_one]
    rw [neg_mul, mul_neg, ← neg_mul]
    congr 1
    · ring
    · rw [← integral_conj, ← integral_comp_neg_Ioi, integral_Ici_eq_integral_Ioi]
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      rw [← nativeSmoothedMobiusIntegrand_conj hXpos]
      congr 1
      simp only [map_add, map_one, map_mul, conj_I, conj_ofReal, map_inv₀,
        map_neg, mul_neg, neg_neg]
      push_cast
      ring
  rw [hconj, RCLike.norm_conj]
  exact hM1 heps hX hT

/-- Both horizontal pieces satisfy a uniform quantitative bound with no
compatibility condition between `X` and `T`.  The proof splits pointwise at the
right edge of the shared PNT+ log-nine window. -/

end RHLean.Analysis
