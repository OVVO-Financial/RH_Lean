import Mathlib
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles
import StrongPNT.PNT5_Strong
import RHLean.Analysis.StrongMertensZetaKernel

/-!
# Residue-free contour pull for the log-nine Mertens route

This file is contour geometry only.  The reciprocal-zeta kernel has removable
value zero at one, so the rectangle theorem is used with residue coefficient
zero.  Quantitative estimates for the five resulting contour pieces live in
`StrongMertensLogNineBounds`.
-/

noncomputable section

open Filter Finset Topology Asymptotics Complex Real MeasureTheory
open scoped BigOperators ArithmeticFunction.Moebius LSeries.notation

namespace RHLean.Analysis

/-- Lower far tail on the right Perron line. -/
def nativeMertensContourM1
    (f : ℝ → ℝ) (eps X T : ℝ) : ℂ :=
  (1 / (2 * pi * I)) *
    (I * ∫ t : ℝ in Set.Iic (-T),
      nativeSmoothedMobiusIntegrand f eps X
        ((1 + (Real.log X)⁻¹) + t * I))

/-- Upper far tail on the right Perron line. -/
def nativeMertensContourM5
    (f : ℝ → ℝ) (eps X T : ℝ) : ℂ :=
  (1 / (2 * pi * I)) *
    (I * ∫ t : ℝ in Set.Ici T,
      nativeSmoothedMobiusIntegrand f eps X
        ((1 + (Real.log X)⁻¹) + t * I))

/-- Lower horizontal cut. -/
def nativeMertensContourM2
    (f : ℝ → ℝ) (eps X T sigmaLeft : ℝ) : ℂ :=
  (1 / (2 * pi * I)) *
    (∫ sigma in sigmaLeft..(1 + (Real.log X)⁻¹),
      nativeSmoothedMobiusIntegrand f eps X (sigma - T * I))

/-- Upper horizontal cut. -/
def nativeMertensContourM4
    (f : ℝ → ℝ) (eps X T sigmaLeft : ℝ) : ℂ :=
  (1 / (2 * pi * I)) *
    (∫ sigma in sigmaLeft..(1 + (Real.log X)⁻¹),
      nativeSmoothedMobiusIntegrand f eps X (sigma + T * I))

/-- Shifted vertical cut. -/
def nativeMertensContourM3
    (f : ℝ → ℝ) (eps X T sigmaLeft : ℝ) : ℂ :=
  (1 / (2 * pi * I)) *
    (I * ∫ t : ℝ in Set.Icc (-T) T,
      nativeSmoothedMobiusIntegrand f eps X (sigmaLeft + t * I))

/-- Exact no-main-term contour identity at an arbitrary positive left edge. -/
def NativeMertensContourPullProp : Prop :=
  ∀ {f : ℝ → ℝ} {eps : ℝ}, 0 < eps → eps < 1 →
    ∀ {X : ℝ}, 3 < X →
    ∀ {T : ℝ}, 0 < T →
    ∀ {sigmaLeft : ℝ}, 0 < sigmaLeft → sigmaLeft < 1 →
      Function.support f ⊆ Set.Icc (1 / 2) 2 →
      (∀ x > 0, 0 ≤ f x) →
      (∫ x in Set.Ioi (0 : ℝ), f x / x = 1) →
      ContDiff ℝ 1 f →
      HolomorphicOn (nativeSmoothedMobiusIntegrand f eps X)
        (((Set.Icc sigmaLeft 2) ×ℂ (Set.Icc (-T) T)) \ {(1 : ℂ)}) →
      Integrable (fun t : ℝ =>
        nativeSmoothedMobiusIntegrand f eps X
          ((1 + (Real.log X)⁻¹) + t * I)) →
      nativeSmoothedMobius f eps X =
        nativeMertensContourM1 f eps X T -
          nativeMertensContourM2 f eps X T sigmaLeft +
          nativeMertensContourM3 f eps X T sigmaLeft +
          nativeMertensContourM4 f eps X T sigmaLeft +
          nativeMertensContourM5 f eps X T

/-- Residue-free five-piece contour pull. -/
theorem nativeMertensContourPull_holds : NativeMertensContourPullProp := by
  intro f eps heps heps1 X hX T hT sigmaLeft hsigma hsigma1
    hsupp hnonneg hmass hdiff hHolo hInt
  have hright1 : (1 : ℝ) < 1 + (Real.log X)⁻¹ := by
    have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
    have : 0 < (Real.log X)⁻¹ := by positivity
    linarith
  have hlogX1 : (1 : ℝ) < Real.log X := by
    rw [show (1 : ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
    apply Real.log_lt_log (Real.exp_pos 1)
    exact Real.exp_one_lt_d9.trans hX
  have hright2 : 1 + (Real.log X)⁻¹ < 2 := by
    rw [← one_add_one_eq_two]
    gcongr
    exact inv_lt_one_of_one_lt₀ hlogX1
  have hright2le : 1 + (Real.log X)⁻¹ ≤ 2 := hright2.le
  have hcast :
      ((1 + (Real.log X)⁻¹ : ℝ) : ℂ) =
        (1 : ℂ) + ((Real.log X)⁻¹ : ℂ) := by simp

  set fRR : ℝ → ℝ → ℂ := fun x y =>
    nativeSmoothedMobiusIntegrand f eps X (x + y * I) with hfRR
  set fC : ℂ → ℂ := fun z => fRR z.re z.im with hfC
  have hfC_eq : ∀ s : ℂ,
      fC s = nativeSmoothedMobiusIntegrand f eps X s := by
    intro s
    rw [hfC, hfRR]
    simp [re_add_im]

  have hOneInterior :
      Rectangle (sigmaLeft - (T : ℂ) * I)
        (1 + ((Real.log X)⁻¹ : ℂ) + (T : ℂ) * I) ∈ 𝓝 (1 : ℂ) := by
    refine rectangle_mem_nhds_iff.mpr (mem_reProdIm.mpr ?_)
    have hzre : (sigmaLeft - (T : ℂ) * I).re = sigmaLeft := by simp
    have hzim : (sigmaLeft - (T : ℂ) * I).im = -T := by simp
    have hwre :
        ((1 : ℂ) + ((Real.log X)⁻¹ : ℂ) + (T : ℂ) * I).re =
          1 + (Real.log X)⁻¹ := by simp
    have hwim :
        ((1 : ℂ) + ((Real.log X)⁻¹ : ℂ) + (T : ℂ) * I).im = T := by simp
    constructor
    · show ((1 : ℂ)).re ∈
        Set.uIoo (sigmaLeft - (T : ℂ) * I).re
          ((1 : ℂ) + ((Real.log X)⁻¹ : ℂ) + (T : ℂ) * I).re
      rw [hzre, hwre, Set.uIoo,
        inf_eq_left.mpr (by linarith), sup_eq_right.mpr (by linarith)]
      exact Set.mem_Ioo.mpr ⟨by simpa using hsigma1, by simp; linarith⟩
    · show ((1 : ℂ)).im ∈
        Set.uIoo (sigmaLeft - (T : ℂ) * I).im
          ((1 : ℂ) + ((Real.log X)⁻¹ : ℂ) + (T : ℂ) * I).im
      rw [hzim, hwim, Set.uIoo,
        inf_eq_left.mpr (by linarith), sup_eq_right.mpr (by linarith)]
      exact Set.mem_Ioo.mpr ⟨by simp; linarith, by simp; linarith⟩

  have hrectZero :
      RectangleIntegral' fC
        (sigmaLeft - (T : ℂ) * I)
        (1 + ((Real.log X)⁻¹ : ℂ) + (T : ℂ) * I) = 0 := by
    have hres := ResidueTheoremOnRectangleWithSimplePole'
      (f := fC)
      (z := sigmaLeft - (T : ℂ) * I)
      (w := 1 + ((Real.log X)⁻¹ : ℂ) + (T : ℂ) * I)
      (p := (1 : ℂ)) (A := (0 : ℂ))
      (by simp; linarith)
      (by simp; linarith)
      hOneInterior
      ?_
      ?_
    · simpa using hres
    · have hsub :
          (Rectangle (sigmaLeft - (T : ℂ) * I)
              (1 + ((Real.log X)⁻¹ : ℂ) + (T : ℂ) * I) \ {(1 : ℂ)}) ⊆
            (((Set.Icc sigmaLeft 2) ×ℂ (Set.Icc (-T) T)) \ {(1 : ℂ)}) := by
        apply Set.diff_subset_diff_left
        intro s hs
        rw [Rectangle, Complex.mem_reProdIm] at hs
        rw [Complex.mem_reProdIm]
        have hzre : (sigmaLeft - (T : ℂ) * I).re = sigmaLeft := by simp
        have hzim : (sigmaLeft - (T : ℂ) * I).im = -T := by simp
        have hwre :
            ((1 : ℂ) + ((Real.log X)⁻¹ : ℂ) + (T : ℂ) * I).re =
              1 + (Real.log X)⁻¹ := by simp
        have hwim :
            ((1 : ℂ) + ((Real.log X)⁻¹ : ℂ) + (T : ℂ) * I).im = T := by simp
        have hre := hs.1
        have him := hs.2
        rw [hzre, hwre, Set.uIcc_of_le (by linarith)] at hre
        rw [hzim, hwim, Set.uIcc_of_le (by linarith)] at him
        exact ⟨⟨hre.1, hre.2.trans hright2le⟩, him⟩
      intro s hs
      have hwithin :
          DifferentiableWithinAt ℂ
            (nativeSmoothedMobiusIntegrand f eps X)
            (Rectangle (sigmaLeft - (T : ℂ) * I)
              (1 + ((Real.log X)⁻¹ : ℂ) + (T : ℂ) * I) \ {(1 : ℂ)}) s :=
        (hHolo s (hsub hs)).mono hsub
      exact hwithin.congr (fun z _ => hfC_eq z) (hfC_eq s)
    · have hbig := nativeSmoothedMobiusIntegrand_isBigO_one_near_one
        heps heps1 hsupp hnonneg hmass hdiff
        (X := X) (by linarith : (0 : ℝ) < X)
      have hsubeq :
          (fC - fun s : ℂ => (0 : ℂ) / (s - 1)) =
            nativeSmoothedMobiusIntegrand f eps X := by
        funext s
        simp [hfC_eq s]
      rw [hsubeq]
      exact hbig

  have hTwoPiI : (2 * (pi : ℂ) * I) ≠ 0 := by
    have h2 : (2 : ℂ) ≠ 0 := by norm_num
    have hpi : (pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero h2 hpi) Complex.I_ne_zero

  rw [RectangleIntegral', RectangleIntegral, HIntegral, HIntegral,
    VIntegral, VIntegral, smul_eq_mul, mul_eq_zero] at hrectZero
  rcases hrectZero with hbad | hbracket
  · exact absurd hbad (by simp [hTwoPiI])
  simp only [hfC_eq] at hbracket

  have hzre : (sigmaLeft - (T : ℂ) * I).re = sigmaLeft := by simp
  have hzim : (sigmaLeft - (T : ℂ) * I).im = -T := by simp
  have hwre :
      ((1 : ℂ) + ((Real.log X)⁻¹ : ℂ) + (T : ℂ) * I).re =
        1 + (Real.log X)⁻¹ := by simp
  have hwim :
      ((1 : ℂ) + ((Real.log X)⁻¹ : ℂ) + (T : ℂ) * I).im = T := by simp
  rw [hzre, hzim, hwre, hwim] at hbracket

  have hTle : (-T : ℝ) ≤ T := by linarith
  have hIcc :
      (∫ y in Set.Icc (-T) T,
          nativeSmoothedMobiusIntegrand f eps X (sigmaLeft + y * I)) =
        ∫ y in -T..T,
          nativeSmoothedMobiusIntegrand f eps X (sigmaLeft + y * I) := by
    rw [intervalIntegral.integral_of_le hTle,
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]

  unfold nativeSmoothedMobius strongMertensSmoothedMobius VerticalIntegral'
  rw [verticalIntegral_split_three (a := -T) (b := T)]
  swap
  · refine hInt.congr (Filter.Eventually.of_forall fun t => ?_)
    rw [hcast]
  unfold nativeMertensContourM1 nativeMertensContourM2
    nativeMertensContourM3 nativeMertensContourM4 nativeMertensContourM5 VIntegral
  rw [hIcc]
  simp only [hcast, smul_eq_mul, ofReal_neg, neg_mul,
    sub_eq_add_neg, mul_comm I] at hbracket ⊢
  linear_combination (1 / (2 * (pi : ℂ) * I)) * hbracket

end RHLean.Analysis
