import Mathlib
import «research.VF_MID_VON_KOCH_BRIDGE»

/-!
# Uniform VF / Li midpoint quadrature

This file sharpens the existing root-scale VF/Li bridge.  The decisive
analytic input is that the derivative of the Li density has derivative

  (log x + 2) / (x^2 log(x)^3),

hence varies on the r-th square band at scale
O(r^-4 log(r)^-2).  Midpoint symmetry will turn that into a summable
O(1/(r log(r)^2)) local quadrature error.

No prime-distribution input occurs here.  All constants are deterministic.
-/

noncomputable section

open Set MeasureTheory intervalIntegral
open scoped BigOperators Interval Topology

namespace RHLean.Analysis

/-- First derivative of the inverse-log density, named as a function so that
its derivative can be bounded directly. -/
def vfInvLogDeriv (x : ℝ) : ℝ :=
  -x⁻¹ / Real.log x ^ 2

/-- The existing VF bridge derivative formula in named-function form. -/
theorem deriv_invLog_eq_vfInvLogDeriv
    {x : ℝ} (hx : 1 < x) :
    deriv (fun t : ℝ => (Real.log t)⁻¹) x =
      vfInvLogDeriv x := by
  simpa [vfInvLogDeriv] using deriv_inv_log_formula hx

/-- Exact derivative of the first derivative of the inverse-log density. -/
theorem hasDerivAt_vfInvLogDeriv
    {x : ℝ} (hx : 1 < x) :
    HasDerivAt vfInvLogDeriv
      ((Real.log x + 2) /
        (x ^ 2 * Real.log x ^ 3)) x := by
  have hx0 : x ≠ 0 := by linarith
  have hlog0 : Real.log x ≠ 0 :=
    ne_of_gt (Real.log_pos hx)
  have hnum :
      HasDerivAt (fun t : ℝ => -(t⁻¹)) ((x ^ 2)⁻¹) x := by
    convert (hasDerivAt_inv hx0).neg using 1
    ring_nf
  have hden :
      HasDerivAt (fun t : ℝ => Real.log t ^ 2)
        (2 * Real.log x * x⁻¹) x := by
    convert (Real.hasDerivAt_log hx0).pow 2 using 1
    ring_nf
  have hquot :=
    hnum.div hden (pow_ne_zero 2 hlog0)
  change HasDerivAt
    (fun t : ℝ => -(t⁻¹) / Real.log t ^ 2)
    ((Real.log x + 2) /
      (x ^ 2 * Real.log x ^ 3)) x
  convert hquot using 1
  field_simp [hx0, hlog0]
  ring

theorem deriv_vfInvLogDeriv
    {x : ℝ} (hx : 1 < x) :
    deriv vfInvLogDeriv x =
      (Real.log x + 2) /
        (x ^ 2 * Real.log x ^ 3) :=
  (hasDerivAt_vfInvLogDeriv hx).deriv

/-- A convenient elementary lower bound used to keep all later constants
explicit and rational. -/
theorem one_lt_log_four : (1 : ℝ) < Real.log 4 := by
  have h2 := Real.log_two_gt_d9
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [h4]
  nlinarith

/-- On square tile r, the second derivative of 1/log is
O(r^-4 log(r)^-2).  The constant 4 is intentionally generous. -/
theorem abs_deriv_vfInvLogDeriv_le_squareTile
    {r : ℕ} (hr : 2 ≤ r) {t : ℝ}
    (ht : t ∈ Icc ((r : ℝ) ^ 2)
      ((((r + 1 : ℕ) : ℝ) ^ 2))) :
    |deriv vfInvLogDeriv t| ≤
      4 / ((r : ℝ) ^ 4 * Real.log (r : ℝ) ^ 2) := by
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hr1 : (1 : ℝ) < (r : ℝ) := by linarith
  have hrpos : (0 : ℝ) < (r : ℝ) := by linarith
  have hlogr : 0 < Real.log (r : ℝ) := Real.log_pos hr1
  have hr4 : (4 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith
  have ht4 : (4 : ℝ) ≤ t := hr4.trans ht.1
  have htpos : (0 : ℝ) < t := by linarith
  have ht1 : (1 : ℝ) < t := by linarith
  have hlogt : 0 < Real.log t := Real.log_pos ht1
  have hlogt1 : (1 : ℝ) < Real.log t := by
    exact one_lt_log_four.trans_le
      (Real.log_le_log (by norm_num) ht4)
  have hrr : (r : ℝ) ≤ (r : ℝ) ^ 2 := by
    nlinarith
  have hrt : (r : ℝ) ≤ t := hrr.trans ht.1
  have hlogle :
      Real.log (r : ℝ) ≤ Real.log t :=
    Real.log_le_log hrpos hrt
  have hlogsq :
      Real.log (r : ℝ) ^ 2 ≤ Real.log t ^ 2 := by
    nlinarith
  have hsumpos :
      0 ≤ t + (r : ℝ) ^ 2 := by positivity
  have hprod :
      0 ≤ (t - (r : ℝ) ^ 2) *
        (t + (r : ℝ) ^ 2) :=
    mul_nonneg (sub_nonneg.mpr ht.1) hsumpos
  have hrpow :
      (r : ℝ) ^ 4 ≤ t ^ 2 := by
    nlinarith
  have hden :
      (r : ℝ) ^ 4 * Real.log (r : ℝ) ^ 2 ≤
        t ^ 2 * Real.log t ^ 2 := by
    exact mul_le_mul hrpow hlogsq (sq_nonneg _) (by positivity)
  have hdensmall :
      0 < (r : ℝ) ^ 4 * Real.log (r : ℝ) ^ 2 := by
    positivity
  rw [deriv_vfInvLogDeriv ht1]
  have hform :
      0 ≤ (Real.log t + 2) /
        (t ^ 2 * Real.log t ^ 3) := by
    positivity
  rw [abs_of_nonneg hform]
  have hnum : Real.log t + 2 ≤ 3 * Real.log t := by
    nlinarith
  have hden3 : 0 < t ^ 2 * Real.log t ^ 3 := by
    positivity
  calc
    (Real.log t + 2) / (t ^ 2 * Real.log t ^ 3)
        ≤ (3 * Real.log t) /
            (t ^ 2 * Real.log t ^ 3) :=
      div_le_div_of_nonneg_right hnum hden3.le
    _ = 3 / (t ^ 2 * Real.log t ^ 2) := by
      field_simp [hlogt.ne']
    _ ≤ 3 / ((r : ℝ) ^ 4 *
          Real.log (r : ℝ) ^ 2) := by
      exact div_le_div_of_nonneg_left
        (by norm_num : (0 : ℝ) ≤ 3) hdensmall hden
    _ ≤ 4 / ((r : ℝ) ^ 4 *
          Real.log (r : ℝ) ^ 2) := by
      exact div_le_div_of_nonneg_right
        (by norm_num) hdensmall.le


/-! ## Summable midpoint error on one square band -/

/-- The inverse-log first derivative is Lipschitz on one square band at the
second-derivative scale. -/
theorem vfInvLogDeriv_lipschitzOn_squareTile
    {r : ℕ} (hr : 2 ≤ r) {u v : ℝ}
    (hu : u ∈ Icc ((r : ℝ) ^ 2)
      ((((r + 1 : ℕ) : ℝ) ^ 2)))
    (hv : v ∈ Icc ((r : ℝ) ^ 2)
      ((((r + 1 : ℕ) : ℝ) ^ 2))) :
    |vfInvLogDeriv u - vfInvLogDeriv v| ≤
      (4 / ((r : ℝ) ^ 4 * Real.log (r : ℝ) ^ 2)) *
        |u - v| := by
  have hdiff :
      ∀ z ∈ Icc ((r : ℝ) ^ 2)
          ((((r + 1 : ℕ) : ℝ) ^ 2)),
        DifferentiableAt ℝ vfInvLogDeriv z := by
    intro z hz
    have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    have hz1 : (1 : ℝ) < z := by
      have hz4 : (4 : ℝ) ≤ z := by
        have hr4 : (4 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith
        exact hr4.trans hz.1
      linarith
    exact (hasDerivAt_vfInvLogDeriv hz1).differentiableAt
  have hder :
      ∀ z ∈ Icc ((r : ℝ) ^ 2)
          ((((r + 1 : ℕ) : ℝ) ^ 2)),
        ‖deriv vfInvLogDeriv z‖ ≤
          4 / ((r : ℝ) ^ 4 * Real.log (r : ℝ) ^ 2) := by
    intro z hz
    simpa [Real.norm_eq_abs] using
      (abs_deriv_vfInvLogDeriv_le_squareTile hr hz)
  have h :=
    Convex.norm_image_sub_le_of_norm_deriv_le
      (s := Icc ((r : ℝ) ^ 2)
        ((((r + 1 : ℕ) : ℝ) ^ 2)))
      (f := vfInvLogDeriv)
      (x := u) (y := v)
      hdiff hder (convex_Icc _ _) hu hv
  simpa [Real.norm_eq_abs, abs_sub_comm] using h

/-- Detrending the inverse-log density by its midpoint tangent leaves a
function whose derivative is O(width * sup |f''|) on the whole square band. -/
theorem abs_deriv_invLog_detrended_le_squareTile
    {r : ℕ} (hr : 2 ≤ r) {u : ℝ}
    (hu : u ∈ Icc ((r : ℝ) ^ 2)
      ((((r + 1 : ℕ) : ℝ) ^ 2))) :
    |deriv
        (fun z : ℝ =>
          (Real.log z)⁻¹ -
            vfInvLogDeriv (vfMidBandMidpoint r) *
              (z - vfMidBandMidpoint r)) u| ≤
      (4 / ((r : ℝ) ^ 4 * Real.log (r : ℝ) ^ 2)) *
        ((((r + 1 : ℕ) : ℝ) ^ 2) - (r : ℝ) ^ 2) := by
  let m := vfMidBandMidpoint r
  let d := vfInvLogDeriv m
  let width :=
    (((r + 1 : ℕ) : ℝ) ^ 2) - (r : ℝ) ^ 2
  have hm :
      m ∈ Icc ((r : ℝ) ^ 2)
        ((((r + 1 : ℕ) : ℝ) ^ 2)) := by
    dsimp [m, vfMidBandMidpoint]
    push_cast
    constructor <;> nlinarith
  have hu1 : (1 : ℝ) < u := by
    have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    have hu4 : (4 : ℝ) ≤ u := by
      have hr4 : (4 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith
      exact hr4.trans hu.1
    linarith
  have hfdiff :
      DifferentiableAt ℝ (fun z : ℝ => (Real.log z)⁻¹) u := by
    have hu0 : u ≠ 0 := by linarith
    have hlog0 : Real.log u ≠ 0 :=
      ne_of_gt (Real.log_pos hu1)
    exact ((Real.hasDerivAt_log hu0).inv hlog0).differentiableAt
  have hlin :
      HasDerivAt (fun z : ℝ => d * (z - m)) d u := by
    simpa using ((hasDerivAt_id u).sub_const m).const_mul d
  have hfder :
      HasDerivAt (fun z : ℝ => (Real.log z)⁻¹)
        (vfInvLogDeriv u) u := by
    have hu0 : u ≠ 0 := by linarith
    have hlog0 : Real.log u ≠ 0 :=
      ne_of_gt (Real.log_pos hu1)
    simpa [vfInvLogDeriv] using
      (Real.hasDerivAt_log hu0).inv hlog0
  have hderiv :
      deriv
        (fun z : ℝ => (Real.log z)⁻¹ - d * (z - m)) u =
          vfInvLogDeriv u - d := by
    exact (hfder.sub hlin).deriv
  have hlip :=
    vfInvLogDeriv_lipschitzOn_squareTile hr hu hm
  have hwidth :
      0 ≤ width := by
    dsimp [width]
    push_cast
    have hr0 : (0 : ℝ) ≤ (r : ℝ) := by positivity
    nlinarith
  have hdist : |u - m| ≤ width := by
    rw [abs_le]
    constructor <;> linarith [hu.1, hu.2, hm.1, hm.2]
  have hr1 : (1 : ℝ) < (r : ℝ) := by
    exact_mod_cast (show 1 < r by omega)
  have hlogr : 0 < Real.log (r : ℝ) := Real.log_pos hr1
  have hM :
      0 ≤ 4 / ((r : ℝ) ^ 4 *
        Real.log (r : ℝ) ^ 2) := by
    positivity
  change
    |deriv
        (fun z : ℝ => (Real.log z)⁻¹ - d * (z - m)) u| ≤
      (4 / ((r : ℝ) ^ 4 * Real.log (r : ℝ) ^ 2)) * width
  rw [hderiv]
  exact hlip.trans
    (mul_le_mul_of_nonneg_left hdist hM)

/-- Midpoint symmetry improves the crude first-derivative tile estimate by one
full factor of the square-root index.  The constant 108 is deliberately loose;
the decisive result is the summable 1/(r log(r)^2) scale. -/
theorem abs_vfMidBandQuadratureError_le_logHarmonic
    {r : ℕ} (hr : 2 ≤ r) :
    |vfMidBandQuadratureError r| ≤
      108 / ((r : ℝ) * Real.log (r : ℝ) ^ 2) := by
  let a : ℝ := (r : ℝ) ^ 2
  let b : ℝ := (((r + 1 : ℕ) : ℝ) ^ 2)
  let m : ℝ := vfMidBandMidpoint r
  let width : ℝ := b - a
  let M : ℝ :=
    4 / ((r : ℝ) ^ 4 * Real.log (r : ℝ) ^ 2)
  let d : ℝ := vfInvLogDeriv m
  let g : ℝ → ℝ :=
    fun z => (Real.log z)⁻¹ - d * (z - m)
  have hm : m ∈ Icc a b := by
    dsimp [a, b, m, vfMidBandMidpoint]
    push_cast
    constructor <;> nlinarith
  have hab : a ≤ b := hm.1.trans hm.2
  have hwidth : 0 ≤ width := sub_nonneg.mpr hab
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  have hdist :
      ∀ {z : ℝ}, z ∈ Icc a b → |z - m| ≤ width := by
    intro z hz
    rw [abs_le]
    constructor <;> linarith [hz.1, hz.2, hm.1, hm.2]
  have hgdiff :
      ∀ z ∈ Icc a b, DifferentiableAt ℝ g z := by
    intro z hz
    have hz1 : (1 : ℝ) < z := by
      have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
      have hz4 : (4 : ℝ) ≤ z := by
        have hr4 : (4 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith
        exact hr4.trans (by simpa [a] using hz.1)
      linarith
    have hz0 : z ≠ 0 := by linarith
    have hlog0 : Real.log z ≠ 0 :=
      ne_of_gt (Real.log_pos hz1)
    have hf :
        DifferentiableAt ℝ (fun u : ℝ => (Real.log u)⁻¹) z :=
      ((Real.hasDerivAt_log hz0).inv hlog0).differentiableAt
    have hl :
        DifferentiableAt ℝ (fun u : ℝ => d * (u - m)) z := by
      fun_prop
    exact hf.sub hl
  have hgder :
      ∀ z ∈ Icc a b, |deriv g z| ≤ M * width := by
    intro z hz
    simpa [a, b, m, width, M, d, g] using
      (abs_deriv_invLog_detrended_le_squareTile hr
        (by simpa [a, b] using hz))
  have hgpoint :
      ∀ z ∈ Icc a b,
        |g m - g z| ≤ M * width ^ 2 := by
    intro z hz
    have hlip :=
      Convex.norm_image_sub_le_of_norm_deriv_le
        (s := Icc a b) (f := g) (x := m) (y := z)
        hgdiff
        (fun u hu => by
          simpa [Real.norm_eq_abs] using hgder u hu)
        (convex_Icc _ _) hm hz
    have hdist' := hdist hz
    calc
      |g m - g z|
          ≤ (M * width) * |m - z| := by
            simpa [Real.norm_eq_abs, abs_sub_comm] using hlip
      _ ≤ (M * width) * width := by
            exact mul_le_mul_of_nonneg_left
              (by simpa [abs_sub_comm] using hdist')
              (mul_nonneg hM hwidth)
      _ = M * width ^ 2 := by ring
  have hlinInt :
      (∫ z in a..b, d * (z - m)) = 0 := by
    let H : ℝ → ℝ := fun z => d * (z - m) ^ 2 / 2
    have hH :
        ∀ z : ℝ, HasDerivAt H (d * (z - m)) z := by
      intro z
      dsimp [H]
      convert
        (((hasDerivAt_id z).sub_const m).pow 2).const_mul d |>.div_const 2
        using 1
      all_goals (simp [id_eq]; ring_nf)
    have hlinI' :
        IntervalIntegrable (fun z : ℝ => d * (z - m))
          MeasureTheory.volume a b :=
      (continuous_const.mul
        (continuous_id.sub continuous_const)).intervalIntegrable _ _
    have hFTC :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun z _hz => hH z) hlinI'
    rw [hFTC]
    dsimp [H, a, b, m, vfMidBandMidpoint]
    push_cast
    ring
  have ha1 : (1 : ℝ) < a := by
    dsimp [a]
    have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    nlinarith
  have hfInt :
      IntervalIntegrable (fun z : ℝ => (Real.log z)⁻¹)
        MeasureTheory.volume a b := by
    exact vfMid_invLog_intervalIntegrable ha1 hab
  have hlinI :
      IntervalIntegrable (fun z : ℝ => d * (z - m))
        MeasureTheory.volume a b :=
    (continuous_const.mul
      (continuous_id.sub continuous_const)).intervalIntegrable _ _
  have hgI :
      IntervalIntegrable g MeasureTheory.volume a b := by
    exact hfInt.sub hlinI
  have hgInt :
      (∫ z in a..b, g z) =
        ∫ z in a..b, (Real.log z)⁻¹ := by
    dsimp [g]
    rw [intervalIntegral.integral_sub hfInt hlinI,
      hlinInt, sub_zero]
  have hgm :
      g m = (Real.log m)⁻¹ := by
    simp [g]
  have hconst :
      (∫ _z in a..b, g m) = width * g m := by
    simp [width, smul_eq_mul]
  have herrInt :
      width * (Real.log m)⁻¹ -
          (∫ z in a..b, (Real.log z)⁻¹) =
        ∫ z in a..b, (g m - g z) := by
    rw [intervalIntegral.integral_sub _root_.intervalIntegrable_const hgI,
      hconst, hgInt, hgm]
  have hnorm :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b) (C := M * width ^ 2)
      (f := fun z : ℝ => g m - g z)
      (fun z hz => by
        rw [Set.uIoc_of_le hab] at hz
        have hz' : z ∈ Icc a b := Ioc_subset_Icc_self hz
        simpa [Real.norm_eq_abs] using hgpoint z hz')
  have herr :
      |width * (Real.log m)⁻¹ -
          (∫ z in a..b, (Real.log z)⁻¹)| ≤
        M * width ^ 3 := by
    rw [herrInt, ← Real.norm_eq_abs]
    calc
      ‖∫ z in a..b, (g m - g z)‖
          ≤ (M * width ^ 2) * |b - a| := hnorm
      _ = M * width ^ 3 := by
        rw [abs_of_nonneg hwidth]
        dsimp [width]
        ring
  have hmass :
      vfMidBandMass r = width * (Real.log m)⁻¹ := by
    unfold vfMidBandMass
    dsimp [width, a, b, m, vfMidBandMidpoint]
    push_cast
    rw [div_eq_mul_inv]
    ring
  have herrBand :
      |vfMidBandQuadratureError r| ≤ M * width ^ 3 := by
    unfold vfMidBandQuadratureError vfMidBandIntegral
    rw [hmass]
    change
      |width * (Real.log m)⁻¹ -
          (∫ z in a..b, (Real.log z)⁻¹)| ≤
        M * width ^ 3
    exact herr
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrpos : (0 : ℝ) < (r : ℝ) := by linarith
  have hr1 : (1 : ℝ) < (r : ℝ) := by linarith
  have hlogr : 0 < Real.log (r : ℝ) := Real.log_pos hr1
  have hwidth3 : width ≤ 3 * (r : ℝ) := by
    dsimp [width, a, b]
    push_cast
    nlinarith
  have hcube : width ^ 3 ≤ (3 * (r : ℝ)) ^ 3 :=
    pow_le_pow_left₀ hwidth hwidth3 3
  calc
    |vfMidBandQuadratureError r|
        ≤ M * width ^ 3 := herrBand
    _ ≤ M * (3 * (r : ℝ)) ^ 3 := by
      exact mul_le_mul_of_nonneg_left hcube hM
    _ = 108 / ((r : ℝ) * Real.log (r : ℝ) ^ 2) := by
      dsimp [M]
      field_simp [hrpos.ne', hlogr.ne']
      ring



/-! ## Uniform O(1) square-endpoint discrepancy -/

def vfLogHarmonicKernel (x : ℝ) : ℝ :=
  x⁻¹ / Real.log x ^ 2

theorem vfLogHarmonicKernel_nonneg
    {x : ℝ} (hx : 1 < x) :
    0 ≤ vfLogHarmonicKernel x := by
  unfold vfLogHarmonicKernel
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos hx
  positivity

theorem integral_vfLogHarmonicKernel
    {a b : ℝ} (ha : 1 < a) (hb : 1 < b) (hab : a ≤ b) :
    (∫ x in a..b, vfLogHarmonicKernel x) =
      (Real.log a)⁻¹ - (Real.log b)⁻¹ := by
  have hderiv :
      ∀ x ∈ Set.uIcc a b,
        HasDerivAt (fun y : ℝ => -(Real.log y)⁻¹)
          (vfLogHarmonicKernel x) x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have hx1 : (1 : ℝ) < x := ha.trans_le hx.1
    have hx0 : x ≠ 0 := by linarith
    have hlog0 : Real.log x ≠ 0 :=
      ne_of_gt (Real.log_pos hx1)
    have hinv :
        HasDerivAt (fun y : ℝ => (Real.log y)⁻¹)
          (vfInvLogDeriv x) x := by
      simpa [vfInvLogDeriv] using
        (Real.hasDerivAt_log hx0).inv hlog0
    have hneg := hinv.neg
    convert hneg using 1
    · rfl
    · unfold vfLogHarmonicKernel vfInvLogDeriv
      field_simp [hx0, hlog0]
      ring
  have hcont :
      ContinuousOn vfLogHarmonicKernel (Set.uIcc a b) := by
    intro x hx
    exact (hderiv x hx).continuousAt.continuousWithinAt
  have h :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      hderiv hcont.intervalIntegrable
  simpa using h

theorem vfLogHarmonicKernel_antitoneOn_two :
    AntitoneOn vfLogHarmonicKernel (Ici (2 : ℝ)) := by
  intro x hx y hy hxy
  have hx2 : (2 : ℝ) ≤ x := hx
  have hy2 : (2 : ℝ) ≤ y := hy
  have hxpos : (0 : ℝ) < x := by linarith
  have hypos : (0 : ℝ) < y := by linarith
  have hx1 : (1 : ℝ) < x := by linarith
  have hy1 : (1 : ℝ) < y := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hlogy : 0 < Real.log y := Real.log_pos hy1
  have hlogxy : Real.log x ≤ Real.log y :=
    Real.log_le_log hxpos hxy
  have hlogsq : Real.log x ^ 2 ≤ Real.log y ^ 2 := by
    nlinarith
  have hden :
      x * Real.log x ^ 2 ≤ y * Real.log y ^ 2 := by
    exact mul_le_mul hxy hlogsq (sq_nonneg _) hypos.le
  have hdenx :
      0 < x * Real.log x ^ 2 := by positivity
  have hxform :
      vfLogHarmonicKernel x =
        1 / (x * Real.log x ^ 2) := by
    unfold vfLogHarmonicKernel
    field_simp [hxpos.ne', hlogx.ne']
  have hyform :
      vfLogHarmonicKernel y =
        1 / (y * Real.log y ^ 2) := by
    unfold vfLogHarmonicKernel
    field_simp [hypos.ne', hlogy.ne']
  rw [hxform, hyform]
  exact one_div_le_one_div_of_le hdenx hden

theorem sum_vfLogHarmonicKernel_Ico_le
    (R : ℕ) (hR : 2 ≤ R) :
    (∑ r ∈ Finset.Ico 2 R,
        vfLogHarmonicKernel (r : ℝ)) ≤
      vfLogHarmonicKernel 2 + (Real.log 2)⁻¹ := by
  by_cases hR2 : R = 2
  · subst R
    simp
    have hlog2 : 0 ≤ (Real.log (2 : ℝ))⁻¹ := by
      exact inv_nonneg.mpr
        (Real.log_nonneg (by norm_num))
    linarith
  have h2R : 2 < R := by omega
  have hRm1 : 2 ≤ R - 1 := by omega
  have hRm1one : 1 < R - 1 := by omega
  have hb1 : (1 : ℝ) < ((R - 1 : ℕ) : ℝ) := by
    exact_mod_cast hRm1one
  have hanti :
      AntitoneOn vfLogHarmonicKernel
        (Icc (2 : ℝ) ((R - 1 : ℕ) : ℝ)) :=
    vfLogHarmonicKernel_antitoneOn_two.mono Icc_subset_Ici_self
  have htail0 :=
    AntitoneOn.sum_le_integral_Ico
      (f := vfLogHarmonicKernel)
      hRm1 hanti
  have hshift :
      (∑ r ∈ Finset.Ico 3 R,
          vfLogHarmonicKernel (r : ℝ)) =
        ∑ i ∈ Finset.Ico 2 (R - 1),
          vfLogHarmonicKernel ((i + 1 : ℕ) : ℝ) := by
    symm
    rw [Finset.sum_Ico_add'
      (fun n : ℕ => vfLogHarmonicKernel (n : ℝ))
      2 (R - 1) 1]
    simp [Nat.sub_add_cancel (by omega : 1 ≤ R)]
  have htail :
      (∑ r ∈ Finset.Ico 3 R,
          vfLogHarmonicKernel (r : ℝ)) ≤
        ∫ x in (2 : ℝ)..((R - 1 : ℕ) : ℝ),
          vfLogHarmonicKernel x := by
    rw [hshift]
    simpa using htail0
  have hint :=
    integral_vfLogHarmonicKernel
      (a := (2 : ℝ))
      (b := ((R - 1 : ℕ) : ℝ))
      (by norm_num) hb1
      (by exact_mod_cast hRm1)
  have hlogRm1 :
      0 < Real.log (((R - 1 : ℕ) : ℝ)) :=
    Real.log_pos hb1
  have hintle :
      (∫ x in (2 : ℝ)..((R - 1 : ℕ) : ℝ),
          vfLogHarmonicKernel x) ≤
        (Real.log 2)⁻¹ := by
    rw [hint]
    have hinv :
        0 ≤ (Real.log (((R - 1 : ℕ) : ℝ))⁻¹ :=
      inv_nonneg.mpr hlogRm1.le
    linarith
  rw [Finset.sum_eq_sum_Ico_succ_bot h2R]
  calc
    vfLogHarmonicKernel 2 +
          ∑ r ∈ Finset.Ico 3 R,
            vfLogHarmonicKernel (r : ℝ)
        ≤ vfLogHarmonicKernel 2 +
            (∫ x in (2 : ℝ)..((R - 1 : ℕ) : ℝ),
              vfLogHarmonicKernel x) :=
      add_le_add_left htail _
    _ ≤ vfLogHarmonicKernel 2 + (Real.log 2)⁻¹ :=
      add_le_add_left hintle _

theorem sum_abs_vfMidBandQuadratureError_le_uniform
    (R : ℕ) (hR : 2 ≤ R) :
    (∑ r ∈ Finset.Ico 2 R,
        |vfMidBandQuadratureError r|) ≤
      108 *
        (vfLogHarmonicKernel 2 + (Real.log 2)⁻¹) := by
  have hterm :
      ∀ r ∈ Finset.Ico 2 R,
        |vfMidBandQuadratureError r| ≤
          108 * vfLogHarmonicKernel (r : ℝ) := by
    intro r hrmem
    have hr2 : 2 ≤ r := (Finset.mem_Ico.mp hrmem).1
    have h :=
      abs_vfMidBandQuadratureError_le_logHarmonic
        (r := r) hr2
    have hrpos : (0 : ℝ) < (r : ℝ) := by
      exact_mod_cast (show 0 < r by omega)
    have hr1 : (1 : ℝ) < (r : ℝ) := by
      exact_mod_cast (show 1 < r by omega)
    have hlogr : 0 < Real.log (r : ℝ) :=
      Real.log_pos hr1
    calc
      |vfMidBandQuadratureError r|
          ≤ 108 / ((r : ℝ) *
              Real.log (r : ℝ) ^ 2) := h
      _ = 108 * vfLogHarmonicKernel (r : ℝ) := by
        unfold vfLogHarmonicKernel
        field_simp [hrpos.ne', hlogr.ne']
        ring
  calc
    (∑ r ∈ Finset.Ico 2 R,
        |vfMidBandQuadratureError r|)
        ≤ ∑ r ∈ Finset.Ico 2 R,
            108 * vfLogHarmonicKernel (r : ℝ) :=
      Finset.sum_le_sum hterm
    _ = 108 *
          (∑ r ∈ Finset.Ico 2 R,
            vfLogHarmonicKernel (r : ℝ)) := by
      rw [Finset.mul_sum]
    _ ≤ 108 *
          (vfLogHarmonicKernel 2 + (Real.log 2)⁻¹) := by
      exact mul_le_mul_of_nonneg_left
        (sum_vfLogHarmonicKernel_Ico_le R hR)
        (by norm_num)

theorem vfMidLiError_sq_eq_base_add_sum
    (R : ℕ) (hR : 2 ≤ R) :
    vfMidLiError ((R : ℝ) ^ 2) =
      vfMidLiError 4 +
        ∑ r ∈ Finset.Ico 2 R,
          vfMidBandQuadratureError r := by
  induction R, hR using Nat.le_induction with
  | base =>
      norm_num
  | succ R hR ih =>
      rw [vfMidLiError_sq_succ hR, ih,
        Finset.sum_Ico_succ_top hR]
      ring

def vfMidLiSquareEndpointUniformConstant : ℝ :=
  |vfMidLiError 4| +
    108 * (vfLogHarmonicKernel 2 + (Real.log 2)⁻¹)

theorem vfMidLiSquareEndpointUniformConstant_nonneg :
    0 ≤ vfMidLiSquareEndpointUniformConstant := by
  unfold vfMidLiSquareEndpointUniformConstant
  have hk :
      0 ≤ vfLogHarmonicKernel 2 :=
    vfLogHarmonicKernel_nonneg (by norm_num)
  have hlog :
      0 ≤ (Real.log (2 : ℝ))⁻¹ :=
    inv_nonneg.mpr (Real.log_nonneg (by norm_num))
  positivity

theorem abs_vfMidLiError_sq_le_uniform
    {R : ℕ} (hR : 2 ≤ R) :
    |vfMidLiError ((R : ℝ) ^ 2)| ≤
      vfMidLiSquareEndpointUniformConstant := by
  rw [vfMidLiError_sq_eq_base_add_sum R hR]
  calc
    |vfMidLiError 4 +
        ∑ r ∈ Finset.Ico 2 R,
          vfMidBandQuadratureError r|
        ≤ |vfMidLiError 4| +
            |∑ r ∈ Finset.Ico 2 R,
              vfMidBandQuadratureError r| :=
      abs_add _ _
    _ ≤ |vfMidLiError 4| +
          ∑ r ∈ Finset.Ico 2 R,
            |vfMidBandQuadratureError r| := by
      gcongr
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ |vfMidLiError 4| +
          108 *
            (vfLogHarmonicKernel 2 +
              (Real.log 2)⁻¹) := by
      exact add_le_add_left
        (sum_abs_vfMidBandQuadratureError_le_uniform R hR) _
    _ = vfMidLiSquareEndpointUniformConstant := rfl

def VFMidLiSquareEndpointUniformBoundedStatement : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ R : ℕ, 2 ≤ R →
      |vfMidLiError ((R : ℝ) ^ 2)| ≤ C

theorem vfMidLiSquareEndpointUniformBounded :
    VFMidLiSquareEndpointUniformBoundedStatement := by
  refine ⟨vfMidLiSquareEndpointUniformConstant,
    vfMidLiSquareEndpointUniformConstant_nonneg, ?_⟩
  intro R hR
  exact abs_vfMidLiError_sq_le_uniform hR


end RHLean.Analysis
