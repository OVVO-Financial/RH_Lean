import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Square-tile midpoint prime-count bridge

This file formalizes the square-tile midpoint path VF_mid used to compare the
exact prime-counting staircase with the logarithmic integral without replacing
the square partition by an integer-site Li proxy.

The intended proof architecture is deliberately minimal:

1. define the real-valued continuous midpoint path vfMid;
2. prove the unconditional quadrature bridge
     vfMid(x) = logarithmicIntegralFromTwo(x) + O(1);
3. isolate the single RH-scale arithmetic target
     |pi(x) - vfMid(x)| <= C * sqrt(x) * log(x);
4. transfer that target to the classical von-Koch prime-count discrepancy.

No per-tile absolute error hypothesis and no separate signed-cancellation
criterion is introduced here.
-/

noncomputable section

open Set MeasureTheory intervalIntegral
open scoped BigOperators Interval Topology

namespace RHLean.Analysis

/-- The repository normalization of the logarithmic integral, reproduced here
with narrow dependencies so this research file does not depend on the umbrella
`Mathlib` import used by older RHLean modules. -/
def vfMidLogarithmicIntegralFromTwo (x : ℝ) : ℝ :=
  ∫ u in (2 : ℝ)..x, (Real.log u)⁻¹

/-- Mathlib's formal Riemann-hypothesis proposition, exposed locally without
importing the heavier RHLean bridge module. -/
def VFMidRiemannHypothesisStatement : Prop :=
  RiemannHypothesis

/-! ## The midpoint-tiled logarithmic integral -/

/-- Square-band index used by the midpoint path.  For x >= 0 this is
floor (sqrt x). -/
def vfMidSquareRootIndex (x : ℝ) : ℕ :=
  ⌊Real.sqrt x⌋₊

/-- Midpoint of the complete square band [r^2,(r+1)^2). -/
def vfMidBandMidpoint (r : ℕ) : ℝ :=
  (r : ℝ) ^ 2 + (r : ℝ) + (1 / 2 : ℝ)

/-- Midpoint Li mass assigned to one completed square band. -/
def vfMidBandMass (r : ℕ) : ℝ :=
  (2 * (r : ℝ) + 1) / Real.log (vfMidBandMidpoint r)

/-- Sum of all completed midpoint masses before square index R. -/
def vfMidFinishedMass (R : ℕ) : ℝ :=
  ∑ r ∈ Finset.Ico 2 R, vfMidBandMass r

/-- Interpolated midpoint mass on the live square band containing x. -/
def vfMidLiveMass (x : ℝ) : ℝ :=
  let R := vfMidSquareRootIndex x
  (x - (R : ℝ) ^ 2) /
    Real.log (((R : ℝ) ^ 2 + x) / 2)

/-- The continuous square-tile midpoint path.

For x < 4 it is zero.  For x >= 4, if R = floor (sqrt x), this is

sum_{r=2}^{R-1} (2r+1)/log(r^2+r+1/2)
 + (x-R^2)/log((R^2+x)/2).
-/
def vfMid (x : ℝ) : ℝ :=
  if x < 4 then 0
  else vfMidFinishedMass (vfMidSquareRootIndex x) + vfMidLiveMass x

/-- The square-root index is exact at square endpoints. -/
@[simp] theorem vfMidSquareRootIndex_sq (R : ℕ) :
    vfMidSquareRootIndex ((R : ℝ) ^ 2) = R := by
  simp [vfMidSquareRootIndex]

/-- The live contribution vanishes when the live band is empty. -/
@[simp] theorem vfMidLiveMass_sq (R : ℕ) :
    vfMidLiveMass ((R : ℝ) ^ 2) = 0 := by
  simp [vfMidLiveMass]

/-- Completing one additional square band appends exactly its midpoint mass. -/
theorem vfMidFinishedMass_succ {R : ℕ} (hR : 2 ≤ R) :
    vfMidFinishedMass (R + 1) =
      vfMidFinishedMass R + vfMidBandMass R := by
  unfold vfMidFinishedMass
  rw [Finset.sum_Ico_succ_top hR]

/-- At every square endpoint R^2 with R >= 2, the path is exactly the sum of
the completed bands before R; there is no live-band correction. -/
theorem vfMid_sq {R : ℕ} (hR : 2 ≤ R) :
    vfMid ((R : ℝ) ^ 2) = vfMidFinishedMass R := by
  have h4nat : 4 ≤ R ^ 2 := by nlinarith
  have h4 : (4 : ℝ) ≤ (R : ℝ) ^ 2 := by
    exact_mod_cast h4nat
  simp [vfMid, not_lt.mpr h4]

/-- Exact prime-counting staircase on the reals, constant between integers.
Only x >= 4 is used by the von-Koch target. -/
def vfMidPrimeCount (x : ℝ) : ℝ :=
  (Nat.primeCounting ⌊x⌋₊ : ℝ)

/-- Running midpoint prime-count error. -/
def vfMidPrimeError (x : ℝ) : ℝ :=
  vfMidPrimeCount x - vfMid x

/-- Midpoint quadrature error relative to the repository's Li normalization. -/
def vfMidLiError (x : ℝ) : ℝ :=
  vfMid x - vfMidLogarithmicIntegralFromTwo x

/-- Classical prime-count discrepancy in the same real-cutoff coordinates. -/
def vfMidPrimeLiError (x : ℝ) : ℝ :=
  vfMidPrimeCount x - vfMidLogarithmicIntegralFromTwo x

/-- The exact algebraic decomposition: prime-minus-Li is
prime-minus-VF plus VF-minus-Li. -/
theorem vfMidPrimeLiError_eq_primeError_add_liError (x : ℝ) :
    vfMidPrimeLiError x = vfMidPrimeError x + vfMidLiError x := by
  unfold vfMidPrimeLiError vfMidPrimeError vfMidLiError
  ring

/-! ## Midpoint quadrature infrastructure -/

/-- Exact Li mass of a complete square band. -/
def vfMidBandIntegral (r : ℕ) : ℝ :=
  ∫ t in ((r : ℝ) ^ 2)..(((r + 1 : ℕ) : ℝ) ^ 2),
    (Real.log t)⁻¹

/-- Signed midpoint quadrature residual on a complete square band. -/
def vfMidBandQuadratureError (r : ℕ) : ℝ :=
  vfMidBandMass r - vfMidBandIntegral r

/-- Exact Li mass on the live portion of square band R. -/
def vfMidLiveIntegral (R : ℕ) (x : ℝ) : ℝ :=
  ∫ t in ((R : ℝ) ^ 2)..x, (Real.log t)⁻¹

/-- Signed midpoint quadrature residual on the live portion of square band R. -/
def vfMidLiveQuadratureError (R : ℕ) (x : ℝ) : ℝ :=
  (x - (R : ℝ) ^ 2) /
      Real.log (((R : ℝ) ^ 2 + x) / 2) -
    vfMidLiveIntegral R x



/-- First derivative of the Li density on the square-tile range.  This is
all the calculus needed for the RH-scale midpoint bridge: a first-derivative
Lipschitz estimate gives a uniform error per completed square tile. -/
theorem deriv_inv_log_formula {x : ℝ} (hx : 1 < x) :
    deriv (fun t : ℝ => (Real.log t)⁻¹) x =
      -x⁻¹ / Real.log x ^ 2 := by
  have hx0 : x ≠ 0 := by linarith
  have hlog0 : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  exact ((Real.hasDerivAt_log hx0).inv hlog0).deriv


/-! ## Root-scale quadrature bridge -/

/-- A fixed envelope for one completed or partial square-tile midpoint error.
The exact constant is intentionally crude: root scale is all the von-Koch
transfer needs. -/
def vfMidTileQuadratureBound : ℝ :=
  9 / Real.log 4 ^ 2

theorem vfMidTileQuadratureBound_nonneg :
    0 ≤ vfMidTileQuadratureBound := by
  unfold vfMidTileQuadratureBound
  positivity

/-- The inverse-log density is interval-integrable on every interval to the
right of 1. -/
theorem vfMid_invLog_intervalIntegrable {a b : ℝ}
    (ha : 1 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => (Real.log t)⁻¹) volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc hab
  intro t ht
  have ht1 : 1 < t := ha.trans_le ht.1
  have ht0 : t ≠ 0 := by linarith
  have hlog0 : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht1)
  exact (((Real.hasDerivAt_log ht0).inv hlog0).continuousAt).continuousWithinAt

/-- On square tile r, the derivative of 1/log is bounded by the left endpoint
and the fixed log(4) denominator. -/
theorem abs_deriv_inv_log_le_squareTile
    {r : ℕ} (hr : 2 ≤ r) {t : ℝ}
    (ht : t ∈ Icc ((r : ℝ) ^ 2) ((((r + 1 : ℕ) : ℝ) ^ 2))) :
    |deriv (fun u : ℝ => (Real.log u)⁻¹) t| ≤
      1 / (((r : ℝ) ^ 2) * Real.log 4 ^ 2) := by
  have hr0 : 0 < (r : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hr)
  have hr4 : (4 : ℝ) ≤ (r : ℝ) ^ 2 := by
    have : (4 : ℕ) ≤ r ^ 2 := by nlinarith
    exact_mod_cast this
  have ht4 : (4 : ℝ) ≤ t := hr4.trans ht.1
  have ht0 : 0 < t := by linarith
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
  have hlogle : Real.log 4 ≤ Real.log t :=
    Real.log_le_log (by norm_num) ht4
  have hlogsq : Real.log 4 ^ 2 ≤ Real.log t ^ 2 := by
    nlinarith
  have hden :
      ((r : ℝ) ^ 2) * Real.log 4 ^ 2 ≤
        t * Real.log t ^ 2 := by
    exact mul_le_mul ht.1 hlogsq (sq_nonneg _) (by positivity)
  have hden0 : 0 < ((r : ℝ) ^ 2) * Real.log 4 ^ 2 := by positivity
  rw [deriv_inv_log_formula (by linarith : 1 < t)]
  have hneg : -t⁻¹ / Real.log t ^ 2 ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (inv_nonneg.mpr ht0.le)) (sq_nonneg _)
  rw [abs_of_nonpos hneg]
  have hrewrite :
      -(-t⁻¹ / Real.log t ^ 2) =
        1 / (t * Real.log t ^ 2) := by
    field_simp [ht0.ne', hlogt.ne']
  rw [hrewrite]
  exact one_div_le_one_div_of_le hden0 hden

/-- Uniform error on any live prefix of one square tile.  Only first
derivatives are used. -/
theorem abs_vfMid_partialBandQuadratureError_le
    {r : ℕ} (hr : 2 ≤ r) {y : ℝ}
    (hyl : (r : ℝ) ^ 2 ≤ y)
    (hyu : y ≤ (((r + 1 : ℕ) : ℝ) ^ 2)) :
    |(y - (r : ℝ) ^ 2) /
          Real.log (((r : ℝ) ^ 2 + y) / 2) -
        ∫ t in ((r : ℝ) ^ 2)..y, (Real.log t)⁻¹|
      ≤ vfMidTileQuadratureBound := by
  let a : ℝ := (r : ℝ) ^ 2
  let m : ℝ := (a + y) / 2
  let h : ℝ := y - a
  let K : ℝ := 1 / (a * Real.log 4 ^ 2)
  have hr0 : 0 < (r : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hr)
  have ha4 : (4 : ℝ) ≤ a := by
    dsimp [a]
    have : (4 : ℕ) ≤ r ^ 2 := by nlinarith
    exact_mod_cast this
  have ha1 : 1 < a := by linarith
  have hy1 : 1 < y := ha1.trans_le hyl
  have hm_mem : m ∈ Icc a y := by
    dsimp [m]
    constructor <;> linarith
  have hI : IntervalIntegrable (fun t : ℝ => (Real.log t)⁻¹) volume a y :=
    vfMid_invLog_intervalIntegrable ha1 hyl
  have hdiff :
      ∀ t ∈ Icc a y,
        |(Real.log m)⁻¹ - (Real.log t)⁻¹| ≤ K * |t - m| := by
    intro t ht
    have htTile :
        t ∈ Icc ((r : ℝ) ^ 2) ((((r + 1 : ℕ) : ℝ) ^ 2)) := by
      constructor
      · simpa [a] using ht.1
      · exact ht.2.trans hyu
    have hmTile :
        m ∈ Icc ((r : ℝ) ^ 2) ((((r + 1 : ℕ) : ℝ) ^ 2)) := by
      constructor
      · simpa [a] using hm_mem.1
      · exact hm_mem.2.trans hyu
    have hLip :=
      Convex.norm_image_sub_le_of_norm_deriv_le
        (s := Icc ((r : ℝ) ^ 2) ((((r + 1 : ℕ) : ℝ) ^ 2)))
        (f := fun u : ℝ => (Real.log u)⁻¹)
        (x := m) (y := t)
        (fun u hu => by
          have hu4 : (4 : ℝ) ≤ u := by
            have hr4 : (4 : ℝ) ≤ (r : ℝ) ^ 2 := by
              have : (4 : ℕ) ≤ r ^ 2 := by nlinarith
              exact_mod_cast this
            exact hr4.trans hu.1
          have hu1 : 1 < u := by linarith
          have hu0 : u ≠ 0 := by linarith
          have hlog0 : Real.log u ≠ 0 := ne_of_gt (Real.log_pos hu1)
          exact ((Real.hasDerivAt_log hu0).inv hlog0).differentiableAt)
        (fun u hu => by
          simpa [K, a, Real.norm_eq_abs] using
            abs_deriv_inv_log_le_squareTile hr hu)
        (convex_Icc _ _) hmTile htTile
    have hKnorm :
        (Real.log 4 ^ 2)⁻¹ * ((r : ℝ) ^ 2)⁻¹ = K := by
      dsimp [K, a]
      field_simp
    rw [hKnorm] at hLip
    simpa [Real.norm_eq_abs, abs_sub_comm] using hLip
  have hwidth : 0 ≤ h := by dsimp [h, a]; linarith
  have hay : a ≤ y := by simpa [a] using hyl
  have hdist : ∀ t ∈ Icc a y, |t - m| ≤ h := by
    intro t ht
    rw [abs_le]
    dsimp [m, h]
    constructor <;> linarith [ht.1, ht.2, hay]
  have hpoint : ∀ t ∈ Icc a y,
      |(Real.log m)⁻¹ - (Real.log t)⁻¹| ≤ K * h := by
    intro t ht
    exact (hdiff t ht).trans
      (mul_le_mul_of_nonneg_left (hdist t ht) (by
        dsimp [K, a]
        positivity))
  have hIntConst :
      (∫ _t in a..y, (Real.log m)⁻¹) = h * (Real.log m)⁻¹ := by
    simp [h]
  have hErrEq :
      h * (Real.log m)⁻¹ - ∫ t in a..y, (Real.log t)⁻¹ =
        ∫ t in a..y, ((Real.log m)⁻¹ - (Real.log t)⁻¹) := by
    rw [intervalIntegral.integral_sub _root_.intervalIntegrable_const hI, hIntConst]
  have hIntBound :
      |h * (Real.log m)⁻¹ - ∫ t in a..y, (Real.log t)⁻¹| ≤
        (K * h) * h := by
    rw [hErrEq, ← Real.norm_eq_abs]
    have hnorm :=
      intervalIntegral.norm_integral_le_of_norm_le_const
        (a := a) (b := y) (C := K * h)
        (f := fun t : ℝ => (Real.log m)⁻¹ - (Real.log t)⁻¹)
        (fun t ht => by
          rw [uIoc_of_le hyl] at ht
          simpa [Real.norm_eq_abs] using hpoint t (Ioc_subset_Icc_self ht))
    simpa [h, abs_of_nonneg hwidth] using hnorm
  have hh : h ≤ 3 * (r : ℝ) := by
    dsimp [h, a]
    have hycast : y ≤ ((r : ℝ) + 1) ^ 2 := by
      simpa [Nat.cast_add, Nat.cast_one] using hyu
    nlinarith
  have hrsq : 0 < (r : ℝ) ^ 2 := by positivity
  have hlog4sq : 0 < Real.log 4 ^ 2 := by
    exact sq_pos_of_pos (Real.log_pos (by norm_num))
  have hratio : h ^ 2 / (r : ℝ) ^ 2 ≤ 9 := by
    rw [div_le_iff₀ hrsq]
    nlinarith [sq_nonneg (h - 3 * (r : ℝ))]
  have hKh :
      (K * h) * h ≤ vfMidTileQuadratureBound := by
    unfold vfMidTileQuadratureBound
    dsimp [K, a]
    have heq :
        (1 / ((r : ℝ) ^ 2 * Real.log 4 ^ 2) * h) * h =
          (h ^ 2 / (r : ℝ) ^ 2) / Real.log 4 ^ 2 := by
      field_simp [ne_of_gt hrsq, ne_of_gt hlog4sq]
    rw [heq]
    exact div_le_div_of_nonneg_right hratio hlog4sq.le
  have hmform :
      h * (Real.log m)⁻¹ =
        (y - (r : ℝ) ^ 2) /
          Real.log (((r : ℝ) ^ 2 + y) / 2) := by
    dsimp [h, m, a]
    ring
  rw [← hmform]
  exact hIntBound.trans hKh

/-- Every completed square band obeys the same absolute quadrature budget. -/
theorem abs_vfMidBandQuadratureError_le
    {r : ℕ} (hr : 2 ≤ r) :
    |vfMidBandQuadratureError r| ≤ vfMidTileQuadratureBound := by
  have h := abs_vfMid_partialBandQuadratureError_le
    (r := r) hr
    (y := (((r + 1 : ℕ) : ℝ) ^ 2))
    (by
      have hr0 : 0 ≤ (r : ℝ) := by positivity
      norm_num [Nat.cast_add, Nat.cast_one]
      nlinarith)
    le_rfl
  unfold vfMidBandQuadratureError vfMidBandMass vfMidBandIntegral vfMidBandMidpoint
  convert h using 1
  · norm_num [Nat.cast_add, Nat.cast_one]
    ring

/-- The live band obeys the same absolute quadrature budget. -/
theorem abs_vfMidLiveQuadratureError_le
    {R : ℕ} (hR : 2 ≤ R) {x : ℝ}
    (hxl : (R : ℝ) ^ 2 ≤ x)
    (hxu : x ≤ (((R + 1 : ℕ) : ℝ) ^ 2)) :
    |vfMidLiveQuadratureError R x| ≤ vfMidTileQuadratureBound := by
  simpa [vfMidLiveQuadratureError, vfMidLiveIntegral] using
    abs_vfMid_partialBandQuadratureError_le (r := R) hR hxl hxu



/-- At square endpoints, one new tile changes the Li discrepancy by exactly
that tile's quadrature residual. -/
theorem vfMidLiError_sq_succ {R : ℕ} (hR : 2 ≤ R) :
    vfMidLiError ((((R + 1 : ℕ) : ℝ) ^ 2)) =
      vfMidLiError ((R : ℝ) ^ 2) + vfMidBandQuadratureError R := by
  have hR1 : 2 ≤ R + 1 := by omega
  have hRreal : (2 : ℝ) ≤ R := by exact_mod_cast hR
  have hR0 : (0 : ℝ) ≤ R := by positivity
  have hR4 : (4 : ℝ) ≤ (R : ℝ) ^ 2 := by
    nlinarith
  have hRsq : (2 : ℝ) ≤ (R : ℝ) ^ 2 := by
    linarith
  have hnext : (R : ℝ) ^ 2 ≤ (((R + 1 : ℕ) : ℝ) ^ 2) := by
    norm_num [Nat.cast_add, Nat.cast_one]
    nlinarith
  have hI₁ :
      IntervalIntegrable (fun t : ℝ => (Real.log t)⁻¹) volume
        2 ((R : ℝ) ^ 2) :=
    vfMid_invLog_intervalIntegrable (by norm_num) hRsq
  have hI₂ :
      IntervalIntegrable (fun t : ℝ => (Real.log t)⁻¹) volume
        ((R : ℝ) ^ 2) ((((R + 1 : ℕ) : ℝ) ^ 2)) :=
    vfMid_invLog_intervalIntegrable (by linarith [hR4]) hnext
  unfold vfMidLiError vfMidBandQuadratureError vfMidBandIntegral
  rw [vfMid_sq hR1, vfMid_sq hR, vfMidFinishedMass_succ hR]
  unfold vfMidLogarithmicIntegralFromTwo
  rw [← intervalIntegral.integral_add_adjacent_intervals hI₁ hI₂]
  ring

/-- Square-endpoint error grows by at most one fixed tile budget per square
band.  The intentionally crude R-factor is exactly the root scale needed. -/
theorem abs_vfMidLiError_sq_le (R : ℕ) (hR : 2 ≤ R) :
    |vfMidLiError ((R : ℝ) ^ 2)| ≤
      |vfMidLiError 4| + (R : ℝ) * vfMidTileQuadratureBound := by
  induction R, hR using Nat.le_induction with
  | base =>
      have hQ : 0 ≤ vfMidTileQuadratureBound :=
        vfMidTileQuadratureBound_nonneg
      norm_num
      nlinarith
  | succ R hR ih =>
      rw [vfMidLiError_sq_succ hR]
      calc
        |vfMidLiError ((R : ℝ) ^ 2) + vfMidBandQuadratureError R|
            ≤ |vfMidLiError ((R : ℝ) ^ 2)| +
                |vfMidBandQuadratureError R| := abs_add_le _ _
        _ ≤ (|vfMidLiError 4| +
              (R : ℝ) * vfMidTileQuadratureBound) +
              vfMidTileQuadratureBound :=
          add_le_add ih (abs_vfMidBandQuadratureError_le hR)
        _ = |vfMidLiError 4| +
              ((R + 1 : ℕ) : ℝ) * vfMidTileQuadratureBound := by
          norm_num [Nat.cast_add, Nat.cast_one]
          ring

/-- Exact decomposition of the Li discrepancy into the completed-square
endpoint plus the one live-band midpoint residual. -/
theorem vfMidLiError_eq_sq_add_live {x : ℝ} (hx : 4 ≤ x) :
    vfMidLiError x =
      vfMidLiError ((vfMidSquareRootIndex x : ℝ) ^ 2) +
        vfMidLiveQuadratureError (vfMidSquareRootIndex x) x := by
  let R : ℕ := vfMidSquareRootIndex x
  have hx0 : 0 ≤ x := by linarith
  have hsqrt2 : (2 : ℝ) ≤ Real.sqrt x := by
    have hs := Real.sq_sqrt hx0
    have hs0 := Real.sqrt_nonneg x
    nlinarith
  have hR : 2 ≤ R := by
    dsimp [R, vfMidSquareRootIndex]
    exact Nat.le_floor hsqrt2
  have hRle : (R : ℝ) ≤ Real.sqrt x := by
    dsimp [R, vfMidSquareRootIndex]
    exact Nat.floor_le (Real.sqrt_nonneg x)
  have hxl : (R : ℝ) ^ 2 ≤ x := by
    have hs := Real.sq_sqrt hx0
    nlinarith [Real.sqrt_nonneg x]
  have hI₁ :
      IntervalIntegrable (fun t : ℝ => (Real.log t)⁻¹) volume
        2 ((R : ℝ) ^ 2) :=
    vfMid_invLog_intervalIntegrable (by norm_num) (by
      have : (4 : ℝ) ≤ (R : ℝ) ^ 2 := by
        have hRreal : (2 : ℝ) ≤ R := by exact_mod_cast hR
        nlinarith
      linarith)
  have hI₂ :
      IntervalIntegrable (fun t : ℝ => (Real.log t)⁻¹) volume
        ((R : ℝ) ^ 2) x :=
    vfMid_invLog_intervalIntegrable (by
      have hRreal : (2 : ℝ) ≤ R := by exact_mod_cast hR
      nlinarith) hxl
  unfold vfMidLiError
  rw [vfMid_sq hR]
  unfold vfMid vfMidLiveMass vfMidLiveQuadratureError vfMidLiveIntegral
  rw [if_neg (not_lt.mpr hx)]
  change
    vfMidFinishedMass R +
        (x - (R : ℝ) ^ 2) / Real.log (((R : ℝ) ^ 2 + x) / 2) -
          vfMidLogarithmicIntegralFromTwo x =
      (vfMidFinishedMass R - vfMidLogarithmicIntegralFromTwo ((R : ℝ) ^ 2)) +
        ((x - (R : ℝ) ^ 2) / Real.log (((R : ℝ) ^ 2 + x) / 2) -
          ∫ t in ((R : ℝ) ^ 2)..x, (Real.log t)⁻¹)
  unfold vfMidLogarithmicIntegralFromTwo
  rw [← intervalIntegral.integral_add_adjacent_intervals hI₁ hI₂]
  ring

/-- Floor-sqrt geometry for the live square band. -/
theorem vfMidSquareRootIndex_bounds {x : ℝ} (hx : 4 ≤ x) :
    let R := vfMidSquareRootIndex x
    2 ≤ R ∧ (R : ℝ) ^ 2 ≤ x ∧
      x ≤ (((R + 1 : ℕ) : ℝ) ^ 2) ∧
      (R : ℝ) ≤ Real.sqrt x := by
  let R : ℕ := vfMidSquareRootIndex x
  have hx0 : 0 ≤ x := by linarith
  have hsqrt2 : (2 : ℝ) ≤ Real.sqrt x := by
    have hs := Real.sq_sqrt hx0
    have hs0 := Real.sqrt_nonneg x
    nlinarith
  have hR : 2 ≤ R := by
    dsimp [R, vfMidSquareRootIndex]
    exact Nat.le_floor hsqrt2
  have hRle : (R : ℝ) ≤ Real.sqrt x := by
    dsimp [R, vfMidSquareRootIndex]
    exact Nat.floor_le (Real.sqrt_nonneg x)
  have hsqrtlt : Real.sqrt x < (R : ℝ) + 1 := by
    dsimp [R, vfMidSquareRootIndex]
    simpa [Nat.cast_add, Nat.cast_one] using
      (Nat.lt_floor_add_one (Real.sqrt x))
  have hxl : (R : ℝ) ^ 2 ≤ x := by
    have hs := Real.sq_sqrt hx0
    nlinarith [Real.sqrt_nonneg x]
  have hxu : x ≤ (((R + 1 : ℕ) : ℝ) ^ 2) := by
    have hs := Real.sq_sqrt hx0
    norm_num [Nat.cast_add, Nat.cast_one]
    nlinarith [Real.sqrt_nonneg x]
  exact ⟨hR, hxl, hxu, hRle⟩


/-! ## Frozen analytic statements -/

/-- Unconditional midpoint quadrature bridge at the scale actually needed
for von Koch.  The stronger O(1) midpoint remainder is optional; O(sqrt x)
already disappears inside the RH-scale O(sqrt x * log x) budget. -/
def VFMidLiRootBoundedStatement : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧
    ∀ x : ℝ, 4 ≤ x →
      |vfMidLiError x| ≤ B * Real.sqrt x


/-- The quadrature bridge is unconditional: the square-tile midpoint path
differs from Li by at most root scale. -/
theorem vfMidLiRootBounded :
    VFMidLiRootBoundedStatement := by
  let Q : ℝ := vfMidTileQuadratureBound
  let A : ℝ := |vfMidLiError 4|
  refine ⟨A + 2 * Q, ?_, ?_⟩
  · dsimp [A, Q]
    exact add_nonneg (abs_nonneg _) (mul_nonneg (by norm_num)
      vfMidTileQuadratureBound_nonneg)
  · intro x hx
    let R : ℕ := vfMidSquareRootIndex x
    have hbounds := vfMidSquareRootIndex_bounds hx
    change 2 ≤ R ∧ (R : ℝ) ^ 2 ≤ x ∧
      x ≤ (((R + 1 : ℕ) : ℝ) ^ 2) ∧
      (R : ℝ) ≤ Real.sqrt x at hbounds
    rcases hbounds with ⟨hR, hxl, hxu, hRle⟩
    have hend := abs_vfMidLiError_sq_le R hR
    have hlive := abs_vfMidLiveQuadratureError_le hR hxl hxu
    have hdecomp := vfMidLiError_eq_sq_add_live hx
    change
      vfMidLiError x =
        vfMidLiError ((R : ℝ) ^ 2) +
          vfMidLiveQuadratureError R x at hdecomp
    have hx0 : 0 ≤ x := by linarith
    have hsqrt1 : (1 : ℝ) ≤ Real.sqrt x := by
      have hs := Real.sq_sqrt hx0
      have hs0 := Real.sqrt_nonneg x
      nlinarith
    have hQ0 : 0 ≤ Q := by
      dsimp [Q]
      exact vfMidTileQuadratureBound_nonneg
    have hA0 : 0 ≤ A := by
      dsimp [A]
      exact abs_nonneg _
    have hA : A ≤ A * Real.sqrt x := by
      simpa using mul_le_mul_of_nonneg_left hsqrt1 hA0
    have hRQ : (R : ℝ) * Q ≤ Real.sqrt x * Q :=
      mul_le_mul_of_nonneg_right hRle hQ0
    have hQ : Q ≤ Q * Real.sqrt x := by
      simpa [mul_comm] using mul_le_mul_of_nonneg_left hsqrt1 hQ0
    rw [hdecomp]
    calc
      |vfMidLiError ((R : ℝ) ^ 2) + vfMidLiveQuadratureError R x|
          ≤ |vfMidLiError ((R : ℝ) ^ 2)| +
              |vfMidLiveQuadratureError R x| := abs_add_le _ _
      _ ≤ (A + (R : ℝ) * Q) + Q := by
        exact add_le_add hend hlive
      _ ≤ A * Real.sqrt x +
            Q * Real.sqrt x + Q * Real.sqrt x := by
        linarith
      _ = (A + 2 * Q) * Real.sqrt x := by ring

/-- The sole arithmetic target.

This is the exact von-Koch scale on the running error.  It deliberately asks
for no per-band bound and no stronger log-free root estimate. -/
def VFMidVonKochBoundedStatement : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ x : ℝ, 4 ≤ x →
      |vfMidPrimeError x| ≤
        C * Real.sqrt x * Real.log x

/-- Classical prime-count form of the von-Koch scale, expressed using the same
real prime-count staircase and the repository's logarithmicIntegralFromTwo. -/
def PrimeLiVonKochBoundedStatement : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ x : ℝ, 4 ≤ x →
      |vfMidPrimeLiError x| ≤
        C * Real.sqrt x * Real.log x

/-- Mathlib currently does not expose the classical von-Koch equivalence in
this normalization.  As elsewhere in this repository for the classical Mertens
criterion, package that standard analytic theorem as an explicit interface. -/
structure ClassicalVonKochRHCriterion where
  iff_riemannHypothesis :
    PrimeLiVonKochBoundedStatement ↔ VFMidRiemannHypothesisStatement

/-! ## Deterministic transfer from VF_mid to the classical discrepancy -/

/-- On x >= 4, the von-Koch weight sqrt x * log x is bounded below by the
positive constant 2 * log 4. -/
theorem two_log_four_le_sqrt_mul_log {x : ℝ} (hx : 4 ≤ x) :
    2 * Real.log 4 ≤ Real.sqrt x * Real.log x := by
  have hx0 : 0 ≤ x := by linarith
  have hsqrt : 2 ≤ Real.sqrt x := by
    have hs := Real.sq_sqrt hx0
    have hs0 := Real.sqrt_nonneg x
    nlinarith
  have hlog : Real.log 4 ≤ Real.log x :=
    Real.log_le_log (by norm_num) hx
  have hlog0 : 0 ≤ Real.log 4 :=
    (Real.log_pos (by norm_num)).le
  calc
    2 * Real.log 4 ≤ Real.sqrt x * Real.log 4 :=
      mul_le_mul_of_nonneg_right hsqrt hlog0
    _ ≤ Real.sqrt x * Real.log x :=
      mul_le_mul_of_nonneg_left hlog (Real.sqrt_nonneg x)

/-- A bounded midpoint quadrature error plus the frozen VF_mid running bound
gives the classical prime-minus-Li von-Koch bound. -/
theorem primeLiVonKochBounded_of_vfMid
    (hquad : VFMidLiRootBoundedStatement)
    (hvf : VFMidVonKochBoundedStatement) :
    PrimeLiVonKochBoundedStatement := by
  rcases hquad with ⟨B, hB0, hB⟩
  rcases hvf with ⟨C, hC0, hC⟩
  let ell : ℝ := Real.log 4
  have hell0 : 0 < ell := by
    dsimp [ell]
    exact Real.log_pos (by norm_num)
  refine ⟨C + B / ell, add_nonneg hC0 (div_nonneg hB0 hell0.le), ?_⟩
  intro x hx
  have hlog : ell ≤ Real.log x := by
    dsimp [ell]
    exact Real.log_le_log (by norm_num) hx
  have hsqrt0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hcoef0 : 0 ≤ (B / ell) * Real.sqrt x :=
    mul_nonneg (div_nonneg hB0 hell0.le) hsqrt0
  have hroot :
      B * Real.sqrt x ≤ (B / ell) * Real.sqrt x * Real.log x := by
    have hm := mul_le_mul_of_nonneg_left hlog hcoef0
    have heq : (B / ell) * Real.sqrt x * ell = B * Real.sqrt x := by
      field_simp [hell0.ne']
    linarith
  calc
    |vfMidPrimeLiError x|
        = |vfMidPrimeError x + vfMidLiError x| := by
            rw [vfMidPrimeLiError_eq_primeError_add_liError]
    _ ≤ |vfMidPrimeError x| + |vfMidLiError x| := abs_add_le _ _
    _ ≤ C * Real.sqrt x * Real.log x + B * Real.sqrt x :=
      add_le_add (hC x hx) (hB x hx)
    _ ≤ (C + B / ell) * Real.sqrt x * Real.log x := by
      calc
        C * Real.sqrt x * Real.log x + B * Real.sqrt x
            ≤ C * Real.sqrt x * Real.log x +
                (B / ell) * Real.sqrt x * Real.log x :=
          add_le_add_left hroot _
        _ = (C + B / ell) * Real.sqrt x * Real.log x := by ring

/-- Once the unconditional quadrature bridge is kernel-checked, the only
remaining hypothesis in this route is VFMidVonKochBoundedStatement. -/
theorem riemannHypothesis_of_vfMidVonKoch
    (criterion : ClassicalVonKochRHCriterion)
    (hquad : VFMidLiRootBoundedStatement)
    (hvf : VFMidVonKochBoundedStatement) :
    VFMidRiemannHypothesisStatement :=
  criterion.iff_riemannHypothesis.mp
    (primeLiVonKochBounded_of_vfMid hquad hvf)

end RHLean.Analysis
