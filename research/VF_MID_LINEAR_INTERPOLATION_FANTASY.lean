import Mathlib
import «research.VF_MID_VON_KOCH_BRIDGE»
import RHLean.Analysis.PrimeSieveLipschitzExcursion

/-!
# Literal midpoint-to-midpoint interpolation of VF_mid

The direct VF route already defines a continuous live-band midpoint quadrature
path.  This file constructs the distinct object requested for the fantasy
model audit: the literal piecewise-linear interpolation through the values of
vfMid at consecutive square-band midpoints.

The theorem proved here is deterministic:

  vfMidLinearMidpointInterpolant(x) = Li_2(x) + O(sqrt x).

Thus, under the explicit fantasy identification of this interpolant with the
actual prime-counting staircase, the classical von-Koch criterion closes RH.
No identification with actual primes is asserted unconditionally.
-/

noncomputable section

namespace RHLean.Analysis

/-- Consecutive square-band midpoints are separated by exactly 2r+2. -/
theorem vfMidBandMidpoint_succ_sub (r : ℕ) :
    vfMidBandMidpoint (r + 1) - vfMidBandMidpoint r =
      2 * (r : ℝ) + 2 := by
  unfold vfMidBandMidpoint
  push_cast
  ring

/-- Literal linear interpolation between the sampled vfMid values at the
midpoints of square bands r and r+1. -/
def vfMidLinearMidpointSegment (r : ℕ) (x : ℝ) : ℝ :=
  vfMid (vfMidBandMidpoint r) +
    ((x - vfMidBandMidpoint r) / (2 * (r : ℝ) + 2)) *
      (vfMid (vfMidBandMidpoint (r + 1)) -
        vfMid (vfMidBandMidpoint r))

@[simp] theorem vfMidLinearMidpointSegment_left (r : ℕ) :
    vfMidLinearMidpointSegment r (vfMidBandMidpoint r) =
      vfMid (vfMidBandMidpoint r) := by
  simp [vfMidLinearMidpointSegment]

@[simp] theorem vfMidLinearMidpointSegment_right (r : ℕ) :
    vfMidLinearMidpointSegment r (vfMidBandMidpoint (r + 1)) =
      vfMid (vfMidBandMidpoint (r + 1)) := by
  have hden : (2 * (r : ℝ) + 2) ≠ 0 := by positivity
  simp [vfMidLinearMidpointSegment, vfMidBandMidpoint_succ_sub, hden]

/-- The global literal midpoint interpolant.  On the finite initial interval
below the first meaningful midpoint m_2 it agrees with vfMid.  Thereafter the
existing square-root index chooses the square band and a single midpoint test
selects the left or right adjacent midpoint segment. -/
def vfMidLinearMidpointInterpolant (x : ℝ) : ℝ :=
  if x < vfMidBandMidpoint 2 then vfMid x
  else
    let R := vfMidSquareRootIndex x
    if x < vfMidBandMidpoint R then
      vfMidLinearMidpointSegment (R - 1) x
    else
      vfMidLinearMidpointSegment R x

set_option maxHeartbeats 1000000

/-- Segment estimate used by the global interpolation theorem. -/
private theorem abs_vfMidLinearMidpointSegment_sub_li_le
    (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ y : ℝ, 4 ≤ y →
      |vfMidLiError y| ≤ B * Real.sqrt y)
    {r : ℕ} (hr : 2 ≤ r) {x : ℝ}
    (hxl : vfMidBandMidpoint r ≤ x)
    (hxu : x ≤ vfMidBandMidpoint (r + 1)) :
    |vfMidLinearMidpointSegment r x -
        vfMidLogarithmicIntegralFromTwo x| ≤
      (3 * B + 6 / Real.log 4) * Real.sqrt x := by
  let a : ℝ := vfMidBandMidpoint r
  let b : ℝ := vfMidBandMidpoint (r + 1)
  let lam : ℝ := (x - a) / (2 * (r : ℝ) + 2)
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have ha4 : (4 : ℝ) ≤ a := by
    dsimp [a, vfMidBandMidpoint]
    nlinarith
  have hb4 : (4 : ℝ) ≤ b := by
    dsimp [b, vfMidBandMidpoint]
    push_cast
    nlinarith
  have hx4 : (4 : ℝ) ≤ x := ha4.trans hxl
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hwidth :
      b - a = 2 * (r : ℝ) + 2 := by
    dsimp [a, b]
    exact vfMidBandMidpoint_succ_sub r
  have hden : 0 < 2 * (r : ℝ) + 2 := by positivity
  have hlam0 : 0 ≤ lam := by
    dsimp [lam]
    exact div_nonneg (sub_nonneg.mpr hxl) hden.le
  have hlam1 : lam ≤ 1 := by
    dsimp [lam]
    rw [div_le_iff₀ hden]
    rw [← hwidth]
    linarith
  have hsqrtax : Real.sqrt a ≤ Real.sqrt x :=
    Real.sqrt_le_sqrt hxl
  have hrsq_le_x : (r : ℝ) ^ 2 ≤ x := by
    dsimp [a, vfMidBandMidpoint] at hxl
    nlinarith
  have hrle : (r : ℝ) ≤ Real.sqrt x := by
    calc
      (r : ℝ) = Real.sqrt ((r : ℝ) ^ 2) := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg]
        positivity
      _ ≤ Real.sqrt x := Real.sqrt_le_sqrt hrsq_le_x
  have hsqrt2 : (2 : ℝ) ≤ Real.sqrt x := hrR.trans hrle
  have hb_sq :
      b ≤ ((r : ℝ) + 2) ^ 2 := by
    dsimp [b, vfMidBandMidpoint]
    push_cast
    nlinarith
  have hsqrtb :
      Real.sqrt b ≤ (r : ℝ) + 2 := by
    calc
      Real.sqrt b ≤ Real.sqrt (((r : ℝ) + 2) ^ 2) :=
        Real.sqrt_le_sqrt hb_sq
      _ = (r : ℝ) + 2 := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg]
        positivity
  have hr2root : (r : ℝ) + 2 ≤ 2 * Real.sqrt x := by
    nlinarith
  have hEa := hB a ha4
  have hEa' :
      |vfMid a - vfMidLogarithmicIntegralFromTwo a| ≤
        B * Real.sqrt x := by
    change |vfMid a - vfMidLogarithmicIntegralFromTwo a| ≤
      B * Real.sqrt a at hEa
    exact hEa.trans (mul_le_mul_of_nonneg_left hsqrtax hB0)
  have hEb := hB b hb4
  have hEb' :
      |vfMid b - vfMidLogarithmicIntegralFromTwo b| ≤
        2 * B * Real.sqrt x := by
    change |vfMid b - vfMidLogarithmicIntegralFromTwo b| ≤
      B * Real.sqrt b at hEb
    have hs : B * Real.sqrt b ≤ B * (2 * Real.sqrt x) :=
      mul_le_mul_of_nonneg_left (hsqrtb.trans hr2root) hB0
    calc
      |vfMid b - vfMidLogarithmicIntegralFromTwo b|
          ≤ B * Real.sqrt b := hEb
      _ ≤ B * (2 * Real.sqrt x) := hs
      _ = 2 * B * Real.sqrt x := by ring
  have haSucc : (((3 : ℕ) : ℝ) + 1) ≤ a := by
    norm_num
    exact ha4
  have hLax0 :
      |logarithmicIntegralFromTwo x - logarithmicIntegralFromTwo a| ≤
        (x - a) / Real.log 4 := by
    have hraw :=
      abs_logarithmicIntegralFromTwo_sub_le_log_succ
        (y := 3) (a := a) (b := x) (by norm_num) haSucc hxl
    norm_num at hraw ⊢
    exact hraw
  have hLax :
      |vfMidLogarithmicIntegralFromTwo a -
          vfMidLogarithmicIntegralFromTwo x| ≤
        (2 * (r : ℝ) + 2) / Real.log 4 := by
    have h0 :
        |vfMidLogarithmicIntegralFromTwo x -
            vfMidLogarithmicIntegralFromTwo a| ≤
          (x - a) / Real.log 4 := by
      simpa [vfMidLogarithmicIntegralFromTwo,
        logarithmicIntegralFromTwo] using hLax0
    rw [abs_sub_comm]
    refine h0.trans ?_
    apply div_le_div_of_nonneg_right _ hlog4.le
    rw [← hwidth]
    linarith
  have hxSucc : (((3 : ℕ) : ℝ) + 1) ≤ x := by
    norm_num
    exact hx4
  have hLbx0 :
      |logarithmicIntegralFromTwo b - logarithmicIntegralFromTwo x| ≤
        (b - x) / Real.log 4 := by
    have hraw :=
      abs_logarithmicIntegralFromTwo_sub_le_log_succ
        (y := 3) (a := x) (b := b) (by norm_num) hxSucc hxu
    norm_num at hraw ⊢
    exact hraw
  have hLbx :
      |vfMidLogarithmicIntegralFromTwo b -
          vfMidLogarithmicIntegralFromTwo x| ≤
        (2 * (r : ℝ) + 2) / Real.log 4 := by
    have h0 :
        |vfMidLogarithmicIntegralFromTwo b -
            vfMidLogarithmicIntegralFromTwo x| ≤
          (b - x) / Real.log 4 := by
      simpa [vfMidLogarithmicIntegralFromTwo,
        logarithmicIntegralFromTwo] using hLbx0
    refine h0.trans ?_
    apply div_le_div_of_nonneg_right _ hlog4.le
    rw [← hwidth]
    linarith
  have hA :
      |vfMid a - vfMidLogarithmicIntegralFromTwo x| ≤
        B * Real.sqrt x +
          (2 * (r : ℝ) + 2) / Real.log 4 := by
    calc
      |vfMid a - vfMidLogarithmicIntegralFromTwo x|
          = |(vfMid a - vfMidLogarithmicIntegralFromTwo a) +
              (vfMidLogarithmicIntegralFromTwo a -
                vfMidLogarithmicIntegralFromTwo x)| := by
              congr 1
              ring
      _ ≤ |vfMid a - vfMidLogarithmicIntegralFromTwo a| +
            |vfMidLogarithmicIntegralFromTwo a -
              vfMidLogarithmicIntegralFromTwo x| := abs_add_le _ _
      _ ≤ _ := add_le_add hEa' hLax
  have hBpoint :
      |vfMid b - vfMidLogarithmicIntegralFromTwo x| ≤
        2 * B * Real.sqrt x +
          (2 * (r : ℝ) + 2) / Real.log 4 := by
    calc
      |vfMid b - vfMidLogarithmicIntegralFromTwo x|
          = |(vfMid b - vfMidLogarithmicIntegralFromTwo b) +
              (vfMidLogarithmicIntegralFromTwo b -
                vfMidLogarithmicIntegralFromTwo x)| := by
              congr 1
              ring
      _ ≤ |vfMid b - vfMidLogarithmicIntegralFromTwo b| +
            |vfMidLogarithmicIntegralFromTwo b -
              vfMidLogarithmicIntegralFromTwo x| := abs_add_le _ _
      _ ≤ _ := add_le_add hEb' hLbx
  have hseg :
      vfMidLinearMidpointSegment r x =
        (1 - lam) * vfMid a + lam * vfMid b := by
    unfold vfMidLinearMidpointSegment
    dsimp [a, b, lam]
    ring
  have hconv :
      |vfMidLinearMidpointSegment r x -
          vfMidLogarithmicIntegralFromTwo x| ≤
        |vfMid a - vfMidLogarithmicIntegralFromTwo x| +
          |vfMid b - vfMidLogarithmicIntegralFromTwo x| := by
    rw [hseg]
    have hdecomp :
        (1 - lam) * vfMid a + lam * vfMid b -
            vfMidLogarithmicIntegralFromTwo x =
          (1 - lam) *
              (vfMid a - vfMidLogarithmicIntegralFromTwo x) +
            lam * (vfMid b - vfMidLogarithmicIntegralFromTwo x) := by
      ring
    rw [hdecomp]
    calc
      |(1 - lam) * (vfMid a - vfMidLogarithmicIntegralFromTwo x) +
          lam * (vfMid b - vfMidLogarithmicIntegralFromTwo x)|
          ≤ |(1 - lam) *
              (vfMid a - vfMidLogarithmicIntegralFromTwo x)| +
            |lam * (vfMid b - vfMidLogarithmicIntegralFromTwo x)| :=
              abs_add_le _ _
      _ = (1 - lam) *
              |vfMid a - vfMidLogarithmicIntegralFromTwo x| +
            lam * |vfMid b - vfMidLogarithmicIntegralFromTwo x| := by
              rw [abs_mul, abs_mul, abs_of_nonneg (by linarith),
                abs_of_nonneg hlam0]
      _ ≤ |vfMid a - vfMidLogarithmicIntegralFromTwo x| +
            |vfMid b - vfMidLogarithmicIntegralFromTwo x| := by
              have h1 :=
                mul_le_mul_of_nonneg_right
                  (show 1 - lam ≤ 1 by linarith)
                  (abs_nonneg
                    (vfMid a - vfMidLogarithmicIntegralFromTwo x))
              have h2 :=
                mul_le_mul_of_nonneg_right hlam1
                  (abs_nonneg
                    (vfMid b - vfMidLogarithmicIntegralFromTwo x))
              nlinarith
  have hwidthRoot :
      2 * (r : ℝ) + 2 ≤ 3 * Real.sqrt x := by
    nlinarith
  have hwidthDiv :
      (2 * (r : ℝ) + 2) / Real.log 4 ≤
        (3 / Real.log 4) * Real.sqrt x := by
    have h :=
      div_le_div_of_nonneg_right hwidthRoot hlog4.le
    calc
      (2 * (r : ℝ) + 2) / Real.log 4
          ≤ (3 * Real.sqrt x) / Real.log 4 := h
      _ = (3 / Real.log 4) * Real.sqrt x := by ring
  calc
    |vfMidLinearMidpointSegment r x -
        vfMidLogarithmicIntegralFromTwo x|
        ≤ |vfMid a - vfMidLogarithmicIntegralFromTwo x| +
            |vfMid b - vfMidLogarithmicIntegralFromTwo x| := hconv
    _ ≤ (B * Real.sqrt x +
          (2 * (r : ℝ) + 2) / Real.log 4) +
        (2 * B * Real.sqrt x +
          (2 * (r : ℝ) + 2) / Real.log 4) :=
      add_le_add hA hBpoint
    _ ≤ (B * Real.sqrt x + (3 / Real.log 4) * Real.sqrt x) +
        (2 * B * Real.sqrt x + (3 / Real.log 4) * Real.sqrt x) := by
      exact add_le_add
        (add_le_add_left hwidthDiv _)
        (add_le_add_left hwidthDiv _)
    _ = (3 * B + 6 / Real.log 4) * Real.sqrt x := by ring

set_option maxHeartbeats 200000

/-- Root-scale deterministic comparison of the literal midpoint interpolant to
Li on every real cutoff x >= 4. -/
def VFMidLinearMidpointLiRootBoundedStatement : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ x : ℝ, 4 ≤ x →
      |vfMidLinearMidpointInterpolant x -
          vfMidLogarithmicIntegralFromTwo x| ≤
        C * Real.sqrt x

theorem vfMidLinearMidpoint_li_root_bounded :
    VFMidLinearMidpointLiRootBoundedStatement := by
  rcases vfMidLiRootBounded with ⟨B, hB0, hB⟩
  let C : ℝ := 3 * B + 6 / Real.log 4
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC0, ?_⟩
  intro x hx
  by_cases hsmall : x < vfMidBandMidpoint 2
  · simp [vfMidLinearMidpointInterpolant, hsmall]
    have h := hB x hx
    change |vfMid x - vfMidLogarithmicIntegralFromTwo x| ≤
      B * Real.sqrt x at h
    have hBC : B ≤ C := by
      dsimp [C]
      have : 0 ≤ 6 / Real.log 4 := by positivity
      nlinarith
    exact h.trans
      (mul_le_mul_of_nonneg_right hBC (Real.sqrt_nonneg x))
  · have hm2x : vfMidBandMidpoint 2 ≤ x := le_of_not_gt hsmall
    let R : ℕ := vfMidSquareRootIndex x
    obtain ⟨hR, hsqL, hsqU, _⟩ := vfMidSquareRootIndex_bounds hx
    change 2 ≤ R at hR
    change (R : ℝ) ^ 2 ≤ x at hsqL
    change x ≤ (((R + 1 : ℕ) : ℝ) ^ 2) at hsqU
    by_cases hleft : x < vfMidBandMidpoint R
    · have hRne : R ≠ 2 := by
        intro hR2
        have hge : vfMidBandMidpoint R ≤ x := by
          simpa [hR2] using hm2x
        exact (not_lt_of_ge hge) hleft
      have hR3 : 3 ≤ R := by omega
      have hr : 2 ≤ R - 1 := by omega
      have hmidL : vfMidBandMidpoint (R - 1) ≤ x := by
        have hprev : vfMidBandMidpoint (R - 1) ≤ (R : ℝ) ^ 2 := by
          have hcast : ((R - 1 : ℕ) : ℝ) = (R : ℝ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ R)]
            norm_num
          unfold vfMidBandMidpoint
          rw [hcast]
          nlinarith
        exact hprev.trans hsqL
      have hmidU : x ≤ vfMidBandMidpoint ((R - 1) + 1) := by
        have hEq : (R - 1) + 1 = R := by omega
        rw [hEq]
        exact hleft.le
      have hseg :=
        abs_vfMidLinearMidpointSegment_sub_li_le
          B hB0 hB hr hmidL hmidU
      have hdef :
          vfMidLinearMidpointInterpolant x =
            vfMidLinearMidpointSegment (R - 1) x := by
        simp [vfMidLinearMidpointInterpolant, hsmall, R, hleft]
      rw [hdef]
      simpa [C] using hseg
    · have hmidL : vfMidBandMidpoint R ≤ x := le_of_not_gt hleft
      have hmidU : x ≤ vfMidBandMidpoint (R + 1) := by
        have hsquareMid :
            (((R + 1 : ℕ) : ℝ) ^ 2) ≤
              vfMidBandMidpoint (R + 1) := by
          unfold vfMidBandMidpoint
          have hnonneg : 0 ≤ ((R + 1 : ℕ) : ℝ) := by positivity
          nlinarith
        exact hsqU.trans hsquareMid
      have hseg :=
        abs_vfMidLinearMidpointSegment_sub_li_le
          B hB0 hB hR hmidL hmidU
      have hdef :
          vfMidLinearMidpointInterpolant x =
            vfMidLinearMidpointSegment R x := by
        simp [vfMidLinearMidpointInterpolant, hsmall, R, hleft]
      rw [hdef]
      simpa [C] using hseg

/-- Fantasy identification of the literal VF midpoint interpolant with actual
prime count. -/
def VFMidLinearMidpointIdentifiesActualPrimes : Prop :=
  ∀ x : ℝ, 4 ≤ x →
    vfMidPrimeCount x = vfMidLinearMidpointInterpolant x

/-- The linear-interpolation fantasy identification gives the actual
prime-minus-Li von-Koch bound. -/
theorem primeLiVonKochBounded_of_vfMidLinearMidpointIdentification
    (hident : VFMidLinearMidpointIdentifiesActualPrimes) :
    PrimeLiVonKochBoundedStatement := by
  rcases vfMidLinearMidpoint_li_root_bounded with ⟨B, hB0, hB⟩
  let ell : ℝ := Real.log 4
  have hell : 0 < ell := by
    dsimp [ell]
    exact Real.log_pos (by norm_num)
  refine ⟨B / ell, div_nonneg hB0 hell.le, ?_⟩
  intro x hx
  have hroot := hB x hx
  have hlog : ell ≤ Real.log x := by
    dsimp [ell]
    exact Real.log_le_log (by norm_num) hx
  have hcoef0 : 0 ≤ (B / ell) * Real.sqrt x :=
    mul_nonneg (div_nonneg hB0 hell.le) (Real.sqrt_nonneg x)
  have hscale :
      B * Real.sqrt x ≤
        (B / ell) * Real.sqrt x * Real.log x := by
    have hm := mul_le_mul_of_nonneg_left hlog hcoef0
    have heq :
        (B / ell) * Real.sqrt x * ell = B * Real.sqrt x := by
      field_simp [hell.ne']
    linarith
  unfold vfMidPrimeLiError
  rw [hident x hx]
  exact hroot.trans hscale

/-- Literal VF midpoint-linear fantasy closure. -/
theorem riemannHypothesis_of_vfMidLinearMidpointIdentification
    (criterion : ClassicalVonKochRHCriterion)
    (hident : VFMidLinearMidpointIdentifiesActualPrimes) :
    VFMidRiemannHypothesisStatement :=
  criterion.iff_riemannHypothesis.mp
    (primeLiVonKochBounded_of_vfMidLinearMidpointIdentification hident)

end RHLean.Analysis
