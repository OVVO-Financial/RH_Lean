import Mathlib
import «research.FOUR_FANTASY_PROXY_RH_CLOSURES»
import «research.VF_MID_ALIGNED_STEP_GRAPH»

/-!
# Solved fantasy cone for the direct VF-mid prime target

The four deterministic fantasy coordinates are already proved to lie at
root scale from the same Li/VF center:

* continuous Li;
* the exact fractional VF cluster;
* the literal midpoint-linear VF interpolant;
* integer-cutoff floor(Li).

This file packages those solved directions into a single admissible cone at
square endpoints.  The cone has a finite coefficient budget `A` and a finite
vertical phase budget `C0`.  Coefficients may vary with the square scale; no
fixed phase or fixed trajectory is imposed.

The analytic part is unconditional: every point in this cone is root-scale
from `VF_mid`, hence automatically inside the weaker `R log R` von-Koch
envelope.

The sole arithmetic input is stated separately:

    ActualPrimeContainedInSolvedFantasyConeStatement

It says only that the honest prime-counting endpoint belongs to this already
safe cone.  No empirical Monte-Carlo behavior and no unknown realized
prime-error cancellation is used in the proof of cone safety.
-/

noncomputable section

namespace RHLean.Analysis

/-- The total solved fantasy displacement away from `VF_mid` at the square
endpoint `R^2`.  In one real endpoint coordinate, an l1-bounded combination
of the four solved directions is exactly controlled by this radius. -/
def vfMidSolvedFantasyConeRadius (R : ℕ) : ℝ :=
  let x : ℝ := (R : ℝ) ^ 2
  |vfMidLogarithmicIntegralFromTwo x - vfMid x| +
    |vfMidFractionalPrimeClusterMass R - vfMid x| +
    |vfMidLinearMidpointInterpolant x - vfMid x| +
    |liIntegerCutoffFloorPrimeCountProxy x - vfMid x|

theorem vfMidSolvedFantasyConeRadius_nonneg (R : ℕ) :
    0 ≤ vfMidSolvedFantasyConeRadius R := by
  unfold vfMidSolvedFantasyConeRadius
  positivity

/-- A scalar endpoint lies in the solved fantasy cone when its displacement
from VF is no larger than an `A`-multiple of the total solved fantasy radius,
plus a bounded vertical phase allowance `C0`. -/
def VFMidSolvedFantasyConeAt
    (A C0 : ℝ) (R : ℕ) (y : ℝ) : Prop :=
  |y - vfMid ((R : ℝ) ^ 2)| ≤
    A * vfMidSolvedFantasyConeRadius R + C0

/-- The canonical aligned VF path is a pure phase direction of the cone.
This records the role of a finite `c_0`-type vertical allowance without
requiring one fixed aligned graph to intersect the prime staircase forever. -/
theorem vfMidAligned_sq_mem_solvedFantasyCone
    {c C0 : ℝ} (hc : |c| ≤ C0)
    {R : ℕ} (hR : 2 ≤ R) :
    VFMidSolvedFantasyConeAt 0 C0 R
      (vfMidAligned c ((R : ℝ) ^ 2)) := by
  unfold VFMidSolvedFantasyConeAt vfMidAligned
  rw [zero_mul, zero_add]
  simpa only [add_sub_cancel_left] using hc

/-- All four solved fantasy directions together have only root-scale radius. -/
theorem vfMidSolvedFantasyConeRadius_le_root :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ R : ℕ, 2 ≤ R →
        vfMidSolvedFantasyConeRadius R ≤ K * (R : ℝ) := by
  rcases vfMidLiRootBounded with ⟨Bvf, hBvf0, hBvf⟩
  rcases vfMidLinearProxy_li_root_bounded with ⟨Blin, hBlin0, hBlin⟩
  rcases liFloorProxy_li_root_bounded with ⟨Bfloor, hBfloor0, hBfloor⟩
  let K : ℝ := 3 * Bvf + Blin + Bfloor
  have hK0 : 0 ≤ K := by
    dsimp [K]
    positivity
  refine ⟨K, hK0, ?_⟩
  intro R hR
  let x : ℝ := (R : ℝ) ^ 2
  have h4nat : 4 ≤ R ^ 2 := by nlinarith
  have hx4 : (4 : ℝ) ≤ x := by
    dsimp [x]
    exact_mod_cast h4nat
  have hR0 : (0 : ℝ) ≤ (R : ℝ) := by positivity
  have hsqrt : Real.sqrt x = (R : ℝ) := by
    dsimp [x]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hR0]

  have hvf0 := hBvf x hx4
  have hvf :
      |vfMidLogarithmicIntegralFromTwo x - vfMid x| ≤
        Bvf * (R : ℝ) := by
    simpa [vfMidLiError, hsqrt, abs_sub_comm] using hvf0

  have hfrac :
      |vfMidFractionalPrimeClusterMass R - vfMid x| = 0 := by
    have heq := vfMidFractionalPrimeClusterMass_eq_vfMid_sq R hR
    dsimp [x]
    rw [heq, sub_self, abs_zero]

  have hlinLi0 := hBlin x hx4
  have hlinLi :
      |vfMidLinearMidpointInterpolant x -
          vfMidLogarithmicIntegralFromTwo x| ≤
        Blin * (R : ℝ) := by
    simpa [hsqrt] using hlinLi0
  have hlin :
      |vfMidLinearMidpointInterpolant x - vfMid x| ≤
        (Blin + Bvf) * (R : ℝ) := by
    calc
      |vfMidLinearMidpointInterpolant x - vfMid x|
          = |(vfMidLinearMidpointInterpolant x -
                vfMidLogarithmicIntegralFromTwo x) +
              (vfMidLogarithmicIntegralFromTwo x - vfMid x)| := by
                congr 1
                ring
      _ ≤ |vfMidLinearMidpointInterpolant x -
              vfMidLogarithmicIntegralFromTwo x| +
            |vfMidLogarithmicIntegralFromTwo x - vfMid x| :=
          abs_add_le _ _
      _ ≤ Blin * (R : ℝ) + Bvf * (R : ℝ) :=
          add_le_add hlinLi hvf
      _ = (Blin + Bvf) * (R : ℝ) := by ring

  have hfloorLi0 := hBfloor x hx4
  have hfloorLi :
      |liIntegerCutoffFloorPrimeCountProxy x -
          vfMidLogarithmicIntegralFromTwo x| ≤
        Bfloor * (R : ℝ) := by
    simpa [hsqrt] using hfloorLi0
  have hfloor :
      |liIntegerCutoffFloorPrimeCountProxy x - vfMid x| ≤
        (Bfloor + Bvf) * (R : ℝ) := by
    calc
      |liIntegerCutoffFloorPrimeCountProxy x - vfMid x|
          = |(liIntegerCutoffFloorPrimeCountProxy x -
                vfMidLogarithmicIntegralFromTwo x) +
              (vfMidLogarithmicIntegralFromTwo x - vfMid x)| := by
                congr 1
                ring
      _ ≤ |liIntegerCutoffFloorPrimeCountProxy x -
              vfMidLogarithmicIntegralFromTwo x| +
            |vfMidLogarithmicIntegralFromTwo x - vfMid x| :=
          abs_add_le _ _
      _ ≤ Bfloor * (R : ℝ) + Bvf * (R : ℝ) :=
          add_le_add hfloorLi hvf
      _ = (Bfloor + Bvf) * (R : ℝ) := by ring

  dsimp [vfMidSolvedFantasyConeRadius, x, K]
  have hfrac' :
      |vfMidFractionalPrimeClusterMass R - vfMid ((R : ℝ) ^ 2)| = 0 := by
    simpa [x] using hfrac
  rw [hfrac']
  have hvf' :
      |vfMidLogarithmicIntegralFromTwo ((R : ℝ) ^ 2) -
          vfMid ((R : ℝ) ^ 2)| ≤ Bvf * (R : ℝ) := by
    simpa [x] using hvf
  have hlin' :
      |vfMidLinearMidpointInterpolant ((R : ℝ) ^ 2) -
          vfMid ((R : ℝ) ^ 2)| ≤
        (Blin + Bvf) * (R : ℝ) := by
    simpa [x] using hlin
  have hfloor' :
      |liIntegerCutoffFloorPrimeCountProxy ((R : ℝ) ^ 2) -
          vfMid ((R : ℝ) ^ 2)| ≤
        (Bfloor + Bvf) * (R : ℝ) := by
    simpa [x] using hfloor
  nlinarith

/-- The entire solved fantasy cone is uniformly root-safe.  This is the
compiled analytic half of the cone strategy. -/
theorem vfMidSolvedFantasyCone_root_safe
    {A C0 : ℝ} (hA : 0 ≤ A) (hC0 : 0 ≤ C0) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ R : ℕ, 2 ≤ R →
      ∀ y : ℝ, VFMidSolvedFantasyConeAt A C0 R y →
        |y - vfMid ((R : ℝ) ^ 2)| ≤ C * (R : ℝ) := by
  rcases vfMidSolvedFantasyConeRadius_le_root with ⟨K, hK0, hK⟩
  let C : ℝ := A * K + C0
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro R hR y hy
  have hradius := hK R hR
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by
    exact_mod_cast (show 1 ≤ R by omega)
  have hphase : C0 ≤ C0 * (R : ℝ) := by
    simpa using mul_le_mul_of_nonneg_left hR1 hC0
  have hscaled :
      A * vfMidSolvedFantasyConeRadius R + C0 ≤
        C * (R : ℝ) := by
    have hmul :=
      mul_le_mul_of_nonneg_left hradius hA
    dsimp [C]
    calc
      A * vfMidSolvedFantasyConeRadius R + C0
          ≤ A * (K * (R : ℝ)) + C0 := add_le_add_right hmul C0
      _ ≤ A * (K * (R : ℝ)) + C0 * (R : ℝ) :=
          add_le_add_left hphase _
      _ = (A * K + C0) * (R : ℝ) := by ring
  exact hy.trans hscaled

/-- The single open arithmetic statement of the cone route:
the honest prime-count endpoint belongs to one fixed finite-budget solved
fantasy cone at every square scale. -/
def ActualPrimeContainedInSolvedFantasyConeStatement : Prop :=
  ∃ A C0 : ℝ, 0 ≤ A ∧ 0 ≤ C0 ∧
    ∀ R : ℕ, 2 ≤ R →
      VFMidSolvedFantasyConeAt A C0 R
        (vfMidPrimeCount ((R : ℝ) ^ 2))

/-- Cone inclusion alone closes the direct square-endpoint VF target. -/
theorem vfMidSquareEndpointVonKochBounded_of_actualPrimeContainedInSolvedFantasyCone
    (hcone : ActualPrimeContainedInSolvedFantasyConeStatement) :
    VFMidSquareEndpointVonKochBoundedStatement := by
  rcases hcone with ⟨A, C0, hA, hC0, hcontain⟩
  rcases vfMidSolvedFantasyCone_root_safe hA hC0 with
    ⟨B, hB0, hB⟩
  let C : ℝ := B / Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact div_nonneg hB0 hlog2.le
  refine ⟨C, hC, ?_⟩
  intro R hR
  have hroot :=
    hB R hR (vfMidPrimeCount ((R : ℝ) ^ 2)) (hcontain R hR)
  have hR0 : (0 : ℝ) ≤ (R : ℝ) := by positivity
  have hlogR : Real.log 2 ≤ Real.log (R : ℝ) := by
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hR)
  have hcoef0 : 0 ≤ (B / Real.log 2) * (R : ℝ) :=
    mul_nonneg (div_nonneg hB0 hlog2.le) hR0
  have hscale :
      B * (R : ℝ) ≤
        (B / Real.log 2) * (R : ℝ) * Real.log (R : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hlogR hcoef0
    have heq :
        (B / Real.log 2) * (R : ℝ) * Real.log 2 =
          B * (R : ℝ) := by
      field_simp [hlog2.ne']
    linarith
  unfold vfMidPrimeError
  exact hroot.trans (by simpa [C] using hscale)

/-- Existing downstream plumbing: once actual prime count is in the solved
fantasy cone, the already-compiled square-endpoint consumer closes RH. -/
theorem riemannHypothesis_of_actualPrimeContainedInSolvedFantasyCone
    (criterion : ClassicalVonKochRHCriterion)
    (hcone : ActualPrimeContainedInSolvedFantasyConeStatement) :
    VFMidRiemannHypothesisStatement :=
  riemannHypothesis_of_vfMidSquareEndpoint criterion
    (vfMidSquareEndpointVonKochBounded_of_actualPrimeContainedInSolvedFantasyCone
      hcone)

end RHLean.Analysis
