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
square endpoints.  The cone uses the full RH-safe freedom: a fixed budget `K`
multiplies `log R`, while `C0` supplies a bounded vertical phase allowance.
Thus the admissible fantasy coefficients may grow logarithmically with scale;
no fixed phase or fixed trajectory is imposed.

The analytic part is unconditional: the fantasy radius itself is root-scale,
so a `K * log R` coefficient budget puts every cone point directly inside the
`R log R` von-Koch envelope.

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
from VF is no larger than a `K * log R` multiple of the total solved fantasy
radius, plus a bounded vertical phase allowance `C0`.  The logarithmic growth
uses the full scale allowed by the square-endpoint von-Koch target instead of
artificially restricting the cone to a fixed root-scale coefficient. -/
def VFMidSolvedFantasyConeAt
    (K C0 : ℝ) (R : ℕ) (y : ℝ) : Prop :=
  |y - vfMid ((R : ℝ) ^ 2)| ≤
    (K * Real.log (R : ℝ)) * vfMidSolvedFantasyConeRadius R + C0

/-- The canonical aligned VF path is a pure phase direction of the cone.
This records the role of a finite `c_0`-type vertical allowance without
requiring one fixed aligned graph to intersect the prime staircase forever. -/
theorem vfMidAligned_sq_mem_solvedFantasyCone
    {c C0 : ℝ} (hc : |c| ≤ C0)
    {R : ℕ} (_hR : 2 ≤ R) :
    VFMidSolvedFantasyConeAt 0 C0 R
      (vfMidAligned c ((R : ℝ) ^ 2)) := by
  unfold VFMidSolvedFantasyConeAt vfMidAligned
  have hleft :
      vfMid ((R : ℝ) ^ 2) + c - vfMid ((R : ℝ) ^ 2) = c := by
    ring
  rw [hleft]
  simpa using hc

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

/-- The expanded solved fantasy cone is uniformly von-Koch safe.  The fantasy
radius is only root-scale, so allowing its coefficient budget to grow like
`K * log R` uses the full `R log R` room without exceeding the target. -/
theorem vfMidSolvedFantasyCone_vonKoch_safe
    {K C0 : ℝ} (hK : 0 ≤ K) (hC0 : 0 ≤ C0) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ R : ℕ, 2 ≤ R →
      ∀ y : ℝ, VFMidSolvedFantasyConeAt K C0 R y →
        |y - vfMid ((R : ℝ) ^ 2)| ≤
          C * (R : ℝ) * Real.log (R : ℝ) := by
  rcases vfMidSolvedFantasyConeRadius_le_root with ⟨B, hB0, hB⟩
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let C : ℝ := K * B + C0 / Real.log 2
  have hC : 0 ≤ C := by
    dsimp [C]
    exact add_nonneg (mul_nonneg hK hB0) (div_nonneg hC0 hlog2.le)
  refine ⟨C, hC, ?_⟩
  intro R hR y hy
  have hradius := hB R hR
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by
    exact_mod_cast (show 1 ≤ R by omega)
  have hlogR : Real.log 2 ≤ Real.log (R : ℝ) := by
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hR)
  have hlogR0 : 0 ≤ Real.log (R : ℝ) :=
    le_trans hlog2.le hlogR
  have hweight0 :
      0 ≤ K * Real.log (R : ℝ) :=
    mul_nonneg hK hlogR0
  have hmul :
      (K * Real.log (R : ℝ)) * vfMidSolvedFantasyConeRadius R ≤
        (K * Real.log (R : ℝ)) * (B * (R : ℝ)) :=
    mul_le_mul_of_nonneg_left hradius hweight0
  have hphaseLog :
      C0 ≤ (C0 / Real.log 2) * Real.log (R : ℝ) := by
    have hcoef0 : 0 ≤ C0 / Real.log 2 :=
      div_nonneg hC0 hlog2.le
    have hm := mul_le_mul_of_nonneg_left hlogR hcoef0
    have heq :
        (C0 / Real.log 2) * Real.log 2 = C0 := by
      field_simp [hlog2.ne']
    linarith
  have hphase :
      C0 ≤ (C0 / Real.log 2) * (R : ℝ) * Real.log (R : ℝ) := by
    have hnonneg :
        0 ≤ (C0 / Real.log 2) * Real.log (R : ℝ) :=
      mul_nonneg (div_nonneg hC0 hlog2.le) hlogR0
    have hgrow :
        (C0 / Real.log 2) * Real.log (R : ℝ) ≤
          (C0 / Real.log 2) * (R : ℝ) * Real.log (R : ℝ) := by
      calc
        (C0 / Real.log 2) * Real.log (R : ℝ)
            = ((C0 / Real.log 2) * Real.log (R : ℝ)) * 1 := by ring
        _ ≤ ((C0 / Real.log 2) * Real.log (R : ℝ)) * (R : ℝ) :=
          mul_le_mul_of_nonneg_left hR1 hnonneg
        _ = (C0 / Real.log 2) * (R : ℝ) * Real.log (R : ℝ) := by ring
    exact hphaseLog.trans hgrow
  have hscaled :
      (K * Real.log (R : ℝ)) * vfMidSolvedFantasyConeRadius R + C0 ≤
        C * (R : ℝ) * Real.log (R : ℝ) := by
    calc
      (K * Real.log (R : ℝ)) * vfMidSolvedFantasyConeRadius R + C0
          ≤ (K * Real.log (R : ℝ)) * (B * (R : ℝ)) + C0 :=
            add_le_add_right hmul C0
      _ ≤ (K * Real.log (R : ℝ)) * (B * (R : ℝ)) +
            (C0 / Real.log 2) * (R : ℝ) * Real.log (R : ℝ) :=
          add_le_add_left hphase _
      _ = C * (R : ℝ) * Real.log (R : ℝ) := by
          dsimp [C]
          ring
  exact hy.trans hscaled

/-- The single open arithmetic statement of the cone route:
the honest prime-count endpoint belongs to one fixed logarithmic-budget solved
fantasy cone at every square scale.  The coefficient available at scale `R`
is `K * log R`, not a fixed `K`; this is the deliberately enlarged admissible
region. -/
def ActualPrimeContainedInSolvedFantasyConeStatement : Prop :=
  ∃ K C0 : ℝ, 0 ≤ K ∧ 0 ≤ C0 ∧
    ∀ R : ℕ, 2 ≤ R →
      VFMidSolvedFantasyConeAt K C0 R
        (vfMidPrimeCount ((R : ℝ) ^ 2))

/-- Cone inclusion alone closes the direct square-endpoint VF target. -/
theorem vfMidSquareEndpointVonKochBounded_of_actualPrimeContainedInSolvedFantasyCone
    (hcone : ActualPrimeContainedInSolvedFantasyConeStatement) :
    VFMidSquareEndpointVonKochBoundedStatement := by
  rcases hcone with ⟨K, C0, hK, hC0, hcontain⟩
  rcases vfMidSolvedFantasyCone_vonKoch_safe hK hC0 with
    ⟨C, hC0', hC⟩
  refine ⟨C, hC0', ?_⟩
  intro R hR
  have hsafe :=
    hC R hR (vfMidPrimeCount ((R : ℝ) ^ 2)) (hcontain R hR)
  unfold vfMidPrimeError
  simpa using hsafe

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
