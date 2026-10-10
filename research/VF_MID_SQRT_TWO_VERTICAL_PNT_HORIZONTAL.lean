import Mathlib
import «research.VF_MID_ALIGNED_STEP_GRAPH»
import RHLean.Analysis.NativePNTTransfer

/-!
# Chosen sqrt(2) vertical VF phase; proven PNT horizontal scale

The user-selected vertical phase is c = sqrt(2), *not* a claim
that sqrt(2) equals the existing exact x=9 calibration
4 - vfMidFinishedMass 3. An additive vertical phase changes no
VF square-band mass and changes no actual prime counts.

The horizontal step graph remains a separate arithmetic predicate.
Prime counting is defined exactly by Nat.Prime, and this module
imports the independently proved native Prime Number Theorem.
It exports PNT at the actual square-root clock, not an unjustified
per-square-band estimate, Legendre's conjecture, or RH.

The finite sqrt(2) vs original-anchor graph experiment is in
scripts/VFMidAlignedStepGraph/verify_c0_contract.py.
-/

noncomputable section

open Filter
open scoped Topology

namespace RHLean.Analysis

/-- Chosen fixed additive VF vertical phase. This does not redefine the
x=9 exact anchor, vfMidInitialAnchor. -/
def vfMidSqrtTwoVerticalPhase : ℝ := Real.sqrt 2

theorem vfMidSqrtTwoVerticalPhase_nonneg :
    0 ≤ vfMidSqrtTwoVerticalPhase := by
  exact Real.sqrt_nonneg 2

theorem vfMidSqrtTwoVerticalPhase_pos :
    0 < vfMidSqrtTwoVerticalPhase := by
  exact Real.sqrt_pos.2 (by norm_num)

theorem vfMidSqrtTwoVerticalPhase_sq :
    vfMidSqrtTwoVerticalPhase ^ 2 = 2 := by
  exact Real.sq_sqrt (by norm_num)

/-- The integer VF square-block staircase at the chosen vertical phase. -/
def vfMidSqrtTwoIntegerLevel (R : ℕ) : ℕ :=
  vfMidAlignedIntegerBlockLevel vfMidSqrtTwoVerticalPhase R

/-- The original REAL VF square-block increment is never rescaled. -/
theorem vfMidSqrtTwoAlignedMass_succ
    {R : ℕ} (hR : 2 ≤ R) :
    vfMidAlignedMass vfMidSqrtTwoVerticalPhase (R + 1) -
        vfMidAlignedMass vfMidSqrtTwoVerticalPhase R =
      vfMidBandMass R := by
  have h := vfMidAlignedMass_succ vfMidSqrtTwoVerticalPhase hR
  linarith

/-- The chosen integer staircase has an explicit *bounded*
rounding-phase correction; it does not alter the original VF mass. -/
theorem vfMidSqrtTwoIntegerLevel_step
    {R : ℕ} (hR : 2 ≤ R) :
    (vfMidSqrtTwoIntegerLevel (R + 1) : ℝ) -
        (vfMidSqrtTwoIntegerLevel R : ℝ) =
      vfMidBandMass R +
        vfMidAlignedRoundingPhase vfMidSqrtTwoVerticalPhase R -
        vfMidAlignedRoundingPhase vfMidSqrtTwoVerticalPhase (R + 1) := by
  exact vfMidAlignedIntegerBlockLevel_succ_real
    vfMidSqrtTwoVerticalPhase hR

/-- Horizontal graph intersection for the ORIGINAL actual-prime carrier:
the genuine prime staircase must cross the chosen integer VF level
in the current square block. This is not postulated universally. -/
def VFMidSqrtTwoHorizontalCrossed (R : ℕ) : Prop :=
  Nat.primeCounting (R ^ 2) ≤ vfMidSqrtTwoIntegerLevel R ∧
    vfMidSqrtTwoIntegerLevel R ≤
      Nat.primeCounting ((R + 1) ^ 2)

/-- Exact horizontal intersection expressed through true native prime
supply in this square block. No unknown or synthetic pi-function. -/
theorem vfMidSqrtTwoHorizontalCrossed_iff_actualSupply
    (R : ℕ) :
    VFMidSqrtTwoHorizontalCrossed R ↔
      Nat.primeCounting (R ^ 2) ≤ vfMidSqrtTwoIntegerLevel R ∧
      vfMidSqrtTwoIntegerLevel R ≤
        Nat.primeCounting (R ^ 2) + vfMidIntegerBlockPrimeSupply R := by
  unfold VFMidSqrtTwoHorizontalCrossed
  rw [← vfMidIntegerBlockPrimeSupply_add_primeCounting R]
  simp only [Nat.add_comm]

/-- Original factorization, not a new definition of pi, identifies the
physical horizontal supply exactly with the full prime-wheel survivor set. -/
theorem vfMidSqrtTwoHorizontalCrossed_iff_actualWheel
    (R : ℕ) (hR : 2 ≤ R) :
    VFMidSqrtTwoHorizontalCrossed R ↔
      Nat.primeCounting (R ^ 2) ≤ vfMidSqrtTwoIntegerLevel R ∧
      vfMidSqrtTwoIntegerLevel R ≤
        Nat.primeCounting (R ^ 2) +
          (vfMidSquarePrefixWheelSurvivors R R).card := by
  rw [vfMidSqrtTwoHorizontalCrossed_iff_actualSupply,
    vfMidIntegerBlockPrimeSupply_eq_fullPrefixWheelCard R hR]

/-- The original signed prime counting error with fixed sqrt(2) and the
fractional rounding phase. The arithmetic error is NOT made small
by this identity. -/
theorem vfMidSqrtTwoIntegerBacklog_eq_actualPrimeError
    (R : ℕ) :
    (vfMidSqrtTwoIntegerLevel R : ℝ) -
        (Nat.primeCounting (R ^ 2) : ℝ) =
      -vfMidDirectSquareEndpointError R +
        vfMidSqrtTwoVerticalPhase -
          vfMidAlignedRoundingPhase vfMidSqrtTwoVerticalPhase R := by
  exact vfMidAlignedIntegerBacklog_eq_direct_error_phase
    vfMidSqrtTwoVerticalPhase R

/-- All successive sqrt(2) rounding errors telescope. They cannot be
reinterpreted as an arithmetic prime-owner payment. -/
theorem vfMidSqrtTwoIntegerBacklog_interval
    (A B : ℕ) :
    ((vfMidSqrtTwoIntegerLevel B : ℝ) -
        (Nat.primeCounting (B ^ 2) : ℝ)) -
      ((vfMidSqrtTwoIntegerLevel A : ℝ) -
        (Nat.primeCounting (A ^ 2) : ℝ)) =
      -(vfMidDirectSquareEndpointError B -
          vfMidDirectSquareEndpointError A) -
        (vfMidAlignedRoundingPhase vfMidSqrtTwoVerticalPhase B -
          vfMidAlignedRoundingPhase vfMidSqrtTwoVerticalPhase A) := by
  exact vfMidAlignedIntegerBacklog_interval_eq_direct_error_phase
    vfMidSqrtTwoVerticalPhase A B

/-! ## Proven PNT: the legitimate macroscopic horizontal information -/

/-- The genuine square-root clock tends to infinity. -/
theorem vfMidSqrtTwoSquareClock_tendsto_atTop :
    Tendsto (fun R : ℕ => R ^ 2) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (max b 1)] with R hR
  have hR1 : 1 ≤ R := (Nat.le_max_right b 1).trans hR
  have hb : b ≤ R := (Nat.le_max_left b 1).trans hR
  nlinarith

/-- The already PROVED native PNT restricted to actual prime counts
at the integer square endpoints. It is not an axiom and says nothing
at the scale of the single block width 2R+1. -/
theorem vfMidSqrtTwoActualPrimeSquarePNT :
    Tendsto
      (fun R : ℕ =>
        (Nat.primeCounting (R ^ 2) : ℝ) *
          Real.log ((R ^ 2 : ℕ) : ℝ) / ((R ^ 2 : ℕ) : ℝ))
      atTop (𝓝 1) := by
  simpa only [Function.comp_apply] using
    nativePrimeNumberTheorem.comp vfMidSqrtTwoSquareClock_tendsto_atTop

/-- PNT supplies arbitrary *fixed percentage* accuracy at square endpoints,
not an RH-scale bound and not prime supply in every individual square block. -/
theorem vfMidSqrtTwoActualPrimeSquarePNT_percent
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ R : ℕ in atTop,
      |((Nat.primeCounting (R ^ 2) : ℝ) *
        Real.log ((R ^ 2 : ℕ) : ℝ) /
          ((R ^ 2 : ℕ) : ℝ)) - 1| < ε := by
  have hl := (tendsto_order.1 vfMidSqrtTwoActualPrimeSquarePNT).1
    (1 - ε) (by linarith)
  have hr := (tendsto_order.1 vfMidSqrtTwoActualPrimeSquarePNT).2
    (1 + ε) (by linarith)
  filter_upwards [hl, hr] with R hlow hhigh
  rw [abs_lt]
  constructor <;> linarith

/-- Precise interface from PNT and the elementary VF main-term
asymptotic to a *relative* horizontal/height matching statement.
The VF input is intentionally EXPLICIT: PNT is about the primes;
it does not itself prove the VF quadrature asymptotic.
The conclusion is o(R^2/log(R^2)), not O(R log R). -/
theorem vfMidSqrtTwoRelativeHeightAlignment_of_VF_mainTerm
    (hVF :
      Tendsto
        (fun R : ℕ =>
          vfMidAlignedMass vfMidSqrtTwoVerticalPhase R *
            Real.log ((R ^ 2 : ℕ) : ℝ) / ((R ^ 2 : ℕ) : ℝ))
        atTop (𝓝 1)) :
    Tendsto
      (fun R : ℕ =>
        (vfMidAlignedMass vfMidSqrtTwoVerticalPhase R -
          (Nat.primeCounting (R ^ 2) : ℝ)) *
            Real.log ((R ^ 2 : ℕ) : ℝ) / ((R ^ 2 : ℕ) : ℝ))
      atTop (𝓝 0) := by
  have hdiff := hVF.sub vfMidSqrtTwoActualPrimeSquarePNT
  have heq :
      (fun R : ℕ =>
        (vfMidAlignedMass vfMidSqrtTwoVerticalPhase R -
          (Nat.primeCounting (R ^ 2) : ℝ)) *
            Real.log ((R ^ 2 : ℕ) : ℝ) / ((R ^ 2 : ℕ) : ℝ)) =
      (fun R : ℕ =>
        vfMidAlignedMass vfMidSqrtTwoVerticalPhase R *
          Real.log ((R ^ 2 : ℕ) : ℝ) / ((R ^ 2 : ℕ) : ℝ) -
        (Nat.primeCounting (R ^ 2) : ℝ) *
          Real.log ((R ^ 2 : ℕ) : ℝ) / ((R ^ 2 : ℕ) : ℝ)) := by
    funext R
    ring
  rw [heq]
  simpa only [sub_self] using hdiff

end RHLean.Analysis
