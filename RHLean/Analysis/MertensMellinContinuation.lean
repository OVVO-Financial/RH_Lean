import Mathlib
import RHLean.Analysis.MertensStepAsymptotics

/-!
# Mellin continuation from Mertens energy growth

The Mertens floor-step function vanishes on a neighbourhood of zero and, under
`MertensEnergyBoundedStatement`, is `O(t^r)` at infinity for every
`r > 1/2`.  Mathlib's Mellin differentiability theorem therefore applies to
`mellin mertensStep` throughout the half-plane `Re z < -1/2`.

After the change of variable `z = -s`, the Abel/Mellin continuation

`F(s) = s * mellin mertensStep (-s)`

is holomorphic on `Re s > 1/2`.  This is the analytic continuation object that
will later be identified with the Möbius Dirichlet series on `Re s > 1`.
-/

noncomputable section

namespace RHLean.Analysis

open Filter Set Asymptotics MeasureTheory

/-- Because the Mertens step function is identically zero for `t < 1`, it has
arbitrary power growth at zero. -/
theorem mertensStep_isBigO_rpow_nhdsGT_zero (b : ℝ) :
    mertensStep =O[𝓝[>] (0 : ℝ)] fun t : ℝ => t ^ (-b) := by
  refine IsBigO.of_bound 0 ?_
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1)] with t ht hpos
  rw [mertensStep_eq_zero_of_lt_one ht]
  simp

/-- Under the Mertens energy criterion, the Mellin transform of the step
function is holomorphic throughout `Re z < -1/2`. -/
theorem mellin_mertensStep_differentiableAt_of_energy
    (hM : MertensEnergyBoundedStatement) {z : ℂ}
    (hz : z.re < -(1 : ℝ) / 2) :
    DifferentiableAt ℂ (mellin mertensStep) z := by
  let r : ℝ := ((1 : ℝ) / 2 + (-z.re)) / 2
  have hr : (1 : ℝ) / 2 < r := by
    dsimp [r]
    linarith
  have hrz : r < -z.re := by
    dsimp [r]
    linarith
  have htop0 := mertensStep_isBigO_rpow_atTop_of_energy hM hr
  have htop :
      mertensStep =O[atTop] fun t : ℝ => t ^ (-(-r)) := by
    simpa using htop0
  let b : ℝ := z.re - 1
  have hbot := mertensStep_isBigO_rpow_nhdsGT_zero b
  apply mellin_differentiableAt_of_isBigO_rpow
    mertensStep_locallyIntegrableOn htop
  · linarith
  · exact hbot
  · dsimp [b]
    linarith

/-- Abel/Mellin continuation of the ordered Möbius Dirichlet series. -/
def mertensDirichletContinuation (s : ℂ) : ℂ :=
  s * mellin mertensStep (-s)

/-- The continuation is holomorphic at every point with real part strictly
greater than one half. -/
theorem mertensDirichletContinuation_differentiableAt_of_energy
    (hM : MertensEnergyBoundedStatement) {s : ℂ}
    (hs : (1 : ℝ) / 2 < s.re) :
    DifferentiableAt ℂ mertensDirichletContinuation s := by
  have hm : DifferentiableAt ℂ (mellin mertensStep) (-s) := by
    apply mellin_mertensStep_differentiableAt_of_energy hM
    simp only [neg_re]
    linarith
  have hneg : DifferentiableAt ℂ (fun z : ℂ => -z) s :=
    differentiableAt_id.neg
  have hcomp :
      DifferentiableAt ℂ (fun z : ℂ => mellin mertensStep (-z)) s := by
    simpa [Function.comp_def] using hm.comp s hneg
  unfold mertensDirichletContinuation
  exact differentiableAt_id.mul hcomp

end RHLean.Analysis
