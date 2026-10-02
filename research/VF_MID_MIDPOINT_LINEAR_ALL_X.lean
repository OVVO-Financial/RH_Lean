import Mathlib
import «research.VF_MID_VON_KOCH_BRIDGE»

/-!
# Midpoint-to-midpoint linear extension of VF

The square-block VF construction supplies a canonical cumulative value at the
geometric midpoint of every block.  If

  F_R = sum_{r < R} V_r

is the completed mass before block R and V_R is the R-th midpoint band mass,
the midpoint anchor is

  A_R = F_R + V_R / 2.

This file connects consecutive anchors (m_R,A_R) and (m_{R+1},A_{R+1}) by an
affine segment.  It therefore gives a literal midpoint-to-midpoint piecewise
linear VF path on all real x (with the already-defined vfMid used only as a
finite initial seed below the first midpoint).

This is a deterministic interpolation layer.  It introduces no arithmetic
hypothesis about actual primes.
-/

noncomputable section

namespace RHLean.Analysis

/-- Cumulative VF value attached to the geometric midpoint of block R. -/
def vfMidMidpointAnchor (R : ℕ) : ℝ :=
  vfMidFinishedMass R + vfMidBandMass R / 2

/-- Consecutive geometric square-band midpoints are separated by exactly
2R+2. -/
theorem vfMidBandMidpoint_succ_sub (R : ℕ) :
    vfMidBandMidpoint (R + 1) - vfMidBandMidpoint R =
      2 * (R : ℝ) + 2 := by
  unfold vfMidBandMidpoint
  push_cast
  ring

/-- The midpoint spacing is strictly positive. -/
theorem vfMidBandMidpoint_succ_sub_pos (R : ℕ) :
    0 < vfMidBandMidpoint (R + 1) - vfMidBandMidpoint R := by
  rw [vfMidBandMidpoint_succ_sub]
  positivity

/-- Advancing one midpoint adds half the old band and half the new band. -/
theorem vfMidMidpointAnchor_succ
    {R : ℕ} (hR : 2 ≤ R) :
    vfMidMidpointAnchor (R + 1) =
      vfMidMidpointAnchor R +
        (vfMidBandMass R + vfMidBandMass (R + 1)) / 2 := by
  unfold vfMidMidpointAnchor
  rw [vfMidFinishedMass_succ hR]
  ring

/-- Affine interpolation between two consecutive VF midpoint anchors. -/
def vfMidMidpointLinearSegment (R : ℕ) (x : ℝ) : ℝ :=
  vfMidMidpointAnchor R +
    (x - vfMidBandMidpoint R) /
        (vfMidBandMidpoint (R + 1) - vfMidBandMidpoint R) *
      (vfMidMidpointAnchor (R + 1) - vfMidMidpointAnchor R)

/-- The affine segment starts at the R-th midpoint anchor. -/
@[simp] theorem vfMidMidpointLinearSegment_left (R : ℕ) :
    vfMidMidpointLinearSegment R (vfMidBandMidpoint R) =
      vfMidMidpointAnchor R := by
  simp [vfMidMidpointLinearSegment]

/-- The affine segment ends at the next midpoint anchor. -/
@[simp] theorem vfMidMidpointLinearSegment_right (R : ℕ) :
    vfMidMidpointLinearSegment R (vfMidBandMidpoint (R + 1)) =
      vfMidMidpointAnchor (R + 1) := by
  unfold vfMidMidpointLinearSegment
  have hne :
      vfMidBandMidpoint (R + 1) - vfMidBandMidpoint R ≠ 0 :=
    ne_of_gt (vfMidBandMidpoint_succ_sub_pos R)
  field_simp [hne]
  ring

/-- Adjacent affine pieces glue exactly at every midpoint. -/
theorem vfMidMidpointLinearSegment_glue (R : ℕ) :
    vfMidMidpointLinearSegment R (vfMidBandMidpoint (R + 1)) =
      vfMidMidpointLinearSegment (R + 1)
        (vfMidBandMidpoint (R + 1)) := by
  simp

/-- Literal all-real midpoint-linear VF extension.

Below the first nontrivial midpoint m_2 the existing continuous vfMid path is
used as a finite seed.  Thereafter, if R=floor(sqrt x), points before m_R lie
on the segment from m_{R-1} to m_R and points at or after m_R lie on the
segment from m_R to m_{R+1}. -/
def vfMidMidpointLinear (x : ℝ) : ℝ :=
  if x < vfMidBandMidpoint 2 then
    vfMid x
  else
    let R := vfMidSquareRootIndex x
    if x < vfMidBandMidpoint R then
      vfMidMidpointLinearSegment (R - 1) x
    else
      vfMidMidpointLinearSegment R x

/-- The finite initial seed agrees literally with the existing vfMid path. -/
theorem vfMidMidpointLinear_eq_vfMid_of_lt_firstMidpoint
    {x : ℝ} (hx : x < vfMidBandMidpoint 2) :
    vfMidMidpointLinear x = vfMid x := by
  simp [vfMidMidpointLinear, hx]

/-- Above the first midpoint, the global path selects the left adjacent
midpoint segment whenever x lies before its current square-block midpoint. -/
theorem vfMidMidpointLinear_eq_leftSegment
    {x : ℝ} (hx0 : vfMidBandMidpoint 2 ≤ x)
    (hx : x < vfMidBandMidpoint (vfMidSquareRootIndex x)) :
    vfMidMidpointLinear x =
      vfMidMidpointLinearSegment (vfMidSquareRootIndex x - 1) x := by
  simp [vfMidMidpointLinear, not_lt.mpr hx0, hx]

/-- Above the first midpoint, the global path selects the right adjacent
midpoint segment at or after the current square-block midpoint. -/
theorem vfMidMidpointLinear_eq_rightSegment
    {x : ℝ} (hx0 : vfMidBandMidpoint 2 ≤ x)
    (hx : vfMidBandMidpoint (vfMidSquareRootIndex x) ≤ x) :
    vfMidMidpointLinear x =
      vfMidMidpointLinearSegment (vfMidSquareRootIndex x) x := by
  simp [vfMidMidpointLinear, not_lt.mpr hx0, not_lt.mpr hx]

/-- Prime-count discrepancy against the literal midpoint-linear VF path. -/
def vfMidMidpointLinearPrimeError (x : ℝ) : ℝ :=
  vfMidPrimeCount x - vfMidMidpointLinear x

/-- The all-x von-Koch target written directly against the midpoint-linear
presentation. -/
def VFMidMidpointLinearVonKochBoundedStatement : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ x : ℝ, 4 ≤ x →
      |vfMidMidpointLinearPrimeError x| ≤
        C * Real.sqrt x * Real.log x

end RHLean.Analysis
