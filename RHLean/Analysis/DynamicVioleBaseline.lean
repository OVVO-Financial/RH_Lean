import Mathlib
import RHLean.Proof.SquareBlockTransportBaseline

/-!
# Dynamic-denominator Viole baseline

This module formalizes the square-index dynamic Viole baseline tested in
`experiments/vf_dynamic_e_asymptote_test.py`.

The corrected architecture uses the square-block index `r` inside the Euler
convergence term:

```text
log b(r) = 1 + a / log r + b / (log r)^2,
a = 5.5872416013500885,
b = -18.957724430717928.
```

Thus the effective base satisfies `b(r) -> e`. The main denominator still uses
`log(r^2)`, while the correction is formed from `log_b(r)`.

The coefficients below are represented as exact rationals. They were fitted on
square-block midpoints from `10^3` through `10^5` and frozen before testing
through `10^8`.

This file formalizes only the deterministic function and its exact insertion
into the existing arbitrary-baseline decomposition. It does not assert any
prime-counting error estimate, asymptotic superiority over `li`, or RH
implication.
-/

noncomputable section

namespace RHLean.Proof

/-- Fitted coefficient of `1 / log r` in the square-index dynamic logarithmic
base exponent. -/
def dynamicVioleFitA : ℝ :=
  55872416013500885 / 10000000000000000

/-- Fitted coefficient of `1 / (log r)^2` in the square-index dynamic
logarithmic-base exponent. -/
def dynamicVioleFitB : ℝ :=
  -(18957724430717928 / 1000000000000000)

/-- The fitted value of `log b(r)`. The leading constant `1` encodes the
intended asymptotic base `e`. -/
def dynamicVioleLogBaseExponent (r : ℝ) : ℝ :=
  1 + dynamicVioleFitA / Real.log r +
    dynamicVioleFitB / (Real.log r) ^ 2

/-- The corresponding positive formal base `b(r) = exp(log b(r))`. -/
def dynamicVioleLogBase (r : ℝ) : ℝ :=
  Real.exp (dynamicVioleLogBaseExponent r)

/-- Dynamic Euler correction using the square-block index `r`.
Writing `R = log r` and `s = log b(r)`, this is

`(1 + R / s) * log (1 + s / R)`,

the logarithm of `(1 + 1 / log_b r)^(1 + log_b r)`. -/
def dynamicVioleCorrection (r : ℕ) : ℝ :=
  let R := Real.log (r : ℝ)
  let s := dynamicVioleLogBaseExponent (r : ℝ)
  (1 + R / s) * Real.log (1 + s / R)

/-- Square-block midpoint `r^2 + r + 1/2`. -/
def dynamicVioleSquareMidpoint (r : ℕ) : ℝ :=
  ((r ^ 2 : ℕ) : ℝ) + (r : ℝ) + 1 / 2

/-- The original square-block numerator `r^2`. -/
def dynamicVioleSquareNumerator (r : ℕ) : ℝ :=
  ((r ^ 2 : ℕ) : ℝ)

/-- Dynamic Viole denominator at square-block index `r`. The main logarithm is
`log(r^2)` while the correction uses `log_b(r)`. -/
def dynamicVioleDenominator (r : ℕ) : ℝ :=
  Real.log (dynamicVioleSquareNumerator r) - dynamicVioleCorrection r

/-- Dynamic Viole anchor attached to the midpoint of square block `r`. -/
def dynamicVioleAnchor (r : ℕ) : ℝ :=
  dynamicVioleSquareNumerator r / dynamicVioleDenominator r

/-- Distance between consecutive square-block midpoint nodes. -/
theorem dynamicVioleSquareMidpoint_succ_sub (r : ℕ) :
    dynamicVioleSquareMidpoint (r + 1) - dynamicVioleSquareMidpoint r =
      2 * (r : ℝ) + 2 := by
  unfold dynamicVioleSquareMidpoint
  push_cast
  ring

/-- Linear interpolation of the dynamic Viole anchors on the segment from the
`r`th square midpoint to the next midpoint. -/
def dynamicVioleLinearSegment (r : ℕ) (x : ℝ) : ℝ :=
  dynamicVioleAnchor r +
    ((x - dynamicVioleSquareMidpoint r) / (2 * (r : ℝ) + 2)) *
      (dynamicVioleAnchor (r + 1) - dynamicVioleAnchor r)

@[simp] theorem dynamicVioleLinearSegment_left (r : ℕ) :
    dynamicVioleLinearSegment r (dynamicVioleSquareMidpoint r) =
      dynamicVioleAnchor r := by
  simp [dynamicVioleLinearSegment]

@[simp] theorem dynamicVioleLinearSegment_right (r : ℕ) :
    dynamicVioleLinearSegment r (dynamicVioleSquareMidpoint (r + 1)) =
      dynamicVioleAnchor (r + 1) := by
  have h : (2 * (r : ℝ) + 2) ≠ 0 := by positivity
  simp [dynamicVioleLinearSegment, dynamicVioleSquareMidpoint_succ_sub, h]

/-- Index of the midpoint segment containing a nonnegative real coordinate. -/
def dynamicVioleMidpointIndex (x : ℝ) : ℕ :=
  Nat.floor ((Real.sqrt (4 * x - 1) - 1) / 2)

/-- Continuous piecewise-linear dynamic Viole baseline through midpoint
anchors. -/
def dynamicVioleBaselineReal (x : ℝ) : ℝ :=
  dynamicVioleLinearSegment (dynamicVioleMidpointIndex x) x

/-- Complex-valued wrapper required by the generic square-block transport API. -/
def dynamicVioleBaseline (x : ℝ) : ℂ :=
  (dynamicVioleBaselineReal x : ℂ)

/-- Exact specialization of the arbitrary-baseline decomposition to the
square-index dynamic Viole baseline. -/
theorem squarePrefixMertens_eq_dynamicVioleMain_sub_error (n : ℕ) :
    RHLean.Analysis.squarePrefixMertens n =
      squareBlockBaselineMainPrefix dynamicVioleBaseline n -
        squareBlockBaselineTransportErrorPrefix dynamicVioleBaseline n := by
  exact squarePrefixMertens_eq_baselineMain_sub_error dynamicVioleBaseline n

end RHLean.Proof
