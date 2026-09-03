import Mathlib
import RHLean.Analysis.PrimeSieveStateDependentSelbergScalePersistence
import RHLean.Proof.SquareBlockTransportBaseline

/-!
# Dynamic-denominator Viole baseline

This module formalizes the square-block prime-counting baseline tested in
`experiments/vf_dynamic_e_asymptote_test.py`.

The original Viole function used one fixed logarithmic-base convergence rate.
The corrected empirical study replaces that fixed rate by

```text
log b(x) = 1 + a / log x + b / (log x)^2,
a = 40.64408021414064,
b = -233.433772115277.
```

The leading constant is `1`, so the effective base satisfies `b(x) -> e` as
`x -> infinity`. The coefficients below are represented as exact rationals.
They were fitted on square-block midpoints from `10^3` through `10^5` and then
frozen before testing through `10^8`.

This file formalizes only the deterministic function and its exact insertion
into the existing arbitrary-baseline decomposition. It does not assert any
prime-counting error estimate, asymptotic superiority over `li`, or RH
implication.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

/-- Fitted coefficient of `1 / log x` in the corrected dynamic logarithmic-base
exponent. The full fitted decimal `40.64408021414064` is stored exactly. -/
def dynamicVioleFitA : ℝ :=
  4064408021414064 / 100000000000000

/-- Fitted coefficient of `1 / (log x)^2` in the corrected dynamic
logarithmic-base exponent. The full fitted decimal `-233.433772115277` is
stored exactly. -/
def dynamicVioleFitB : ℝ :=
  -(233433772115277 / 1000000000000)

/-- The fitted value of `log b(x)`, where `b(x)` is the effective logarithmic
base used by the dynamic Viole denominator. The leading constant `1` encodes
the intended asymptotic base `e`. -/
def dynamicVioleLogBaseExponent (x : ℝ) : ℝ :=
  1 + dynamicVioleFitA / Real.log x +
    dynamicVioleFitB / (Real.log x) ^ 2

/-- The corresponding positive formal base `b(x) = exp(log b(x))`.
Positivity follows from `Real.exp_pos`; no claim is made here that the fitted
exponent itself is positive on every real input. -/
def dynamicVioleLogBase (x : ℝ) : ℝ :=
  Real.exp (dynamicVioleLogBaseExponent x)

/-- Dynamic replacement for the original fixed-base convergence correction.
Writing `L = log x` and `s = log b(x)`, this is

`(1 + L / s) * log (1 + s / L)`,

the logarithm of `(1 + 1 / log_b x)^(1 + log_b x)`. -/
def dynamicVioleCorrection (x : ℝ) : ℝ :=
  let L := Real.log x
  let s := dynamicVioleLogBaseExponent x
  (1 + L / s) * Real.log (1 + s / L)

/-- Square-block midpoint `r^2 + r + 1/2`. -/
def dynamicVioleSquareMidpoint (r : ℕ) : ℝ :=
  ((r ^ 2 : ℕ) : ℝ) + (r : ℝ) + 1 / 2

/-- The original square-block numerator `r^2`. -/
def dynamicVioleSquareNumerator (r : ℕ) : ℝ :=
  ((r ^ 2 : ℕ) : ℝ)

/-- Dynamic Viole denominator at the midpoint of square block `r`.
This is the exact denominator used by the empirically selected model. -/
def dynamicVioleDenominator (r : ℕ) : ℝ :=
  Real.log (dynamicVioleSquareNumerator r) -
    dynamicVioleCorrection (dynamicVioleSquareMidpoint r)

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

/-- Index of the midpoint segment containing a nonnegative real coordinate.
The closed-form inversion comes from solving `r^2 + r + 1/2 ≤ x` for `r`.
For inputs below the first meaningful prime-counting block, natural flooring
provides the harmless fallback index `0`. -/
def dynamicVioleMidpointIndex (x : ℝ) : ℕ :=
  Nat.floor ((Real.sqrt (4 * x - 1) - 1) / 2)

/-- Continuous piecewise-linear dynamic Viole baseline through the midpoint
anchors. This is the cumulative real-valued baseline used in the exact-activity
interval experiment. -/
def dynamicVioleBaselineReal (x : ℝ) : ℝ :=
  dynamicVioleLinearSegment (dynamicVioleMidpointIndex x) x

/-- Complex-valued wrapper required by the generic square-block transport
baseline API. -/
def dynamicVioleBaseline (x : ℝ) : ℂ :=
  (dynamicVioleBaselineReal x : ℂ)

/-- Exact specialization of the existing arbitrary-baseline decomposition to
the corrected dynamic Viole baseline. This is algebraic and imports no
empirical error claim. -/
theorem squarePrefixMertens_eq_dynamicVioleMain_sub_error (n : ℕ) :
    RHLean.Analysis.squarePrefixMertens n =
      squareBlockBaselineMainPrefix dynamicVioleBaseline n -
        squareBlockBaselineTransportErrorPrefix dynamicVioleBaseline n := by
  exact squarePrefixMertens_eq_baselineMain_sub_error dynamicVioleBaseline n

end RHLean.Proof

namespace RHLean.Analysis

open RHLean.Proof

/-! ## Reciprocal-square coupling to the square clock -/

/-- The remaining local arithmetic seam for the Viole-clock route.

The left-hand state is deliberately the pure tail predicate: there is no
affine intercept and no globalization through a finite prefix.  The square
cutoff at stage `r` is the already-compiled floor `r^2 + r`, and the gain is
measured directly against the increment of `dynamicVioleAnchor`.

A proof of this proposition must therefore produce the new tail slope from the
signed arithmetic born in the single square block `r`; consumers may telescope
the resulting reciprocal-square gains, but cannot manufacture them. -/
def VioleClockReciprocalSquareCoupling
    (r0 : Nat) (c : Real) (eps : Nat → Real) : Prop :=
  2 ≤ r0 ∧ 0 < c ∧
  ∀ (r : Nat) (alpha : Real),
    r0 ≤ r →
    PrimeSieveStateDependentSelbergTailAbove (r ^ 2 + r) alpha →
    ∃ alpha' : Real,
      PrimeSieveStateDependentSelbergTailAbove
        ((r + 1) ^ 2 + (r + 1)) alpha' ∧
      alpha' ≤ alpha ∧
      c * (dynamicVioleAnchor (r + 1) - dynamicVioleAnchor r) - eps r
        ≤ 1 / alpha' ^ 2 - 1 / alpha ^ 2

/-- Projection of the frozen coupling to one admissible square block. -/
theorem violeClockReciprocalSquareCoupling_step
    {r0 : Nat} {c : Real} {eps : Nat → Real}
    (h : VioleClockReciprocalSquareCoupling r0 c eps)
    (r : Nat) (alpha : Real) (hr : r0 ≤ r)
    (htail : PrimeSieveStateDependentSelbergTailAbove (r ^ 2 + r) alpha) :
    ∃ alpha' : Real,
      PrimeSieveStateDependentSelbergTailAbove
        ((r + 1) ^ 2 + (r + 1)) alpha' ∧
      alpha' ≤ alpha ∧
      c * (dynamicVioleAnchor (r + 1) - dynamicVioleAnchor r) - eps r
        ≤ 1 / alpha' ^ 2 - 1 / alpha ^ 2 :=
  h.2.2 r alpha hr htail

private theorem violeClock_sum_increment_Ico
    (f : Nat → Real) {a b : Nat} (hab : a ≤ b) :
    (∑ k ∈ Finset.Ico a b, (f (k + 1) - f k)) = f b - f a := by
  rw [Finset.sum_Ico_eq_sub _ hab, Finset.sum_range_sub f b,
    Finset.sum_range_sub f a]
  abel

/-- Deterministic consumption of any selected slope chain: the local
reciprocal-square gains telescope exactly against the same Viole clock. -/
theorem violeClockReciprocalSquare_telescope
    (r0 R : Nat) (c : Real) (eps : Nat → Real) (a : Nat → Real)
    (hR : r0 ≤ R)
    (hstep : ∀ r : Nat, r ∈ Finset.Ico r0 R →
      c * (dynamicVioleAnchor (r + 1) - dynamicVioleAnchor r) - eps r
        ≤ 1 / (a (r + 1)) ^ 2 - 1 / (a r) ^ 2) :
    c * (dynamicVioleAnchor R - dynamicVioleAnchor r0) -
        ∑ r ∈ Finset.Ico r0 R, eps r
      ≤ 1 / (a R) ^ 2 - 1 / (a r0) ^ 2 := by
  have hsum :
      (∑ r ∈ Finset.Ico r0 R,
        (c * (dynamicVioleAnchor (r + 1) - dynamicVioleAnchor r) - eps r))
        ≤
      ∑ r ∈ Finset.Ico r0 R,
        (1 / (a (r + 1)) ^ 2 - 1 / (a r) ^ 2) := by
    exact Finset.sum_le_sum (fun r hr => hstep r hr)
  have hV :=
    violeClock_sum_increment_Ico dynamicVioleAnchor hR
  have hA :=
    violeClock_sum_increment_Ico (fun r => 1 / (a r) ^ 2) hR
  calc
    c * (dynamicVioleAnchor R - dynamicVioleAnchor r0) -
          ∑ r ∈ Finset.Ico r0 R, eps r
        = c * (∑ r ∈ Finset.Ico r0 R,
            (dynamicVioleAnchor (r + 1) - dynamicVioleAnchor r)) -
            ∑ r ∈ Finset.Ico r0 R, eps r := by rw [hV]
    _ = ∑ r ∈ Finset.Ico r0 R,
          (c * (dynamicVioleAnchor (r + 1) - dynamicVioleAnchor r) - eps r) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    _ ≤ ∑ r ∈ Finset.Ico r0 R,
          (1 / (a (r + 1)) ^ 2 - 1 / (a r) ^ 2) := hsum
    _ = 1 / (a R) ^ 2 - 1 / (a r0) ^ 2 := hA

/-- If cumulative leakage costs at most half the clock, the selected slope
chain retains at least half of the reciprocal-square clock gain. -/
theorem violeClockReciprocalSquare_of_half_leakage
    (r0 R : Nat) (c : Real) (eps : Nat → Real) (a : Nat → Real)
    (hR : r0 ≤ R)
    (hstep : ∀ r : Nat, r ∈ Finset.Ico r0 R →
      c * (dynamicVioleAnchor (r + 1) - dynamicVioleAnchor r) - eps r
        ≤ 1 / (a (r + 1)) ^ 2 - 1 / (a r) ^ 2)
    (hleak :
      (∑ r ∈ Finset.Ico r0 R, eps r) ≤
        (c / 2) * (dynamicVioleAnchor R - dynamicVioleAnchor r0)) :
    1 / (a r0) ^ 2 +
        (c / 2) * (dynamicVioleAnchor R - dynamicVioleAnchor r0)
      ≤ 1 / (a R) ^ 2 := by
  have htel :=
    violeClockReciprocalSquare_telescope r0 R c eps a hR hstep
  nlinarith

end RHLean.Analysis
