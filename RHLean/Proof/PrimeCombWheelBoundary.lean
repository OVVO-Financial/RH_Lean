import Mathlib
import RHLean.Proof.PrimeCombDiscrepancyRecurrence

/-!
# Complete-wheel and boundary decomposition for prime-comb updates

A finite square block is an arbitrary interval relative to any fixed prime wheel.
For a wheel of period `Q`, the block decomposes into complete `Q`-cells together
with at most two incomplete fragments.  The complete cells carry the exact
prime-comb update law.  Every failure of exact wheel proportions is confined to
the incomplete boundary.

This module formalizes that reduction abstractly.  It does not assert the final
arithmetic estimate on the complete-wheel restoring term.
-/

noncomputable section

namespace RHLean.Proof

/-- Signed state carried by an incomplete wheel boundary before and after one
prime-comb update. -/
structure PrimeCombBoundaryState where
  before : ℤ
  after : ℤ
  length : ℕ
  beforeBound : |before| ≤ (length : ℤ)
  afterBound : |after| ≤ (length : ℤ)

/-- The boundary update itself can change the signed discrepancy by at most twice
its number of coordinates. -/
theorem PrimeCombBoundaryState.abs_increment_le_two_mul_length
    (b : PrimeCombBoundaryState) :
    |b.after - b.before| ≤ 2 * (b.length : ℤ) := by
  calc
    |b.after - b.before| ≤ |b.after| + |b.before| := by
      simpa [sub_eq_add_neg] using abs_add b.after (-b.before)
    _ ≤ (b.length : ℤ) + (b.length : ℤ) :=
      add_le_add b.afterBound b.beforeBound
    _ = 2 * (b.length : ℤ) := by ring

/-- Exact splitting of a total prime-comb update into complete-wheel and
incomplete-boundary contributions. -/
structure PrimeCombWheelSplit where
  total : PrimeCombUpdate
  complete : PrimeCombUpdate
  boundary : PrimeCombBoundaryState
  beforeSplit : total.before = complete.before + boundary.before
  afterSplit : total.after = complete.after + boundary.after

/-- Exact increment decomposition: total change equals complete-wheel change plus
boundary change. -/
theorem PrimeCombWheelSplit.increment_eq_complete_add_boundary
    (s : PrimeCombWheelSplit) :
    s.total.after - s.total.before =
      (s.complete.after - s.complete.before) +
      (s.boundary.after - s.boundary.before) := by
  rw [s.beforeSplit, s.afterSplit]
  ring

/-- The total prime-comb increment differs from the complete-wheel increment by
at most twice the incomplete boundary length. -/
theorem PrimeCombWheelSplit.abs_increment_sub_complete_le_boundary
    (s : PrimeCombWheelSplit) :
    |(s.total.after - s.total.before) -
      (s.complete.after - s.complete.before)| ≤
      2 * (s.boundary.length : ℤ) := by
  rw [s.increment_eq_complete_add_boundary]
  ring_nf
  exact s.boundary.abs_increment_le_two_mul_length

/-- Pointwise discrepancy bound: the total post-update discrepancy is the
complete-wheel post-update discrepancy plus a boundary term of size at most the
boundary length. -/
theorem PrimeCombWheelSplit.abs_total_after_le_complete_add_boundary
    (s : PrimeCombWheelSplit) :
    |s.total.after| ≤ |s.complete.after| + (s.boundary.length : ℤ) := by
  rw [s.afterSplit]
  exact (abs_add _ _).trans (add_le_add_left s.boundary.afterBound _)

/-- A two-fragment boundary around complete wheel cells. -/
structure TwoFragmentWheelBoundary where
  period : ℕ
  leftLength : ℕ
  rightLength : ℕ
  left_lt : leftLength < period
  right_lt : rightLength < period

/-- Total incomplete boundary length. -/
def TwoFragmentWheelBoundary.length (b : TwoFragmentWheelBoundary) : ℕ :=
  b.leftLength + b.rightLength

/-- Any arbitrary interval cuts fewer than two full wheel periods at its two
ends. -/
theorem TwoFragmentWheelBoundary.length_lt_two_mul_period
    (b : TwoFragmentWheelBoundary) :
    b.length < 2 * b.period := by
  unfold TwoFragmentWheelBoundary.length
  omega

/-- Integer form of the arbitrary-cutoff boundary estimate. -/
theorem TwoFragmentWheelBoundary.int_length_le_two_mul_period
    (b : TwoFragmentWheelBoundary) :
    (b.length : ℤ) ≤ 2 * (b.period : ℤ) := by
  exact_mod_cast (Nat.le_of_lt b.length_lt_two_mul_period)

/-- Combining the complete-wheel split with an arbitrary two-fragment cutoff:
the total post-update discrepancy is controlled by the complete-wheel value plus
at most two wheel periods. -/
theorem PrimeCombWheelSplit.abs_total_after_le_complete_add_two_periods
    (s : PrimeCombWheelSplit) (b : TwoFragmentWheelBoundary)
    (hlen : s.boundary.length = b.length) :
    |s.total.after| ≤ |s.complete.after| + 2 * (b.period : ℤ) := by
  have hmain := s.abs_total_after_le_complete_add_boundary
  rw [hlen] at hmain
  exact hmain.trans (add_le_add_left b.int_length_le_two_mul_period _)

/-- If every complete wheel has zero post-update discrepancy, an arbitrary block
is supported entirely on its incomplete wheel boundary. -/
theorem PrimeCombWheelSplit.abs_total_after_le_two_periods_of_complete_zero
    (s : PrimeCombWheelSplit) (b : TwoFragmentWheelBoundary)
    (hlen : s.boundary.length = b.length)
    (hcomplete : s.complete.after = 0) :
    |s.total.after| ≤ 2 * (b.period : ℤ) := by
  have h := s.abs_total_after_le_complete_add_two_periods b hlen
  simpa [hcomplete] using h

end RHLean.Proof
