import Mathlib

/-!
# General primorial-wheel cancellation

The arithmetic mechanism behind the `2,3,5,7` wheel does not depend on the
particular odd primes.  Let `Q` be the product of any finite collection of odd
prime moduli.  After the prime-`2` coordinate is added, the full wheel has
period `2Q`.  Its second `Q`-cell is the sign-reversed copy of its first
`Q`-cell.  Consequently every complete `2Q`-cell has exact signed mass zero.

The statements below isolate this mechanism abstractly.  A later bridge may
instantiate `f` with the actual progressive first-cover sign assignment.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Arithmetic

/-- A sign pattern on a cell of length `2 * Q` has the primorial half-reversal
property when its second half is the pointwise negative of its first half. -/
def HasWheelHalfReversal (Q : ℕ) (f : ℕ → ℤ) : Prop :=
  ∀ r < Q, f (Q + r) = -f r

/-- Exact cancellation of any complete wheel cell whose second half is the
negative of its first half. -/
theorem sum_two_mul_cell_eq_zero_of_halfReversal
    (Q : ℕ) (f : ℕ → ℤ)
    (hrev : HasWheelHalfReversal Q f) :
    ∑ r ∈ Finset.range (2 * Q), f r = 0 := by
  have htwo : 2 * Q = Q + Q := by omega
  rw [htwo, Finset.sum_range_add]
  have hsecond :
      (∑ r ∈ Finset.range Q, f (Q + r)) =
        -(∑ r ∈ Finset.range Q, f r) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    exact hrev r (Finset.mem_range.mp hr)
  rw [hsecond]
  ring

/-- A wheel pattern is periodic with period `P`. -/
def HasWheelPeriod (P : ℕ) (f : ℕ → ℤ) : Prop :=
  ∀ n, f (n + P) = f n

/-- Iterating a one-period identity gives invariance under any whole number of
periods. -/
theorem wheel_period_mul
    {P : ℕ} {f : ℕ → ℤ}
    (hperiod : HasWheelPeriod P f) :
    ∀ q n : ℕ, f (q * P + n) = f n := by
  intro q
  induction q with
  | zero =>
      intro n
      simp
  | succ q ih =>
      intro n
      have hstep := hperiod (q * P + n)
      rw [Nat.succ_mul, Nat.add_assoc] at hstep
      calc
        f ((q + 1) * P + n) = f (q * P + n) := hstep
        _ = f n := ih n

/-- Every translated complete `2Q`-cell also cancels when the wheel is
`2Q`-periodic. -/
theorem translated_two_mul_cell_eq_zero
    (Q q : ℕ) (f : ℕ → ℤ)
    (hperiod : HasWheelPeriod (2 * Q) f)
    (hrev : HasWheelHalfReversal Q f) :
    ∑ r ∈ Finset.range (2 * Q), f (q * (2 * Q) + r) = 0 := by
  have htranslate : ∀ r : ℕ,
      f (q * (2 * Q) + r) = f r := wheel_period_mul hperiod q
  calc
    ∑ r ∈ Finset.range (2 * Q), f (q * (2 * Q) + r) =
        ∑ r ∈ Finset.range (2 * Q), f r := by
          apply Finset.sum_congr rfl
          intro r hr
          exact htranslate r
    _ = 0 := sum_two_mul_cell_eq_zero_of_halfReversal Q f hrev

/-- Pointwise unit control for a wheel sign. -/
def IsUnitWheelSign (f : ℕ → ℤ) : Prop :=
  ∀ n, |f n| ≤ 1

/-- Any incomplete wheel fragment contributes at most its number of entries. -/
theorem abs_wheel_fragment_le_length
    (f : ℕ → ℤ) (hunit : IsUnitWheelSign f)
    (a L : ℕ) :
    |∑ r ∈ Finset.range L, f (a + r)| ≤ (L : ℤ) := by
  calc
    |∑ r ∈ Finset.range L, f (a + r)|
        ≤ ∑ r ∈ Finset.range L, |f (a + r)| := by
          simpa only [Int.norm_eq_abs] using
            (norm_sum_le (Finset.range L) (fun r => f (a + r)))
    _ ≤ ∑ _r ∈ Finset.range L, (1 : ℤ) := by
          apply Finset.sum_le_sum
          intro r hr
          exact hunit (a + r)
    _ = (L : ℤ) := by simp

/-- Abstract complete-cell plus boundary principle.

If an interval has been split into complete wheel cells and a residual fragment
of length `L`, then all possible signed discrepancy is carried by that residual
fragment. -/
theorem wheel_discrepancy_carried_by_boundary
    (f : ℕ → ℤ) (hunit : IsUnitWheelSign f)
    (boundaryStart boundaryLength : ℕ) :
    |∑ r ∈ Finset.range boundaryLength, f (boundaryStart + r)| ≤
      (boundaryLength : ℤ) :=
  abs_wheel_fragment_le_length f hunit boundaryStart boundaryLength

end RHLean.Arithmetic
