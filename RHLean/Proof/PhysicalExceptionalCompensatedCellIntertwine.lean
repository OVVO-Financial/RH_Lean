import RHLean.Analysis.TwoWheelQ2Compensation
import RHLean.Proof.ExceptionalSignedPacketIdentification

/-!
# Coefficient-level q-square compensation on physical four-cell increments

The scalar predecessor/high-transport compatibility identity is not itself an
unsummed physical field.  This file constructs the coefficient-level daughter
without making that substitution.

For any arithmetic prefix field `g`, first take the literal four-cell increment
`g(4(k+1)) - g(4k)`.  Applying the exact two-step Euler identity at both
endpoints and subtracting leaves the four-cell increment of the same field at
the square-dilated cutoff.  Thus parent, current-q response, and first-power
mate are identified before any norm is taken.

Specializing to the ordinary Mobius prefix makes the parent increment exactly
`fourSlotCellSum k`.  No selected-prime parity law, CRT independence, Gram
estimate, or Mertens cancellation is used.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic

/-- Increment of an arithmetic prefix across one complete physical four-cell. -/
def fourCellPrefixIncrement {A : Type*} [AddGroup A]
    (g : ℕ → A) (k : ℕ) : A :=
  g (4 * (k + 1)) - g (4 * k)

/-- **Coefficient-level two-step q-square compensation.**

Subtract the current-q Euler response and its first-power mate from a physical
four-cell increment.  The remainder is exactly the same four-cell increment
of the q-square shifted field.  This is the unsummed version of the algebraic
q-square remainder needed by the physical packet construction. -/
theorem fourCellPrefixIncrement_twoStep_q2_remainder
    {A : Type*} [CommRing A]
    (q k : ℕ) (g : ℕ → A) :
    fourCellPrefixIncrement g k -
        fourCellPrefixIncrement (freshPrimeDifference q g) k -
        fourCellPrefixIncrement (shift q (freshPrimeDifference q g)) k =
      fourCellPrefixIncrement (shift (q * q) g) k := by
  have hhi := freshPrimeDifference_twoStep_q2_remainder
    q (4 * (k + 1)) g
  have hlo := freshPrimeDifference_twoStep_q2_remainder
    q (4 * k) g
  unfold fourCellPrefixIncrement
  simp only [shift]
  calc
    (g (4 * (k + 1)) - g (4 * k)) -
          (freshPrimeDifference q g (4 * (k + 1)) -
            freshPrimeDifference q g (4 * k)) -
          (freshPrimeDifference q g (4 * (k + 1) / q) -
            freshPrimeDifference q g (4 * k / q)) =
        (g (4 * (k + 1)) -
            freshPrimeDifference q g (4 * (k + 1)) -
            freshPrimeDifference q g (4 * (k + 1) / q)) -
          (g (4 * k) - freshPrimeDifference q g (4 * k) -
            freshPrimeDifference q g (4 * k / q)) := by ring
    _ = g (4 * (k + 1) / (q * q)) - g (4 * k / (q * q)) := by
      rw [hhi, hlo]
    _ = (shift (q * q) g) (4 * (k + 1)) -
          (shift (q * q) g) (4 * k) := by
      rfl

/-- A Mobius prefix changes across one complete four-cell by exactly that
cell's three active Mobius values. -/
theorem fourCellPrefixIncrement_moebius_eq_fourSlotCellSum (k : ℕ) :
    fourCellPrefixIncrement moebiusPositivePrefix k = fourSlotCellSum k := by
  unfold fourCellPrefixIncrement
  rw [moebiusPositivePrefix_four_mul_eq_fourSlotCellSum,
    moebiusPositivePrefix_four_mul_eq_fourSlotCellSum,
    Finset.sum_range_succ]
  ring

/-- Literal current-q response on one physical four-cell. -/
def physicalEulerResponseCellIncrement (q k : ℕ) : ℤ :=
  fourCellPrefixIncrement (freshPrimeDifference q moebiusPositivePrefix) k

/-- Literal first-power mate of the current-q response on the same physical
four-cell endpoints. -/
def physicalEulerMateCellIncrement (q k : ℕ) : ℤ :=
  fourCellPrefixIncrement
    (shift q (freshPrimeDifference q moebiusPositivePrefix)) k

/-- The coefficient-level q-square daughter.  It is deliberately an increment
of the square-shifted full Mobius prefix, not an incidence map applied to a
scalar frozen cube. -/
def physicalQ2DaughterCellIncrement (q k : ℕ) : ℤ :=
  fourCellPrefixIncrement (shift (q * q) moebiusPositivePrefix) k

/-- **Physical compensated cell identity.**  Parent minus current response minus
first-power mate equals the literal q-square daughter, coefficient by
coefficient. -/
theorem fourSlotCellSum_sub_response_sub_mate_eq_q2Daughter
    (q k : ℕ) :
    fourSlotCellSum k - physicalEulerResponseCellIncrement q k -
        physicalEulerMateCellIncrement q k =
      physicalQ2DaughterCellIncrement q k := by
  rw [← fourCellPrefixIncrement_moebius_eq_fourSlotCellSum]
  exact fourCellPrefixIncrement_twoStep_q2_remainder
    q k moebiusPositivePrefix

/-- Expanded endpoint form of the coefficient-level daughter. -/
theorem physicalQ2DaughterCellIncrement_eq (q k : ℕ) :
    physicalQ2DaughterCellIncrement q k =
      moebiusPositivePrefix (4 * (k + 1) / (q * q)) -
        moebiusPositivePrefix (4 * k / (q * q)) := by
  rfl

end RHLean.Analysis
