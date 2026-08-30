import Mathlib
import RHLean.Proof.SquareRootLowPrimeNoLibertyBoundaryHome

/-!
# Signed mass on the terminal no-liberty boundary

`SquareRootLowPrimeNoLibertyBoundaryHome` introduced the four tagged endpoint
classes needed after rematching, but deliberately used them only for a
cardinality bound.  This file equips that exact tagged carrier with its native
signed orientation.

* the distinguished head has weight `+1`;
* each compressed partial-packet cell represents a subtracted unit and has
  weight `-1`;
* a born exit carries the Mobius sign of its arithmetic child;
* a Go root-equality incidence carries the Mobius sign `mu(q*d)` used by the
  existing root-equality defect mass.

No equality with the processed terminal frontier is asserted here.  That is
precisely the second-involution identification theorem still to be proved.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

/-- Native real weight of one tagged no-liberty boundary endpoint. -/
def squareRootLowPrimeNoLibertyBoundaryWeight :
    SquareRootLowPrimeProcessedSeatNoLibertyState → ℝ
  | .inl _ => 1
  | .inr (.inl _) => -1
  | .inr (.inr (.inl z)) =>
      ((μ (squareRootLowPrimeBadAtomChild z) : ℤ) : ℝ)
  | .inr (.inr (.inr z)) =>
      ((μ (z.1.2 * z.2) : ℤ) : ℝ)

@[simp] theorem squareRootLowPrimeNoLibertyBoundaryWeight_head
    (u : Unit) :
    squareRootLowPrimeNoLibertyBoundaryWeight (.inl u) = 1 := rfl

@[simp] theorem squareRootLowPrimeNoLibertyBoundaryWeight_partial
    (s : ℕ) :
    squareRootLowPrimeNoLibertyBoundaryWeight (.inr (.inl s)) = -1 := rfl

@[simp] theorem squareRootLowPrimeNoLibertyBoundaryWeight_born
    (z : ℕ × ℕ) :
    squareRootLowPrimeNoLibertyBoundaryWeight (.inr (.inr (.inl z))) =
      ((μ (squareRootLowPrimeBadAtomChild z) : ℤ) : ℝ) := rfl

@[simp] theorem squareRootLowPrimeNoLibertyBoundaryWeight_rootEquality
    (z : (ℕ × ℕ) × ℕ) :
    squareRootLowPrimeNoLibertyBoundaryWeight (.inr (.inr (.inr z))) =
      ((μ (z.1.2 * z.2) : ℤ) : ℝ) := rfl

end RHLean.Proof
