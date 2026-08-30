import Mathlib
import RHLean.Proof.SquareRootLowPrimeOppositeFixedClassification

/-!
# Weight-preserving finite equivalence at the no-liberty seam

The true fixed population of the second processed-seat Othello matching and the
four-class tagged no-liberty boundary live in different coordinate types.  The
correct closure object is therefore not literal Finset equality, but an
Equiv between the corresponding finite subtypes which preserves signed weight.

This file packages exactly that interface and proves the finite-sum transfer.
The arithmetic construction of the equivalence is the remaining carrier-specific
rematching theorem; once supplied, no further cancellation argument is needed.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- The true stable population of the second processed-seat Othello matching. -/
abbrev SquareRootLowPrimeProcessedSeatNoLibertyStable
    (R K j U : ℕ) :=
  ↥(finiteOthelloStablePart
      (squareRootLowPrimeProcessedSeatCarrier R K j U)
      (squareRootLowPrimeProcessedSeatNoLibertyMate R K j U))

/-- The tagged four-class terminal boundary as a finite subtype. -/
abbrev SquareRootLowPrimeProcessedSeatNoLibertyTaggedBoundary
    (R K j U : ℕ) :=
  ↥(squareRootLowPrimeProcessedSeatNoLibertyBoundary R K j U)

/-- A finite equivalence across the two coordinate systems, together with exact
pointwise preservation of the native signed weights. -/
structure SquareRootLowPrimeNoLibertyWeightEquiv
    (R K j U : ℕ) where
  toEquiv :
    SquareRootLowPrimeProcessedSeatNoLibertyStable R K j U ≃
      SquareRootLowPrimeProcessedSeatNoLibertyTaggedBoundary R K j U
  weight_eq : ∀ x,
    squareRootLowPrimeNoLibertyBoundaryWeight (toEquiv x :
      SquareRootLowPrimeProcessedSeatNoLibertyState) =
      squareRootLowPrimeProcessedSeatWeightReal
        (x : SquareRootLowPrimeProcessedState)

/-- A weight-preserving finite equivalence transfers the complete signed mass.
This is the exact replacement for the ill-typed claim that the two finite sets
are literally equal. -/
theorem squareRootLowPrimeNoLibertyWeightEquiv_sum_eq
    {R K j U : ℕ}
    (e : SquareRootLowPrimeNoLibertyWeightEquiv R K j U) :
    (∑ x ∈ finiteOthelloStablePart
        (squareRootLowPrimeProcessedSeatCarrier R K j U)
        (squareRootLowPrimeProcessedSeatNoLibertyMate R K j U),
      squareRootLowPrimeProcessedSeatWeightReal x) =
      ∑ z ∈ squareRootLowPrimeProcessedSeatNoLibertyBoundary R K j U,
        squareRootLowPrimeNoLibertyBoundaryWeight z := by
  classical
  let A := finiteOthelloStablePart
    (squareRootLowPrimeProcessedSeatCarrier R K j U)
    (squareRootLowPrimeProcessedSeatNoLibertyMate R K j U)
  let B := squareRootLowPrimeProcessedSeatNoLibertyBoundary R K j U
  calc
    (∑ x ∈ A, squareRootLowPrimeProcessedSeatWeightReal x) =
        ∑ x : ↥A, squareRootLowPrimeProcessedSeatWeightReal (x : SquareRootLowPrimeProcessedState) := by
      simp
    _ = ∑ z : ↥B, squareRootLowPrimeNoLibertyBoundaryWeight
          (z : SquareRootLowPrimeProcessedSeatNoLibertyState) := by
      rw [← e.toEquiv.sum_comp]
      apply Finset.sum_congr rfl
      intro x _hx
      simpa [A, B] using (e.weight_eq x).symm
    _ = ∑ z ∈ B, squareRootLowPrimeNoLibertyBoundaryWeight z := by
      simp

/-- Once the carrier-specific weight equivalence is constructed, the tagged
boundary mass is exactly the running imbalance already computed on the true
processed carrier. -/
theorem squareRootLowPrimeNoLibertyWeightEquiv_boundaryMass_eq_runningImbalance
    {R K j U : ℕ} (hR : 2 ≤ R)
    (e : SquareRootLowPrimeNoLibertyWeightEquiv R K j U) :
    (∑ z ∈ squareRootLowPrimeProcessedSeatNoLibertyBoundary R K j U,
      squareRootLowPrimeNoLibertyBoundaryWeight z) =
      squareRootLowPrimeRunningImbalanceReal R K j U := by
  rw [← squareRootLowPrimeNoLibertyWeightEquiv_sum_eq e]
  exact squareRootLowPrimeProcessedSeatNoLibertyMate_stableMass_eq_runningImbalance hR

end RHLean.Proof
