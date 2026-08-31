import Mathlib
import RHLean.Proof.SquareRootLowPrimeOppositeFixedClassification
import RHLean.Proof.SquareRootLowPrimeNoLibertyBoundaryHome

/-!
# Pointwise embedding interface for the no-liberty boundary

The final no-liberty compression does not need surjectivity onto every available
boundary home.  What the quantitative argument actually uses is a literal
pointwise injection from the descending processed-seat survivors into the tagged
four-class boundary, together with preservation of the native signed weight.

This file isolates that exact interface.  It deliberately does not manufacture
an equivalence from a cardinality equality: the embedding must be supplied by
the arithmetic alternating-component classifier.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- A pointwise no-liberty classifier: every descending terminal survivor is
sent to one actual tagged boundary endpoint, injectively and with its signed
weight unchanged. -/
structure SquareRootLowPrimeDescendingBoundaryWeightEmbedding
    (R K j U : ℕ) where
  toEmbedding :
    ↥(squareRootLowPrimeProcessedSeatDescendingTerminalFrontier R K j U) ↪
      ↥(squareRootLowPrimeProcessedSeatNoLibertyBoundary R K j U)
  weight_eq : ∀ x,
    squareRootLowPrimeNoLibertyBoundaryWeight
        (toEmbedding x : SquareRootLowPrimeProcessedSeatNoLibertyState) =
      squareRootLowPrimeProcessedSeatWeightReal
        (x : SquareRootLowPrimeProcessedState)

/-- The source side is pointwise unit-bounded before any mass-from-cardinality
argument is made. -/
theorem abs_squareRootLowPrimeProcessedSeatDescendingFrontierWeight_le_one
    {R K j U : ℕ}
    (x : ↥(squareRootLowPrimeProcessedSeatDescendingTerminalFrontier R K j U)) :
    |squareRootLowPrimeProcessedSeatWeightReal
        (x : SquareRootLowPrimeProcessedState)| ≤ 1 := by
  exact abs_squareRootLowPrimeProcessedSeatWeightReal_le_one
    (x : SquareRootLowPrimeProcessedState)

/-- Unit source weights bound the absolute descending-frontier mass by the
number of surviving processed seats. -/
theorem abs_squareRootLowPrimeProcessedSeatDescendingFrontierMass_le_card
    (R K j U : ℕ) :
    |∑ x ∈ squareRootLowPrimeProcessedSeatDescendingTerminalFrontier R K j U,
        squareRootLowPrimeProcessedSeatWeightReal x| ≤
      ((squareRootLowPrimeProcessedSeatDescendingTerminalFrontier
          R K j U).card : ℝ) := by
  calc
    |∑ x ∈ squareRootLowPrimeProcessedSeatDescendingTerminalFrontier R K j U,
        squareRootLowPrimeProcessedSeatWeightReal x| ≤
      ∑ x ∈ squareRootLowPrimeProcessedSeatDescendingTerminalFrontier R K j U,
        |squareRootLowPrimeProcessedSeatWeightReal x| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x ∈ squareRootLowPrimeProcessedSeatDescendingTerminalFrontier R K j U,
        (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro x _hx
      exact abs_squareRootLowPrimeProcessedSeatWeightReal_le_one x
    _ = ((squareRootLowPrimeProcessedSeatDescendingTerminalFrontier
          R K j U).card : ℝ) := by
      simp

/-- An actual pointwise embedding transfers source cardinality to the tagged
boundary cardinality. -/
theorem squareRootLowPrimeProcessedSeatDescendingFrontier_card_le_boundary
    {R K j U : ℕ}
    (e : SquareRootLowPrimeDescendingBoundaryWeightEmbedding R K j U) :
    (squareRootLowPrimeProcessedSeatDescendingTerminalFrontier R K j U).card ≤
      (squareRootLowPrimeProcessedSeatNoLibertyBoundary R K j U).card := by
  have hcard :
      Fintype.card
          ↥(squareRootLowPrimeProcessedSeatDescendingTerminalFrontier R K j U) ≤
        Fintype.card ↥(squareRootLowPrimeProcessedSeatNoLibertyBoundary R K j U) :=
    Fintype.card_le_of_injective e.toEmbedding e.toEmbedding.injective
  simpa using hcard

/-- **Mass transfer from the actual classifier.**  At the canonical terminal
cutoff, a weight-preserving injection into the four tagged endpoint classes
immediately gives the `4*R` bound.  No surjectivity and no arbitrary finite-set
equivalence are used. -/
theorem abs_squareRootLowPrimeRunningImbalanceReal_le_four_root_of_embedding
    {R K j : ℕ}
    (hR : 2 ≤ R) (hKR : K < R)
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j)
    (hVK : squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ))
    (e : SquareRootLowPrimeDescendingBoundaryWeightEmbedding
      R K j (squareRootBornPostTailLowPrimeCutoff R)) :
    |squareRootLowPrimeRunningImbalanceReal R K j
        (squareRootBornPostTailLowPrimeCutoff R)| ≤ 4 * (R : ℝ) := by
  rw [← squareRootLowPrimeProcessedSeatDescendingTerminalFrontier_weight_sum hR]
  have hmass :=
    abs_squareRootLowPrimeProcessedSeatDescendingFrontierMass_le_card
      R K j (squareRootBornPostTailLowPrimeCutoff R)
  have hsourceTarget :=
    squareRootLowPrimeProcessedSeatDescendingFrontier_card_le_boundary e
  have htarget :=
    squareRootLowPrimeProcessedSeatNoLibertyBoundary_card_le_four_root
      (R := R) (K := K) (j := j) (by omega) hKR hV0 hVK
  exact hmass.trans <| by
    exact_mod_cast hsourceTarget.trans htarget

end RHLean.Proof
