import Mathlib
import RHLean.Proof.FiniteOthelloMatching
import RHLean.Proof.SquareRootLowPrimeNoLibertyFiniteEquiv
import RHLean.Proof.SquareRootLowPrimePartialEndpointCarrier
import RHLean.Proof.SquareRootLowPrimeProcessedCreationResponseInvolution
import RHLean.Proof.SquareRootLowPrimeProcessedCreationResponseFixedClassification

/-!
# Boundary-shadow Morse/Othello reduction

The processed-seat terminal frontier and the four tagged no-liberty endpoint
classes live in different coordinate types.  For the final signed-mass question
the correct common carrier is their disjoint sum, with the terminal-side weight
negated.

A fixed-point-free sign-reversing involution on this one finite carrier is
strictly stronger than the aggregate mass-transfer identity, and therefore
immediately yields the existing 4R bound.  No homology library is required:
finite involution parity is enough.  Acyclic/monotone blocker arguments are
useful only for constructing the involution.

This file deliberately does not assume a source-to-boundary classifier.  It
packages the exact object such a bottom-up boundary-shadow construction has to
annihilate.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

abbrev SquareRootLowPrimeBoundaryShadowState :=
  Sum SquareRootLowPrimeProcessedState
    SquareRootLowPrimeProcessedSeatNoLibertyState

/-- Signed defect carrier
    critical frontier disjoint-union negative terminal boundary. -/
def squareRootLowPrimeBoundaryShadowCarrier
    (R K j U : ℕ) : Finset SquareRootLowPrimeBoundaryShadowState :=
  (squareRootLowPrimeProcessedSeatDescendingTerminalFrontier R K j U).disjSum
    (squareRootLowPrimeProcessedSeatNoLibertyBoundary R K j U)

/-- Native signed weight on the defect carrier.  The terminal side is negated,
so total mass zero is exactly the desired mass-transfer identity. -/
def squareRootLowPrimeBoundaryShadowWeight :
    SquareRootLowPrimeBoundaryShadowState → ℝ
  | .inl x => squareRootLowPrimeProcessedSeatWeightReal x
  | .inr z => -squareRootLowPrimeNoLibertyBoundaryWeight z

/-- The defect-carrier mass is literally source mass minus target mass. -/
theorem sum_squareRootLowPrimeBoundaryShadowCarrier_eq_frontier_sub_boundary
    (R K j U : ℕ) :
    (∑ x ∈ squareRootLowPrimeBoundaryShadowCarrier R K j U,
        squareRootLowPrimeBoundaryShadowWeight x) =
      (∑ x ∈ squareRootLowPrimeProcessedSeatDescendingTerminalFrontier R K j U,
          squareRootLowPrimeProcessedSeatWeightReal x) -
        ∑ z ∈ squareRootLowPrimeProcessedSeatNoLibertyBoundary R K j U,
          squareRootLowPrimeNoLibertyBoundaryWeight z := by
  unfold squareRootLowPrimeBoundaryShadowCarrier
    squareRootLowPrimeBoundaryShadowWeight
  rw [Finset.sum_disjSum]
  simp only [Finset.sum_neg_distrib]

/-- Exact finite-Morse/Othello target.  Acyclicity is not a separate hypothesis:
a fixed-point-free involution with sign reversal already annihilates the finite
signed chain.  The existing decreasing-blocker machinery is one way to build
such a mate. -/
structure SquareRootLowPrimeBoundaryShadowMatching
    (R K j U : ℕ) where
  mate : SquareRootLowPrimeBoundaryShadowState →
    SquareRootLowPrimeBoundaryShadowState
  mem : ∀ x ∈ squareRootLowPrimeBoundaryShadowCarrier R K j U,
    mate x ∈ squareRootLowPrimeBoundaryShadowCarrier R K j U
  inv : ∀ x ∈ squareRootLowPrimeBoundaryShadowCarrier R K j U,
    mate (mate x) = x
  nofix : ∀ x ∈ squareRootLowPrimeBoundaryShadowCarrier R K j U,
    mate x ≠ x
  neg : ∀ x ∈ squareRootLowPrimeBoundaryShadowCarrier R K j U,
    squareRootLowPrimeBoundaryShadowWeight (mate x) =
      -squareRootLowPrimeBoundaryShadowWeight x

/-- A perfect signed boundary-shadow matching annihilates the defect carrier. -/
theorem sum_squareRootLowPrimeBoundaryShadowCarrier_eq_zero_of_matching
    {R K j U : ℕ}
    (M : SquareRootLowPrimeBoundaryShadowMatching R K j U) :
    (∑ x ∈ squareRootLowPrimeBoundaryShadowCarrier R K j U,
        squareRootLowPrimeBoundaryShadowWeight x) = 0 := by
  let S := squareRootLowPrimeBoundaryShadowCarrier R K j U
  let w := squareRootLowPrimeBoundaryShadowWeight
  have hmove : finiteOthelloMovingPart S M.mate = S := by
    ext x
    constructor
    · intro hx
      exact (Finset.mem_filter.mp hx).1
    · intro hx
      exact Finset.mem_filter.mpr ⟨hx, M.nofix x hx⟩
  rw [← hmove]
  exact sum_finiteOthelloMovingPart_eq_zero
    S M.mate w
    (fun x hx => M.mem x hx)
    (fun x hx => M.inv x hx)
    (fun x hx _ => M.neg x hx)

/-- Therefore a perfect boundary-shadow matching proves the exact source/target
mass transfer needed by the no-liberty endpoint argument. -/
theorem squareRootLowPrimeBoundaryShadow_massTransfer_of_matching
    {R K j U : ℕ}
    (M : SquareRootLowPrimeBoundaryShadowMatching R K j U) :
    (∑ x ∈ squareRootLowPrimeProcessedSeatDescendingTerminalFrontier R K j U,
        squareRootLowPrimeProcessedSeatWeightReal x) =
      ∑ z ∈ squareRootLowPrimeProcessedSeatNoLibertyBoundary R K j U,
        squareRootLowPrimeNoLibertyBoundaryWeight z := by
  have hzero :=
    sum_squareRootLowPrimeBoundaryShadowCarrier_eq_zero_of_matching M
  rw [sum_squareRootLowPrimeBoundaryShadowCarrier_eq_frontier_sub_boundary] at hzero
  linarith

/-- At the canonical cutoff, the boundary-shadow involution is already enough
to close the root-scale terminal amplitude estimate. -/
theorem abs_squareRootLowPrimeRunningImbalanceReal_le_four_root_of_boundaryShadowMatching
    {R K j : ℕ} (hR : 2 ≤ R) (hKR : K < R)
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j)
    (hVK : squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ))
    (M : SquareRootLowPrimeBoundaryShadowMatching
      R K j (squareRootBornPostTailLowPrimeCutoff R)) :
    |squareRootLowPrimeRunningImbalanceReal R K j
        (squareRootBornPostTailLowPrimeCutoff R)| ≤ 4 * (R : ℝ) := by
  apply abs_squareRootLowPrimeRunningImbalanceReal_le_four_root_of_massTransfer
    hR hKR hV0 hVK
  exact squareRootLowPrimeBoundaryShadow_massTransfer_of_matching M

/-! ## Replace the descending critical set by the creation-response critical set

Both the descending-prime mate and the creation-response mate act on the exact
same processed-seat carrier, are involutions there, and reverse native signed
weight on every moved state.  Finite Othello therefore identifies their stable
masses exactly.  This is the useful Morse move-order invariance: we are free to
classify whichever fixed set has the cleaner endpoint geometry.
-/

/-- The two processed-carrier Morse/Othello matchings have exactly the same
signed critical mass.  No alternating path has to be constructed explicitly. -/
theorem squareRootLowPrime_creationResponseStableMass_eq_noLibertyStableMass
    {R K j U : ℕ} (hR : 1 ≤ R) (hK : 1 ≤ K) (hKU : K ≤ U) :
    (∑ x ∈ finiteOthelloStablePart
        (squareRootLowPrimeProcessedSeatCarrier R K j U)
        (squareRootLowPrimeProcessedSeatCreationResponseMate R K j U),
      squareRootLowPrimeProcessedSeatWeightReal x) =
      ∑ x ∈ finiteOthelloStablePart
        (squareRootLowPrimeProcessedSeatCarrier R K j U)
        (squareRootLowPrimeProcessedSeatNoLibertyMate R K j U),
      squareRootLowPrimeProcessedSeatWeightReal x := by
  exact
    sum_finiteOthelloStablePart_eq_of_two_involutions
      (squareRootLowPrimeProcessedSeatCarrier R K j U)
      (squareRootLowPrimeProcessedSeatCreationResponseMate R K j U)
      (squareRootLowPrimeProcessedSeatNoLibertyMate R K j U)
      squareRootLowPrimeProcessedSeatWeightReal
      (fun x hx =>
        squareRootLowPrimeProcessedSeatCreationResponseMate_mem hR hK hKU hx)
      (fun x hx =>
        squareRootLowPrimeProcessedSeatCreationResponseMate_involutive hR hK hKU hx)
      (fun x hx hne =>
        squareRootLowPrimeProcessedSeatCreationResponseMate_weight_neg
          hR hK hKU hx hne)
      (fun x hx => squareRootLowPrimeProcessedSeatNoLibertyMate_mem hx)
      (fun x hx => squareRootLowPrimeProcessedSeatNoLibertyMate_involutive hx)
      (fun x hx hne =>
        squareRootLowPrimeProcessedSeatNoLibertyMate_weight_neg hx hne)

/-- Consequently the creation-response fixed set already carries the complete
running imbalance.  The descending terminal frontier can be discarded from the
remaining classification problem. -/
theorem squareRootLowPrime_creationResponseStableMass_eq_runningImbalance
    {R K j U : ℕ} (hR : 2 ≤ R) (hK : 1 ≤ K) (hKU : K ≤ U) :
    (∑ x ∈ finiteOthelloStablePart
        (squareRootLowPrimeProcessedSeatCarrier R K j U)
        (squareRootLowPrimeProcessedSeatCreationResponseMate R K j U),
      squareRootLowPrimeProcessedSeatWeightReal x) =
      squareRootLowPrimeRunningImbalanceReal R K j U := by
  calc
    (∑ x ∈ finiteOthelloStablePart
        (squareRootLowPrimeProcessedSeatCarrier R K j U)
        (squareRootLowPrimeProcessedSeatCreationResponseMate R K j U),
      squareRootLowPrimeProcessedSeatWeightReal x) =
      ∑ x ∈ finiteOthelloStablePart
        (squareRootLowPrimeProcessedSeatCarrier R K j U)
        (squareRootLowPrimeProcessedSeatNoLibertyMate R K j U),
      squareRootLowPrimeProcessedSeatWeightReal x :=
        squareRootLowPrime_creationResponseStableMass_eq_noLibertyStableMass
          (by omega) hK hKU
    _ = squareRootLowPrimeRunningImbalanceReal R K j U :=
      squareRootLowPrimeProcessedSeatNoLibertyMate_stableMass_eq_runningImbalance hR

end RHLean.Proof
