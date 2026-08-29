import Mathlib
import RHLean.Proof.SquareRootLowPrimeDefectThresholdBridge
import RHLean.Proof.SquareRootLowPrimeGoWallPartnerReassembly
import RHLean.Proof.SquareRootLowPrimeGoCrossingMateLedger
import RHLean.Proof.SquareRootLowPrimeGoRootEqualityBoundary
import RHLean.Proof.SquareRootLowPrimeSmoothTransportRecoupling

/-!
# Square-root cross-coordinate intertwiner

The square-root cut is the same arithmetic wall in every coordinate system used
by the low-prime program.  This module packages the already-proved pointwise and
occurrence-level bridges into one kernel-checked certificate.

The certificate deliberately keeps the carriers visible:

* post-root/high and born defects both reduce to the same threshold predicate
  `a <= B < p*a`;
* the canonical processed-seat (Othello) terminal frontier has exactly the
  historical matched `BornSmooth - Transport` mass, up to the already-exposed
  shallow packet/near-root boundary;
* the first-owner wall has literally the same `(c,q)` carrier in cofactor-first
  and old-prime-first (Go) coordinates;
* opening that wall gives the square-dilated Go residual plus its existing
  partner ledger;
* strict Go crossings embed injectively, with multiplicity preserved, into the
  pre-existing tagged transport carrier, where the canonical mate is also
  injective, disjoint from the source image, and cancels it exactly;
* the only non-strict Go crossing face is the exact root-equality carrier, whose
  cardinality and signed mass are at most `R`.

Thus “low”, “high”, Othello, Go, and the original `A-T` transport coordinate do
not define independent arithmetic obstructions.  They form one commuting finite
bookkeeping diagram around the same square-root wall.

This is an exact structural theorem.  It does **not** assert a new bound for
`squareRootMatchedBornSmoothTransport`; any such quantitative estimate remains
a separate theorem obligation until proved from the common carrier.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- The literal canonical processed-seat terminal frontier and the historical
matched smooth/transport coordinate are the same signed state after removing
only the already-exposed shallow boundary.  This is the occurrence-level
Othello-to-`A-T` edge of the cross-coordinate diagram. -/
theorem squareRootLowPrimeProcessedSeatCanonicalTerminalFrontier_weight_sum_eq_matched_sub_shallowBoundary_re
    (R K j : ℕ) (hR : 56 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K) :
    (∑ x ∈ squareRootLowPrimeProcessedSeatCanonicalTerminalFrontier
        R K j (squareRootBornPostTailLowPrimeCutoff R),
      squareRootLowPrimeProcessedSeatWeightReal x) =
      (squareRootMatchedBornSmoothTransport R -
        squareRootLowPrimeTerminalShallowBoundary R K j).re := by
  calc
    (∑ x ∈ squareRootLowPrimeProcessedSeatCanonicalTerminalFrontier
        R K j (squareRootBornPostTailLowPrimeCutoff R),
      squareRootLowPrimeProcessedSeatWeightReal x) =
        squareRootLowPrimeRunningImbalanceReal R K j
          (squareRootBornPostTailLowPrimeCutoff R) :=
      squareRootLowPrimeProcessedSeatCanonicalTerminalFrontier_weight_sum
        (R := R) (K := K) (j := j)
        (U := squareRootBornPostTailLowPrimeCutoff R) (by omega)
    _ = (squareRootMatchedBornSmoothTransport R -
          squareRootLowPrimeTerminalShallowBoundary R K j).re := by
      have h := congrArg Complex.re
        (squareRootLowPrimeRunningImbalance_at_cutoff_eq_matched_sub_shallowBoundary
          R K j hR hK hKR hj)
      simpa [squareRootLowPrimeRunningImbalanceReal] using h

/-- A single proposition carrying all exact maps needed to identify the
square-root obstruction across the Born/high, processed-seat, literal Go-wall,
and tagged transport coordinates.

The fixed prime `p` is the fresh wall coordinate used by the literal
first-owner wall carrier. -/
structure SquareRootLowPrimeCrossCoordinateIntertwiner
    (R K j p : ℕ) : Prop where
  /-- Post-root/high product-boundary defects use the universal threshold
  coordinate `B = X_R / r`. -/
  postRootThreshold :
    ∀ a r : ℕ,
      r ∈ squareRootPostRootPrimePartnerProductBoundary R a (p * a) ↔
        r ∈ squareRootPostRootPrimePartnerSet R a ∧
          squareRootLowPrimeThresholdCrosses p (squareRootEndpoint R / r) a
  /-- Born defects use the same universal threshold coordinate, now with
  `B = r - 1`. -/
  bornThreshold :
    ∀ a r : ℕ,
      r ∈ squareRootBornPartnerBirthBoundary R a (p * a) ↔
        r ∈ squareRootBornPartnerSet R (p * a) ∧
          squareRootLowPrimeThresholdCrosses p (r - 1) a
  /-- The canonical processed-seat terminal carrier is exactly the old matched
  smooth/transport state modulo the explicit shallow boundary. -/
  processedTerminalToMatched :
    (∑ x ∈ squareRootLowPrimeProcessedSeatCanonicalTerminalFrontier
        R K j (squareRootBornPostTailLowPrimeCutoff R),
      squareRootLowPrimeProcessedSeatWeightReal x) =
      (squareRootMatchedBornSmoothTransport R -
        squareRootLowPrimeTerminalShallowBoundary R K j).re
  /-- The underlying complex terminal state satisfies the same identity. -/
  terminalToMatched :
    squareRootLowPrimeRunningImbalance R K j
        (squareRootBornPostTailLowPrimeCutoff R) =
      squareRootMatchedBornSmoothTransport R -
        squareRootLowPrimeTerminalShallowBoundary R K j
  /-- Cofactor-first/Othello and old-prime-first/Go wall readings are literally
  the same finite occurrence carrier, not merely equal signed totals. -/
  literalWallCarrier :
    squareRootLowPrimeWallPairCarrierCofactorFirst R K p =
      squareRootLowPrimeWallPairCarrierOldPrimeFirst R K p
  /-- Opening that literal wall gives its Go square residual plus the partner
  ledger already present beside it. -/
  literalWallReassembly :
    squareRootLowPrimeLiteralWallFalloutMass R K p =
      squareRootLowPrimeLiteralWallResidualFalloutMass R K +
        squareRootLowPrimeLiteralWallPartnerFalloutMass R K p
  /-- The strict Go source map preserves occurrence multiplicity globally. -/
  goSourceInjective :
    Function.Injective squareRootLowPrimeGoStrictCrossingSourceTag
  /-- The canonical mate map also preserves multiplicity on the strict carrier. -/
  goMateInjective :
    Set.InjOn squareRootLowPrimeGoStrictCrossingMateTag
      (squareRootLowPrimeGoStrictCrossingCarrier R)
  /-- Every strict source occurrence is already in the global tagged transport
  support. -/
  goSourceInTransport :
    squareRootLowPrimeGoStrictCrossingSourceImage R ⊆
      lowWheelCanonicalTaggedPhysicalCarrier R
  /-- Every canonical mate occurrence is already in that same transport
  support. -/
  goMateInTransport :
    squareRootLowPrimeGoStrictCrossingMateImage R ⊆
      lowWheelCanonicalTaggedPhysicalCarrier R
  /-- Source and mate images are disjoint occurrences of that transport
  ledger. -/
  goImagesDisjoint :
    Disjoint
      (squareRootLowPrimeGoStrictCrossingSourceImage R)
      (squareRootLowPrimeGoStrictCrossingMateImage R)
  /-- Strict Go crossings cancel exactly against their existing transport
  mates, with no norm and no multiplicity loss. -/
  goStrictCancellation :
    ((squareRootLowPrimeGoStrictCrossingSourceMass R : ℤ) : ℂ) +
      squareRootLowPrimeGoStrictCrossingMateLedger R = 0
  /-- The only crossing face not covered by the strict mate is root equality,
  and its literal occurrence carrier injects into `range R`. -/
  goRootEqualityCard :
    (squareRootLowPrimeGoRootEqualityDefectCarrier R).card ≤ R
  /-- Hence even its signed Möbius mass is root-scale. -/
  goRootEqualityMass :
    |squareRootLowPrimeGoRootEqualityDefectMass R| ≤ (R : ℤ)
  /-- The only terminal discrepancy outside the historical matched core is the
  explicit packet/near-root shallow boundary. -/
  shallowBoundaryBound :
    ‖squareRootLowPrimeTerminalShallowBoundary R K j‖ ≤
      (R : ℝ) + (K : ℝ)

/-- **Cross-coordinate square-root intertwiner.**

Under the native terminal packet hypotheses and one fresh wall prime
`K < p < R`, every structural edge in the diagram above is simultaneously
realized.  In particular the old high response has not disappeared and a new
low obstruction appeared: both sides have been transported to the same
threshold/first-owner/Go coordinates, while the terminal signed state remains
exactly the historical matched `A-T` core modulo the explicit shallow boundary.
-/
theorem squareRootLowPrime_crossCoordinateIntertwiner
    (R K j p : ℕ)
    (hR : 56 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hp : p.Prime) (hKp : K < p) (hpR : p < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K)
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j)
    (hVK : squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ)) :
    SquareRootLowPrimeCrossCoordinateIntertwiner R K j p := by
  have hR2 : 2 ≤ R := by omega
  refine
    { postRootThreshold := ?_
      bornThreshold := ?_
      processedTerminalToMatched := ?_
      terminalToMatched := ?_
      literalWallCarrier := ?_
      literalWallReassembly := ?_
      goSourceInjective := ?_
      goMateInjective := ?_
      goSourceInTransport := ?_
      goMateInTransport := ?_
      goImagesDisjoint := ?_
      goStrictCancellation := ?_
      goRootEqualityCard := ?_
      goRootEqualityMass := ?_
      shallowBoundaryBound := ?_ }
  · intro a r
    exact mem_squareRootPostRootPrimePartnerProductBoundary_iff_thresholdCrosses
  · intro a r
    exact mem_squareRootBornPartnerBirthBoundary_iff_thresholdCrosses
  · exact
      squareRootLowPrimeProcessedSeatCanonicalTerminalFrontier_weight_sum_eq_matched_sub_shallowBoundary_re
        R K j hR hK hKR hj
  · exact
      squareRootLowPrimeRunningImbalance_at_cutoff_eq_matched_sub_shallowBoundary
        R K j hR hK hKR hj
  · exact
      squareRootLowPrimeWallPairCarrierCofactorFirst_eq_oldPrimeFirst
        hR2 hp hKp hpR
  · exact
      squareRootLowPrimeLiteralWallFalloutMass_eq_residual_add_partner
        hR2 hp hKp hpR
  · exact squareRootLowPrimeGoStrictCrossingSourceTag_injective
  · exact squareRootLowPrimeGoStrictCrossingMateTag_injOn R
  · exact squareRootLowPrimeGoStrictCrossingSourceImage_subset_transport hR2
  · exact squareRootLowPrimeGoStrictCrossingMateImage_subset_transport hR2
  · exact squareRootLowPrimeGoStrictCrossingImages_disjoint R
  · exact squareRootLowPrimeGoStrictCrossingMass_add_existingMate_eq_zero hR2
  · exact squareRootLowPrimeGoRootEqualityDefectCarrier_card_le_root R
  · exact abs_squareRootLowPrimeGoRootEqualityDefectMass_le_root R
  · exact
      norm_squareRootLowPrimeTerminalShallowBoundary_le_root_add_depth
        R K j hR hK hKR hj hV0 hVK

end RHLean.Proof
