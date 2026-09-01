import Mathlib
import RHLean.Proof.SquareWheelSurvivorProcessedResponseBridge

/-!
# Square-wheel runs in the processed / positive coordinate

The endpoint bridge

`Survivor = Processed + Positive + Boundary - Low - Death`

can be substituted directly into the existing square-wheel survivor-run
identity.  The low and lifetime-death endpoint differences then cancel
*exactly*, before any norm is taken.

It is convenient to keep the two genuinely coupled arithmetic channels as one
signed object

`Coupled = Processed + Positive`.

At the canonical low-prime cutoff this object is exactly the square-prefix
Mertens value minus the already-elementary shallow boundary.  Consequently a
square-wheel run is the difference of two coupled endpoint masses, plus the
shallow-boundary difference, minus the unchanged rank-one wheel zero-mode
correction.

No estimate, triangle inequality, independence assumption, or asymptotic input
appears here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

/-- The signed channel that must remain coupled: terminal processed-seat mass
plus the positive-orientation smooth mass. -/
def squareRootLowPrimeProcessedPositiveCoupled
    (R K j : ℕ) : ℂ :=
  squareRootLowPrimeRunningImbalance R K j
      (squareRootBornPostTailLowPrimeCutoff R) +
    squareRootPositiveSmoothMass R

/-- **Endpoint coupled identity.**  The processed and positive channels together
are exactly Mertens minus the shallow terminal boundary. -/
theorem squareRootLowPrimeProcessedPositiveCoupled_eq_squarePrefixMertens_sub_boundary
    (R K j : ℕ) (hR : 56 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K) :
    squareRootLowPrimeProcessedPositiveCoupled R K j =
      squarePrefixMertens (R - 1) -
        squareRootLowPrimeTerminalShallowBoundary R K j := by
  unfold squareRootLowPrimeProcessedPositiveCoupled
  rw [squareRootLowPrimeRunningImbalance_at_cutoff_eq_squarePrefixMertens_sub_positiveSmooth_sub_boundary
      R K j hR hK hKR hj]
  ring

/-- The same endpoint identity rearranged so that the shallow boundary restores
the complete square-prefix Mertens value. -/
theorem squareRootLowPrimeProcessedPositiveCoupled_add_boundary_eq_squarePrefixMertens
    (R K j : ℕ) (hR : 56 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K) :
    squareRootLowPrimeProcessedPositiveCoupled R K j +
        squareRootLowPrimeTerminalShallowBoundary R K j =
      squarePrefixMertens (R - 1) := by
  rw [squareRootLowPrimeProcessedPositiveCoupled_eq_squarePrefixMertens_sub_boundary
      R K j hR hK hKR hj]
  ring

/-- **Run-level coordinate synthesis.**

After substituting the processed endpoint dictionary into the existing
`SquareWheelSurvivorRun` identity, both the low endpoint process and the
lifetime-death endpoint process disappear algebraically.  What remains is only

* the difference of the coupled processed/positive channel;
* the difference of the shallow terminal boundary; and
* the original rank-one wheel zero-mode correction.

This is the exact run-level statement that the low obstruction was a coordinate
artifact rather than an additional analytic degree of freedom. -/
theorem primorialMinimalSquareWheelNonzeroResponse_sub_eq_processedPositiveRun_add_boundaryRun_sub_zeroMode
    (k Ra Rb K ja jb : ℕ)
    (hRa : 56 ≤ Ra) (hRb : 56 ≤ Rb)
    (hK : 1 ≤ K)
    (hKRa : K < Ra) (hKRb : K < Rb)
    (hja : ja ≤ squareRootReciprocalPrimeLayerCard Ra K)
    (hjb : jb ≤ squareRootReciprocalPrimeLayerCard Rb K)
    (haLower : primorialBlockLower k < squarePrefixEndpoint (Ra - 1))
    (haUpper : squarePrefixEndpoint (Ra - 1) ≤ primorialBlockUpper k)
    (hbLower : primorialBlockLower k < squarePrefixEndpoint (Rb - 1))
    (hbUpper : squarePrefixEndpoint (Rb - 1) ≤ primorialBlockUpper k) :
    squareWheelNonzeroSampleResponse (primorialMinimalWheelSystem k) (Rb - 1) -
        squareWheelNonzeroSampleResponse (primorialMinimalWheelSystem k) (Ra - 1) =
      (squareRootLowPrimeProcessedPositiveCoupled Rb K jb -
        squareRootLowPrimeProcessedPositiveCoupled Ra K ja) +
      (squareRootLowPrimeTerminalShallowBoundary Rb K jb -
        squareRootLowPrimeTerminalShallowBoundary Ra K ja) -
      (squareWheelSampleRatio (primorialMinimalWheelSystem k) (Rb - 1) -
        squareWheelSampleRatio (primorialMinimalWheelSystem k) (Ra - 1)) *
        ((((primorialMinimalWheelSystem k).residual
          (primorialBlockUpper k) : ℤ) : ℂ)) := by
  rw [primorialMinimalSquareWheelNonzeroResponse_sub_eq_survivorRunCentered_add_lowDiff_add_deathDiff
      k (Ra - 1) (Rb - 1) haLower haUpper hbLower hbUpper]
  unfold primorialMinimalSquareWheelSurvivorRunCentered
  rw [survivorZeroMode_eq_processedRunningImbalance_add_endpointResiduals
        Rb K jb hRb hK hKRb hjb,
      survivorZeroMode_eq_processedRunningImbalance_add_endpointResiduals
        Ra K ja hRa hK hKRa hja]
  unfold squareRootLowPrimeProcessedPositiveCoupled
  ring

end RHLean.Proof
