import Mathlib
import RHLean.Proof.SquareRootLowPrimeSmoothTransportRecoupling

/-!
# One-block terminal boundary budget

The low-prime terminal geometry has already collapsed all fresh-prime matching
failures onto the common square endpoint.  The remaining shallow boundary is
the sum of the compressed partial packet and the near-root rectangle, and
`SquareRootLowPrimeSmoothTransportRecoupling` proves its norm is at most
`R + K`.

This file records the square-budget consequence in the exact currency used by
the later energy arguments.  In particular, for `1 <= K < R`,

  ||boundary||^2 <= 4 R^2 K.

The same bound holds for the difference between the actual terminal running
state and the historical matched smooth/transport core.  Thus the terminal
first-failure/frontier contribution already fits inside an `O(R^2 K)` budget;
any remaining RH-strength estimate must act on the matched signed core rather
than pay again for independent prime-owner boundary strips.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

private theorem root_add_depth_sq_le_four_root_sq_depth
    (R K : ℕ) (hK : 1 ≤ K) (hKR : K < R) :
    ((R : ℝ) + (K : ℝ)) ^ 2 ≤
      4 * (R : ℝ) ^ 2 * (K : ℝ) := by
  have hKreal : (1 : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast hK
  have hKRreal : (K : ℝ) ≤ (R : ℝ) := by
    exact_mod_cast (Nat.le_of_lt hKR)
  have hR0 : (0 : ℝ) ≤ (R : ℝ) := by positivity
  have hK0 : (0 : ℝ) ≤ (K : ℝ) := by positivity
  nlinarith [sq_nonneg ((R : ℝ) - (K : ℝ))]

/-- **One-block shallow-boundary square budget.**

The already-exposed terminal boundary costs at most `4 R^2 K`; no sum over
fresh-prime owners appears. -/
theorem norm_squareRootLowPrimeTerminalShallowBoundary_sq_le_four_root_sq_depth
    (R K j : ℕ) (hR : 56 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K)
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j)
    (hVK : squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ)) :
    ‖squareRootLowPrimeTerminalShallowBoundary R K j‖ ^ 2 ≤
      4 * (R : ℝ) ^ 2 * (K : ℝ) := by
  have hnorm :=
    norm_squareRootLowPrimeTerminalShallowBoundary_le_root_add_depth
      R K j hR hK hKR hj hV0 hVK
  have hnorm0 :
      0 ≤ ‖squareRootLowPrimeTerminalShallowBoundary R K j‖ :=
    norm_nonneg _
  have hRK0 : 0 ≤ (R : ℝ) + (K : ℝ) := by positivity
  have hsquare :
      ‖squareRootLowPrimeTerminalShallowBoundary R K j‖ ^ 2 ≤
        ((R : ℝ) + (K : ℝ)) ^ 2 := by
    nlinarith
  exact hsquare.trans
    (root_add_depth_sq_le_four_root_sq_depth R K hK hKR)

/-- **The terminal frontier relative to the matched core is already budgeted.**

This is the quantitative form of the one-common-square-wall geometry: after all
fresh-prime matching, the actual terminal state differs from the signed matched
smooth/transport core by at most `4 R^2 K` in squared norm. -/
theorem norm_squareRootLowPrimeRunningImbalance_sub_matched_sq_le_four_root_sq_depth
    (R K j : ℕ) (hR : 56 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K)
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j)
    (hVK : squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ)) :
    ‖squareRootLowPrimeRunningImbalance R K j
        (squareRootBornPostTailLowPrimeCutoff R) -
      squareRootMatchedBornSmoothTransport R‖ ^ 2 ≤
        4 * (R : ℝ) ^ 2 * (K : ℝ) := by
  have hnorm :=
    norm_squareRootLowPrimeRunningImbalance_sub_matched_le_root_add_depth
      R K j hR hK hKR hj hV0 hVK
  have hnorm0 :
      0 ≤ ‖squareRootLowPrimeRunningImbalance R K j
        (squareRootBornPostTailLowPrimeCutoff R) -
          squareRootMatchedBornSmoothTransport R‖ :=
    norm_nonneg _
  have hRK0 : 0 ≤ (R : ℝ) + (K : ℝ) := by positivity
  have hsquare :
      ‖squareRootLowPrimeRunningImbalance R K j
          (squareRootBornPostTailLowPrimeCutoff R) -
        squareRootMatchedBornSmoothTransport R‖ ^ 2 ≤
          ((R : ℝ) + (K : ℝ)) ^ 2 := by
    nlinarith
  exact hsquare.trans
    (root_add_depth_sq_le_four_root_sq_depth R K hK hKR)

end RHLean.Proof
