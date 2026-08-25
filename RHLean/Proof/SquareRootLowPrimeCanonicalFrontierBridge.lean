import Mathlib
import RHLean.Proof.SquareRootLowPrimeSequentialDissipationOwnership
import RHLean.Proof.LowWheelCanonicalDefectReduction
import RHLean.Analysis.SquareRootPositiveSmoothCollapse

/-!
# Full low-prime response as the canonical root-downcross frontier

The sequential dissipation modules split every actual fresh-prime increment as

`Delta_p = -D_p + F_p`

and assign the complete positive-orientation response mass to its unique
largest-prime owner.  That support theorem does not make the response weight of
one cofactor small.  The correct next operation is to retain the signed response
and connect it to the repository's older atom-level least-prime involution.

This file makes that connection exactly at the terminal low-prime cutoff

`P_R = R - floor(sqrt R)`.

Four existing identities are synthesized:

* the low-prime collapse of `BornPostTail`;
* `BornPostTail = matched born/transport - partial crossing packet`;
* the positive-smooth prime-Mertens collapse;
* the canonical transport involution
  `M(R^2-1) = M(R) - canonicalDowncross`.

The result identifies the complete processed response, and therefore the final
running imbalance, with the canonical adjacent root-downcross ledger plus only
explicit lower-scale terms, the already-isolated partial crossing packet, and
the near-root remainder.  The latter already has norm at most `R`.

Thus the transition-seat shell is not declared to be the complete bad
frontier.  The complete atom-level frontier supplied by the existing Lean
architecture is the canonical quotient root-downcross ledger.

No bound on that ledger, no energy decrement, no PNT estimate, no Mertens
hypothesis, and no RH implication is asserted here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

/-- The lower-scale and canonical-frontier core of the terminal running
imbalance.  The only omitted term is the positive near-root remainder. -/
def squareRootLowPrimeCanonicalTerminalCore
    (R K j : ℕ) : ℂ :=
  mertensSummatory R - lowWheelCanonicalDowncrossLedger R +
    squareRootPositiveSmoothPrimeMertensTransform R -
      ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ)

/-- **Full processed-response / canonical-frontier bridge.**

The entire low-prime processed response—not merely the transition-seat
component—is the canonical root-downcross ledger together with explicit
lower-scale terms and the already-controlled near-root remainder. -/
theorem squareRootBornPostTailLowPrimeProcessedResponse_eq_canonicalFrontier
    (R K j : ℕ) (hR : 16 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K) :
    squareRootBornPostTailLowPrimeProcessedResponse R K j =
      1 - mertensSummatory R + lowWheelCanonicalDowncrossLedger R -
        squareRootPositiveSmoothPrimeMertensTransform R +
        ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ) +
        squareRootBornPostTailNearRootRemainder R K j := by
  have hcollapse :=
    squareRootBornPostTail_eq_one_sub_lowPrimeProcessedResponse_add_nearRootRemainder
      R K j hR hK hKR hj
  have hmatched :=
    squareRootBornPostTail_eq_matched_sub_partial R K j (by omega)
  have hpositive :=
    squarePrefixMertens_eq_neg_positivePrimeTransform_add_matched
      R (by omega)
  have hdowncross :=
    squarePrefixMertens_eq_mertens_sub_canonicalDowncross R (by omega)
  linear_combination hcollapse - hmatched + hpositive - hdowncross

/-- Terminal running imbalance in the exact canonical-frontier coordinates. -/
theorem squareRootLowPrimeRunningImbalance_at_cutoff_eq_canonicalFrontier
    (R K j : ℕ) (hR : 16 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K) :
    squareRootLowPrimeRunningImbalance R K j
        (squareRootBornPostTailLowPrimeCutoff R) =
      squareRootLowPrimeCanonicalTerminalCore R K j -
        squareRootBornPostTailNearRootRemainder R K j := by
  unfold squareRootLowPrimeRunningImbalance
    squareRootLowPrimeCanonicalTerminalCore
  rw [squareRootBornPostTailRunningLowPrimeResponse_at_cutoff]
  rw [squareRootBornPostTailLowPrimeProcessedResponse_eq_canonicalFrontier
    R K j hR hK hKR hj]
  ring

/-- **Quantitative terminal reduction.**  After the complete signed low-prime
response is synthesized with the canonical involution, the discrepancy from
the explicit canonical core is at most `R`.  This estimate uses only the
already-proved near-root rectangle bound; it does not estimate the canonical
downcross ledger itself. -/
theorem squareRootLowPrimeRunningImbalance_sub_canonicalCore_norm_le_root
    (R K j : ℕ) (hR : 16 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K) :
    ‖squareRootLowPrimeRunningImbalance R K j
        (squareRootBornPostTailLowPrimeCutoff R) -
      squareRootLowPrimeCanonicalTerminalCore R K j‖ ≤ (R : ℝ) := by
  rw [squareRootLowPrimeRunningImbalance_at_cutoff_eq_canonicalFrontier
    R K j hR hK hKR hj]
  have hnear := squareRootBornPostTailNearRootRemainder_norm_le_root
    R K j hR hK hKR hj
  simpa using hnear

end RHLean.Proof
