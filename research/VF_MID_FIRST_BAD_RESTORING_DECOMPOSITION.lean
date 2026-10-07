import Mathlib
import «research.VF_MID_ANCHORED_CODIV_GATE_INLET»
import «research.VF_MID_GLOBAL_FIRST_BAD_RADIAL_BUDGET»

/-!
# First-bad anchored Co/Div decomposition with restoring terms retained

The full denominator is the original odd-seat anchored PM denominator.  Both
endpoint-sign identities retain the restoring packet and the historical anchor
square.  At a first-bad successor, the prior-good hypothesis signs the anchor
slack; it does not sign the remaining one-sided source budget.

This module proves the exact equalities and the restoring/slack signs.  It does
not identify the remaining source budget with a completed-gate or clipped-tree
ledger, and does not claim the final normalized half bound.
-/

noncomputable section
open scoped BigOperators
namespace RHLean.Analysis
open RHLean.Arithmetic RHLean.Proof
attribute [local instance] Classical.propDecidable

/-- **Exact upper-sign anchored normal form.**

The rigid anchor square is retained and the squareful strict-descendant packet
is isolated as the exact restoring term.  This is an equality. -/
theorem vfMidFirstBadNormalizedProduct_eq_upperActive_sub_squarefulRestoring
    {R : ℕ} (hR : 3 ≤ R) :
    vfMidFirstBadNNSNormalizedCovariance R *
        vfMidFirstBadZeroTargetTotalMass R =
      vfMidUpperFirstBadSourceBill R -
        vfMidOneBlockProcessedSquarefulCharge R *
          (2 * vfMidActualPrimeEndpointDefect (R + 1) +
            vfMidOneBlockProcessedSquarefulCharge R) +
        vfMidActualPrimeEndpointDefect R ^ 2 := by
  rw [← vfMidCorrelationEnergy_add_anchorSq_eq_nnsNormalized_mul_total hR]
  rw [vfMidCorrelationEnergy_eq_upperActive_sub_squarefulRestoring hR]
  rfl

/-- **Exact lower-sign anchored normal form.**

The negative prime stream is retained as the exact restoring term and the
anchor square stays coupled to the remaining composite source.  This is an
equality. -/
theorem vfMidFirstBadNormalizedProduct_eq_lowerComposite_add_primeRestoring
    {R : ℕ} (hR : 3 ≤ R) :
    vfMidFirstBadNNSNormalizedCovariance R *
        vfMidFirstBadZeroTargetTotalMass R =
      vfMidLowerFirstBadSourceBill R +
        vfMidOneBlockPrimeSeatCharge R *
          (-2 * vfMidActualPrimeEndpointDefect (R + 1) -
            vfMidOneBlockPrimeSeatCharge R) +
        vfMidActualPrimeEndpointDefect R ^ 2 := by
  rw [← vfMidCorrelationEnergy_add_anchorSq_eq_nnsNormalized_mul_total hR]
  rw [vfMidCorrelationEnergy_eq_lowerActive_add_primeRestoring hR]
  rfl

/-- **Exact normalized endpoint-energy identity.**

The complete anchored NNS numerator is not an additional energy packet: after
the exact endpoint weld it is literally the next endpoint defect squared.
Naming this identity prevents the rigid anchor square from being charged a
second time or assigned a fictitious fresh owner. -/
theorem vfMidFirstBadNormalizedProduct_eq_nextEndpointDefect_sq
    {R : ℕ} (hR : 3 ≤ R) :
    vfMidFirstBadNNSNormalizedCovariance R *
        vfMidFirstBadZeroTargetTotalMass R =
      vfMidActualPrimeEndpointDefect (R + 1) ^ 2 := by
  have hnorm :=
    vfMidCorrelationEnergy_add_anchorSq_eq_nnsNormalized_mul_total hR
  have hcorr :=
    vfMidSquareEndpointError_sq_succ_eq_correlation
      R (by omega : 2 ≤ R)
  calc
    vfMidFirstBadNNSNormalizedCovariance R *
        vfMidFirstBadZeroTargetTotalMass R =
      2 * vfMidSquareEndpointAccumulationCorrelation R +
        vfMidSquareBandError R ^ 2 +
        vfMidActualPrimeEndpointDefect R ^ 2 := hnorm.symm
    _ = vfMidActualPrimeEndpointDefect (R + 1) ^ 2 := by
      rw [vfMidActualPrimeEndpointDefect_eq_squareEndpointError
          (R := R) (by omega : 2 ≤ R),
        vfMidActualPrimeEndpointDefect_eq_squareEndpointError
          (R := R + 1) (by omega : 2 ≤ R + 1)]
      nlinarith [hcorr]

/-- The actual full anchored Co minus three times Div.  In particular, this
includes the historical diagonal and all squareful current seats. -/
def vfMidFirstBadAnchoredCoDivExcess (R : ℕ) : ℝ :=
  vfMidAnchoredZeroTargetCoPartialGram
      (vfMidOddCandidateSeats R) (vfMidOddSignedSeatCharge R)
      (vfMidActualPrimeEndpointDefect R) -
    3 * vfMidAnchoredZeroTargetDivergentGram
      (vfMidOddCandidateSeats R) (vfMidOddSignedSeatCharge R)
      (vfMidActualPrimeEndpointDefect R)

/-- Exact full-denominator conversion; no zero-denominator division is used. -/
theorem vfMidFirstBadAnchoredCoDivExcess_eq_two_product_sub_total (R : ℕ) :
    vfMidFirstBadAnchoredCoDivExcess R =
      2 * (vfMidFirstBadNNSNormalizedCovariance R *
        vfMidFirstBadZeroTargetTotalMass R) -
        vfMidFirstBadZeroTargetTotalMass R := by
  unfold vfMidFirstBadAnchoredCoDivExcess
    vfMidFirstBadNNSNormalizedCovariance
    vfMidAnchoredZeroTargetNNSNormalizedCovariance
    vfMidFirstBadZeroTargetTotalMass vfMidAnchoredZeroTargetTotalMass
  rw [nnsZeroTargetNormalizedCovariance_mul_total
    (vfMidAnchoredZeroTargetCoPartialGram_nonneg _ _ _)
    (vfMidAnchoredZeroTargetDivergentGram_nonneg _ _ _)]
  ring

/-- Upper-sign source identity with the full squareful restoring packet and
the exact prior-wall anchor slack.  The first parenthesis is an explicit VF
source budget; no nonpositivity or completed-gate identification is asserted. -/
theorem vfMidFirstBadAnchoredCoDivExcess_eq_upper_restoring_slack
    {R : ℕ} (hR : 3 ≤ R) :
    vfMidFirstBadAnchoredCoDivExcess R =
      (2 * vfMidUpperFirstBadSourceBill R +
        2 * ((2 : ℝ) * vfMidSyntheticRadialScale R) ^ 2 -
        vfMidFirstBadZeroTargetTotalMass R) -
      2 * vfMidOneBlockProcessedSquarefulCharge R *
        (2 * vfMidActualPrimeEndpointDefect (R + 1) +
          vfMidOneBlockProcessedSquarefulCharge R) -
      2 * vfMidFirstBadQuadraticAnchorSlack (2 : ℝ) R := by
  rw [vfMidFirstBadAnchoredCoDivExcess_eq_two_product_sub_total,
    vfMidFirstBadNormalizedProduct_eq_upperActive_sub_squarefulRestoring hR]
  unfold vfMidFirstBadQuadraticAnchorSlack
  ring

/-- Lower-sign source identity.  The prime restoring term stays inside the
exact target; the stronger lower-source-only half bound is not required. -/
theorem vfMidFirstBadAnchoredCoDivExcess_eq_lower_restoring_slack
    {R : ℕ} (hR : 3 ≤ R) :
    vfMidFirstBadAnchoredCoDivExcess R =
      (2 * vfMidLowerFirstBadSourceBill R +
        2 * ((2 : ℝ) * vfMidSyntheticRadialScale R) ^ 2 -
        vfMidFirstBadZeroTargetTotalMass R) +
      2 * vfMidOneBlockPrimeSeatCharge R *
        (-2 * vfMidActualPrimeEndpointDefect (R + 1) -
          vfMidOneBlockPrimeSeatCharge R) -
      2 * vfMidFirstBadQuadraticAnchorSlack (2 : ℝ) R := by
  rw [vfMidFirstBadAnchoredCoDivExcess_eq_two_product_sub_total,
    vfMidFirstBadNormalizedProduct_eq_lowerComposite_add_primeRestoring hR]
  unfold vfMidFirstBadQuadraticAnchorSlack
  ring

/-- The upper restoring/anchor-slack sector is nonpositive at a first-bad
successor.  Here `hfirst` is consumed by the prior-good anchor theorem. -/
theorem vfMidFirstBadUpperRestoringAnchorSlack_nonpos
    {R : ℕ} (hR : 3 ≤ R)
    (hfirst : VFMidActualPrimeFirstBadAt (2 : ℝ) (R + 1))
    (hB : 0 ≤ vfMidActualPrimeEndpointDefect (R + 1)) :
    -(2 * vfMidOneBlockProcessedSquarefulCharge R *
        (2 * vfMidActualPrimeEndpointDefect (R + 1) +
          vfMidOneBlockProcessedSquarefulCharge R)) -
      2 * vfMidFirstBadQuadraticAnchorSlack (2 : ℝ) R ≤ 0 := by
  have hslack := vfMidActualPrimeFirstBadAt_succ_anchorEnergySlack_nonneg
    hfirst (by omega : 2 ≤ R)
  have hQ := vfMidOneBlockProcessedSquarefulCharge_nonneg R (by omega : 2 ≤ R)
  have hfactor : 0 ≤ 2 * vfMidActualPrimeEndpointDefect (R + 1) +
      vfMidOneBlockProcessedSquarefulCharge R := by linarith
  have hrestore := mul_nonneg hQ hfactor
  nlinarith

/-- The lower restoring/anchor-slack sector is nonpositive at a first-bad
successor.  The prime packet is retained, including its interaction with the
actual next endpoint; it is not discarded before the source is assembled. -/
theorem vfMidFirstBadLowerRestoringAnchorSlack_nonpos
    {R : ℕ} (hR : 3 ≤ R)
    (hfirst : VFMidActualPrimeFirstBadAt (2 : ℝ) (R + 1))
    (hB : vfMidActualPrimeEndpointDefect (R + 1) ≤ 0) :
    2 * vfMidOneBlockPrimeSeatCharge R *
        (-2 * vfMidActualPrimeEndpointDefect (R + 1) -
          vfMidOneBlockPrimeSeatCharge R) -
      2 * vfMidFirstBadQuadraticAnchorSlack (2 : ℝ) R ≤ 0 := by
  have hslack := vfMidActualPrimeFirstBadAt_succ_anchorEnergySlack_nonneg
    hfirst (by omega : 2 ≤ R)
  have hP := vfMidOneBlockPrimeSeatCharge_nonpos R hR
  have hfactor : 0 ≤ -2 * vfMidActualPrimeEndpointDefect (R + 1) -
      vfMidOneBlockPrimeSeatCharge R := by linarith
  have hrestore := mul_nonpos_of_nonpos_of_nonneg hP hfactor
  nlinarith

end RHLean.Analysis

