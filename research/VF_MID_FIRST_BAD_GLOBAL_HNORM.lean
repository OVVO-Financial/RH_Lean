import Mathlib
import «research.VF_MID_ANCHORED_CODIV_GATE_INLET»
import «research.VF_MID_GLOBAL_FIRST_BAD_RADIAL_BUDGET»

/-!
# Final first-bad global hnorm splice

This file is the equality-first terminal wiring layer above #899.

The first operation is to quarantine the restoring sectors *before* any owner
Fubini or reciprocal estimate is introduced.  The normalized anchored numerator
is kept as the exact product

  rho_R * T_R,

and rewritten in the two endpoint-sign branches as

  upper active source - squareful restoring + D_R^2,

or

  lower composite source + prime restoring + D_R^2.

Thus the anchor remains coupled to the complete one-block source while the
squareful/prime restoring packet is still explicit.  Only after these exact
normal forms are established is the favorable restoring sign dropped.

No new analytic hypothesis, carrier enlargement, or packet-to-scale
inheritance is introduced here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

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

/-- Once the endpoint is on the upper side, the exact squareful restoring
packet is nonpositive and may be dropped.  This is the first inequality in the
upper branch. -/
theorem vfMidFirstBadNormalizedProduct_le_upperActive_add_anchorSq
    {R : ℕ} (hR : 3 ≤ R)
    (hupper : 0 ≤ vfMidActualPrimeEndpointDefect (R + 1)) :
    vfMidFirstBadNNSNormalizedCovariance R *
        vfMidFirstBadZeroTargetTotalMass R ≤
      vfMidUpperFirstBadSourceBill R +
        vfMidActualPrimeEndpointDefect R ^ 2 := by
  rw [vfMidFirstBadNormalizedProduct_eq_upperActive_sub_squarefulRestoring hR]
  have hQ :=
    vfMidOneBlockProcessedSquarefulCharge_nonneg R (by omega : 2 ≤ R)
  nlinarith

/-- Once the endpoint is on the lower side, the exact prime restoring packet
is nonpositive and may be dropped.  This is the first inequality in the lower
branch. -/
theorem vfMidFirstBadNormalizedProduct_le_lowerComposite_add_anchorSq
    {R : ℕ} (hR : 3 ≤ R)
    (hlower : vfMidActualPrimeEndpointDefect (R + 1) ≤ 0) :
    vfMidFirstBadNNSNormalizedCovariance R *
        vfMidFirstBadZeroTargetTotalMass R ≤
      vfMidLowerFirstBadSourceBill R +
        vfMidActualPrimeEndpointDefect R ^ 2 := by
  rw [vfMidFirstBadNormalizedProduct_eq_lowerComposite_add_primeRestoring hR]
  have hP := vfMidOneBlockPrimeSeatCharge_nonpos R hR
  nlinarith

end RHLean.Analysis
