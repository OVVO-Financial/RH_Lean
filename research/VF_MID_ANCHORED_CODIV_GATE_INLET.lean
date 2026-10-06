import Mathlib
import «research.VF_MID_FIRST_BAD_NORMALIZED_PARTIAL_MOMENT»
import «research.VF_MID_GLOBAL_COMPLETED_GATE_PM_BUDGET»

/-!
# Anchored Co/Div inlet to the completed-gate budget

The #897 anchored NNS partial moment is the actual object consumed by the final
first-bad contradiction.  Before any owner/rank inequality is used, its signed
numerator is transported through the already-compiled #894 child-decompressed
source.

The resulting exact identity keeps three pieces visible:

* the Mobius-active squarefree affine bill;
* the complete squareful strict-descendant cross packet;
* the rigid historical anchor square D_R^2.

No owner labels are collapsed and no denominator is changed.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- **Exact anchored Co/Div to child-decompressed inlet.**

The signed anchored partial-moment excess is the full child-decompressed
first-bad source plus the rigid anchor square.  This equality is prior to every
reciprocal-energy or rank inequality. -/
theorem vfMidFirstBadAnchoredPartialExcess_eq_childDecompressed_add_anchorSq
    {R : ℕ} (hR : 3 ≤ R) :
    vfMidAnchoredZeroTargetCoPartialGram
        (vfMidOddCandidateSeats R)
        (vfMidOddSignedSeatCharge R)
        (vfMidActualPrimeEndpointDefect R) -
      vfMidAnchoredZeroTargetDivergentGram
        (vfMidOddCandidateSeats R)
        (vfMidOddSignedSeatCharge R)
        (vfMidActualPrimeEndpointDefect R) =
      vfMidOneBlockUnifiedChildDecompressedLedger R +
        vfMidActualPrimeEndpointDefect R ^ 2 := by
  have hpm :=
    vfMidCorrelationEnergy_eq_anchoredPartialExcess_sub_anchorSq hR
  have hchild :=
    vfMidCorrelationEnergy_eq_unifiedChildDecompressedLedger hR
  linarith

/-- **Exact authorized-bucket form of the anchored Co/Div numerator.**

After the lossless child reindex, the squarefree active source and squareful
strict-descendant source remain explicit, and the rigid anchor square is still
present. -/
theorem vfMidFirstBadAnchoredPartialExcess_eq_active_add_squareful_add_anchorSq
    {R : ℕ} (hR : 3 ≤ R) :
    vfMidAnchoredZeroTargetCoPartialGram
        (vfMidOddCandidateSeats R)
        (vfMidOddSignedSeatCharge R)
        (vfMidActualPrimeEndpointDefect R) -
      vfMidAnchoredZeroTargetDivergentGram
        (vfMidOddCandidateSeats R)
        (vfMidOddSignedSeatCharge R)
        (vfMidActualPrimeEndpointDefect R) =
      vfMidOneBlockActiveChildAffineBill R +
        vfMidOneBlockSquarefulChildDescendantCross R +
        vfMidActualPrimeEndpointDefect R ^ 2 := by
  rw [vfMidFirstBadAnchoredPartialExcess_eq_childDecompressed_add_anchorSq hR]
  rw [vfMidOneBlockUnifiedChildDecompressedLedger_eq_active_add_squarefulDescendant hR]
  ring

/-- **Normalized global anchored numerator in the same inlet currency.**

This is the exact numerator identity to be combined with the completed-gate
half budget.  It deliberately leaves the squareful bucket and anchor visible;
neither is silently inserted into the Mobius gate. -/
theorem vfMidFirstBadNNSNormalized_mul_total_eq_active_add_squareful_add_anchorSq
    {R : ℕ} (hR : 3 ≤ R) :
    vfMidFirstBadNNSNormalizedCovariance R *
        vfMidFirstBadZeroTargetTotalMass R =
      vfMidOneBlockActiveChildAffineBill R +
        vfMidOneBlockSquarefulChildDescendantCross R +
        vfMidActualPrimeEndpointDefect R ^ 2 := by
  have hnorm :=
    vfMidCorrelationEnergy_add_anchorSq_eq_nnsNormalized_mul_total hR
  have hsource :=
    vfMidCorrelationEnergy_eq_activeChild_add_squarefulDescendant hR
  nlinarith

end RHLean.Analysis
