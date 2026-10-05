import Mathlib
import «research.VF_MID_ONE_BLOCK_SOURCE_TO_RANK_INLET»
import «research.VF_MID_FIRST_BAD_TERMINAL_CONTRADICTION»

/-!
# VF first-bad global radial budget

This file isolates the exact quadratic budget consumed by the terminal
first-bad contradiction after the full one-block source-to-rank inlet.

The right-hand side of `hrank` is not merely a one-step radial gradient.
It is exactly

  local radial-square growth + accumulated quadratic anchor slack.

The anchor slack is nonnegative at a first-bad successor because the preceding
endpoint is prior-good.

The already-compiled endpoint-sign rectifiers are then used before any owner
energy comparison:

* upper escape: the squareful processed stream is favorable and may be dropped;
* lower escape: the prime stream is favorable and may be dropped.

Thus the remaining arithmetic work is precisely two sign-specific global
owner-tree packing inequalities on the literal one-sided VF sources.  No
remainder split, packet-to-scale inheritance, survivor-only square, or new
analytic hypothesis is introduced here.
-/

noncomputable section

namespace RHLean.Analysis

/-- Quadratic slack already accumulated at the prior-good anchor. -/
def vfMidFirstBadQuadraticAnchorSlack (K : ℝ) (R : ℕ) : ℝ :=
  (K * vfMidSyntheticRadialScale R) ^ 2 -
    vfMidActualPrimeEndpointDefect R ^ 2

/-- Pure one-step growth of the squared synthetic radial wall. -/
def vfMidFirstBadQuadraticRadialGrowth (K : ℝ) (R : ℕ) : ℝ :=
  (K * vfMidSyntheticRadialScale (R + 1)) ^ 2 -
    (K * vfMidSyntheticRadialScale R) ^ 2

/-- Exact anatomy of the terminal `hrank` budget. -/
theorem vfMidFirstBadTotalRadialBudget_eq_growth_add_anchorSlack
    (K : ℝ) (R : ℕ) :
    (K * vfMidSyntheticRadialScale (R + 1)) ^ 2 -
        vfMidActualPrimeEndpointDefect R ^ 2 =
      vfMidFirstBadQuadraticRadialGrowth K R +
        vfMidFirstBadQuadraticAnchorSlack K R := by
  unfold vfMidFirstBadQuadraticRadialGrowth
    vfMidFirstBadQuadraticAnchorSlack
  ring

/-- A first-bad successor has nonnegative quadratic slack at its prior anchor. -/
theorem vfMidActualPrimeFirstBadAt_succ_anchorEnergySlack_nonneg
    {K : ℝ} {R : ℕ}
    (hfirst : VFMidActualPrimeFirstBadAt K (R + 1))
    (hR : 2 ≤ R) :
    0 ≤ vfMidFirstBadQuadraticAnchorSlack K R := by
  have hprior :=
    vfMidActualPrimeFirstBadAt_prior_inside
      hfirst hR (by omega : R < R + 1)
  have hwall0 :
      0 ≤ K * vfMidSyntheticRadialScale R :=
    (abs_nonneg _).trans hprior
  have hsquare :=
    (sq_le_sq₀ (abs_nonneg _) hwall0).2 hprior
  have hsq :
      vfMidActualPrimeEndpointDefect R ^ 2 ≤
        (K * vfMidSyntheticRadialScale R) ^ 2 := by
    simpa [sq_abs] using hsquare
  unfold vfMidFirstBadQuadraticAnchorSlack
  linarith

/-- The complete #894 child-decompressed source is exactly active plus the
strict-descendant squareful cross packet. -/
theorem vfMidCorrelationEnergy_eq_activeChild_add_squarefulDescendant
    {R : ℕ} (hR : 3 ≤ R) :
    2 * vfMidSquareEndpointAccumulationCorrelation R +
        vfMidSquareBandError R ^ 2 =
      vfMidOneBlockActiveChildAffineBill R +
        vfMidOneBlockSquarefulChildDescendantCross R := by
  rw [vfMidCorrelationEnergy_eq_unifiedChildDecompressedLedger hR,
    vfMidOneBlockUnifiedChildDecompressedLedger_eq_active_add_squarefulDescendant hR]

/-- Canonical upper-sign one-sided source bill. -/
def vfMidUpperFirstBadSourceBill (R : ℕ) : ℝ :=
  (vfMidOneBlockPrimeSeatCharge R +
      vfMidOneBlockProcessedSquarefreeCharge R) ^ 2 -
    2 * vfMidActualPrimeEndpointDefect R *
      (vfMidOneBlockPrimeSeatCharge R +
        vfMidOneBlockProcessedSquarefreeCharge R)

/-- Canonical lower-sign one-sided source bill. -/
def vfMidLowerFirstBadSourceBill (R : ℕ) : ℝ :=
  (vfMidOneBlockProcessedSquarefreeCharge R +
      vfMidOneBlockProcessedSquarefulCharge R) ^ 2 -
    2 * vfMidActualPrimeEndpointDefect R *
      (vfMidOneBlockProcessedSquarefreeCharge R +
        vfMidOneBlockProcessedSquarefulCharge R)

/-- Upper endpoint sign removes the squareful restoring sector before the
global owner-tree comparison. -/
theorem vfMidCorrelationEnergy_le_upperFirstBadSourceBill
    {R : ℕ} (hR : 3 ≤ R)
    (hupper : 0 ≤ vfMidActualPrimeEndpointDefect (R + 1)) :
    2 * vfMidSquareEndpointAccumulationCorrelation R +
        vfMidSquareBandError R ^ 2 ≤
      vfMidUpperFirstBadSourceBill R := by
  simpa [vfMidUpperFirstBadSourceBill] using
    vfMidCorrelationEnergy_le_upperActive_of_endpoint_nonneg hR hupper

/-- Lower endpoint sign removes the prime restoring sector before the global
owner-tree comparison. -/
theorem vfMidCorrelationEnergy_le_lowerFirstBadSourceBill
    {R : ℕ} (hR : 3 ≤ R)
    (hlower : vfMidActualPrimeEndpointDefect (R + 1) ≤ 0) :
    2 * vfMidSquareEndpointAccumulationCorrelation R +
        vfMidSquareBandError R ^ 2 ≤
      vfMidLowerFirstBadSourceBill R := by
  simpa [vfMidLowerFirstBadSourceBill] using
    vfMidCorrelationEnergy_le_lowerComposite_of_endpoint_nonpos hR hlower

/-- **Direct terminal consumer for the two genuine global packing bounds.**

Once the upper and lower one-sided VF source bills are each proved to fit the
same first-bad radial budget, the already-compiled terminal contradiction
closes immediately.  The endpoint sign chooses which source bound is actually
used; the discarded physical sector has already been proved favorable.
-/
theorem vfMidActualPrimeFirstBadAt_succ_finalContraction_of_oneSidedRadialBudgets
    {K : ℝ} {R : ℕ}
    (hK : 0 ≤ K)
    (hR : 3 ≤ R)
    (hfirst : VFMidActualPrimeFirstBadAt K (R + 1))
    (hupperBudget :
      0 ≤ vfMidActualPrimeEndpointDefect (R + 1) →
        vfMidUpperFirstBadSourceBill R ≤
          (K * vfMidSyntheticRadialScale (R + 1)) ^ 2 -
            vfMidActualPrimeEndpointDefect R ^ 2)
    (hlowerBudget :
      vfMidActualPrimeEndpointDefect (R + 1) ≤ 0 →
        vfMidLowerFirstBadSourceBill R ≤
          (K * vfMidSyntheticRadialScale (R + 1)) ^ 2 -
            vfMidActualPrimeEndpointDefect R ^ 2) :
    False := by
  by_cases hsign : 0 ≤ vfMidActualPrimeEndpointDefect (R + 1)
  · have hsource :=
      vfMidCorrelationEnergy_le_upperFirstBadSourceBill hR hsign
    have hbudget := hupperBudget hsign
    have hrank :
        2 * vfMidSquareEndpointAccumulationCorrelation R +
            vfMidSquareBandError R ^ 2 ≤
          (K * vfMidSyntheticRadialScale (R + 1)) ^ 2 -
            vfMidActualPrimeEndpointDefect R ^ 2 :=
      hsource.trans hbudget
    exact
      vfMidActualPrimeFirstBadAt_succ_finalContraction
        hK hR hfirst hrank
  · have hsign' :
        vfMidActualPrimeEndpointDefect (R + 1) ≤ 0 :=
      le_of_not_ge hsign
    have hsource :=
      vfMidCorrelationEnergy_le_lowerFirstBadSourceBill hR hsign'
    have hbudget := hlowerBudget hsign'
    have hrank :
        2 * vfMidSquareEndpointAccumulationCorrelation R +
            vfMidSquareBandError R ^ 2 ≤
          (K * vfMidSyntheticRadialScale (R + 1)) ^ 2 -
            vfMidActualPrimeEndpointDefect R ^ 2 :=
      hsource.trans hbudget
    exact
      vfMidActualPrimeFirstBadAt_succ_finalContraction
        hK hR hfirst hrank

end RHLean.Analysis
