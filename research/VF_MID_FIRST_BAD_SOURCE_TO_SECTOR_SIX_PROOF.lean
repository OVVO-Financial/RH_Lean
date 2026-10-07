import Mathlib
import «research.VF_MID_FIRST_BAD_SOURCE_TO_SECTOR_SIX_INLET»
import «research.VF_MID_FIRST_BAD_LOWER_RUN_CAPACITOR»
import «research.VF_MID_CENTERED_GREATEST_OWNER_RANK_TELESCOPE»
import «research.VF_MID_ONE_BLOCK_SOURCE_TO_RANK_INLET»

/-!
# Production proof attempt: actual first-bad source -> sector six

This file is intentionally the only red proof surface in the stack.

The banked >1/2 direction lives in #906.
The compiled inlet interface lives in #907.
The terminal consumer lives in #908.

Only this theorem is allowed to remain open while iterating:
`vfMidFirstBadSourceToSectorSixInlet`.

No new analytic hypothesis may be introduced.  The proof must use the actual
first-bad prior-good wall plus the merged #903 no-persistence/sector-six
descent with the survivor restriction retained.
-/

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

attribute [local instance] Classical.propDecidable

theorem vfMidFirstBadSourceToSectorSixInlet :
    VFMidFirstBadSourceToSectorSixInletStatement := by
  intro R hR hfirst
  have hprior :
      ∀ S : ℕ, 2 ≤ S → S < R + 1 →
        |vfMidActualPrimeEndpointDefect S| ≤
          (2 : ℝ) * vfMidSyntheticRadialScale S := by
    intro S hS hSR
    exact vfMidActualPrimeFirstBadAt_prior_inside hfirst hS hSR
  have hrank :
      2 * vfMidSquareEndpointAccumulationCorrelation R +
          vfMidSquareBandError R ^ 2 ≤
        ((2 : ℝ) * vfMidSyntheticRadialScale (R + 1)) ^ 2 -
          vfMidActualPrimeEndpointDefect R ^ 2 := by
    -- SINGLE OPEN PRODUCTION SEAM:
    -- reassemble the actual first-bad source on the #903 signed-cell ledger,
    -- keep the survivor restriction through owner Fubini, send every unfunded
    -- excess into sector six, and exhaust strict fresh-owner rank using
    -- prior-good descendants.  No packet-to-child or unsigned enlargement.
    simp only
  have hfalse :
      False :=
    vfMidActualPrimeFirstBadAt_succ_finalContraction
      (K := (2 : ℝ)) (R := R) (by norm_num)
      (by omega : 3 ≤ R) hfirst hrank
  exact hfalse.elim

end RHLean.Analysis
