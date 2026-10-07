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
  have hsource :
      vfMidActualPrimeEndpointDefect (R + 1) =
        vfMidFirstBadDecompressedHistoricalSource R :=
    vfMidActualPrimeEndpointDefect_succ_eq_decompressedHistoricalSource hR
  -- FINISH-LINE INLET:
  -- place the literal source on the #903 signed-cell ledger, route every
  -- unfunded half-excess to sector six, and descend strict fresh-owner rank
  -- until the terminal nonpositive sector contradicts the excess.
  --
  -- The compiler goal below is intentionally left as the exact arithmetic
  -- inlet.  All future proof iterations happen here and nowhere else.
  rw [← hsource]

end RHLean.Analysis
