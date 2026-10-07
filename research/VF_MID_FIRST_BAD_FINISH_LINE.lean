import Mathlib
import «research.VF_MID_FIRST_BAD_SOURCE_TO_SECTOR_SIX_INLET»

/-!
# Terminal actual-prime first-bad contradiction consumer

This file contains no owner-tree mathematics.

The strict `> 1/2` direction is banked in #906.  The `≤ 1/2` direction is
provided by the isolated source-to-sector-six inlet interface in #907.  Once
the production inlet theorem is discharged, the unconditional finish-line
theorem is obtained by applying this consumer to it.
-/

noncomputable section

namespace RHLean.Analysis

/-- **Three-line terminal contradiction from the isolated inlet.** -/
theorem vfMidActualPrimeFirstBadAt_two_succ_closed_of_sourceToSectorSixInlet
    (hinlet : VFMidFirstBadSourceToSectorSixInletStatement)
    {R : ℕ} (hR : 8 ≤ R)
    (hfirst : VFMidActualPrimeFirstBadAt (2 : ℝ) (R + 1)) :
    False := by
  have hgt :=
    vfMidActualPrimeFirstBadAt_two_succ_nnsNormalized_gt_half hR hfirst
  have hle :=
    vfMidFirstBadNNSNormalizedCovariance_le_half_of_sourceToSectorSixInlet
      hinlet hR hfirst
  linarith

end RHLean.Analysis
