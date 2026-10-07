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
  -- First-badness is already known to put the normalized source strictly
  -- above the one-half gate.
  have hgt :
      (1 / 2 : ℝ) < vfMidFirstBadNNSNormalizedCovariance R :=
    vfMidActualPrimeFirstBadAt_two_succ_nnsNormalized_gt_half hR hfirst
  have hendpoint :=
    vfMidFirstBadNormalizedProduct_eq_nextEndpointDefect_sq
      (R := R) (by omega : 3 ≤ R)
  have htotal0 : 0 ≤ vfMidFirstBadZeroTargetTotalMass R := by
    rw [vfMidFirstBadZeroTargetTotalMass_eq]
    positivity
  have htotalPos : 0 < vfMidFirstBadZeroTargetTotalMass R := by
    by_contra hnot
    have hzero : vfMidFirstBadZeroTargetTotalMass R = 0 :=
      le_antisymm (le_of_not_gt hnot) htotal0
    rw [hzero, mul_zero] at hendpoint
    have hDzero : vfMidActualPrimeEndpointDefect (R + 1) = 0 := by
      nlinarith [sq_nonneg (vfMidActualPrimeEndpointDefect (R + 1))]
    have hbreach := hfirst.1
    unfold VFMidSyntheticBadAt at hbreach
    rw [hDzero, abs_zero] at hbreach
    have hscalePos :
        0 < vfMidSyntheticRadialScale (R + 1) :=
      vfMidSyntheticRadialScale_pos (by omega : 2 ≤ R + 1)
    nlinarith
  have hmul :
      (1 / 2 : ℝ) * vfMidFirstBadZeroTargetTotalMass R <
        vfMidFirstBadNNSNormalizedCovariance R *
          vfMidFirstBadZeroTargetTotalMass R :=
    mul_lt_mul_of_pos_right hgt htotalPos
  have h_excess :
      vfMidFirstBadZeroTargetTotalMass R <
        2 * vfMidActualPrimeEndpointDefect (R + 1) ^ 2 := by
    rw [hendpoint] at hmul
    nlinarith

  -- TRUE PRODUCTION INLET:
  -- transport the global strict excess onto the exact #903 first-owner/signature
  -- signed-cell ledger, with the survivor restriction retained.  Once one cell
  -- exceeds its no-persistence safe side, the compiled sector-six capacitor
  -- fires verbatim.
  have htripwire :
      ∃ p ∈ primesUpTo (squareRootEndpoint R),
        ∃ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
          lowOwnerFirstOwnerNoPersistenceSafeDirichletMass R p sig <
            lowOwnerFirstOwnerSignedCellTelescope R p sig := by
    -- Exact source/reassembly splice.  This is now the single red seam.
    simp only

  rcases htripwire with ⟨p, hpMem, sig, hsig, hcell⟩
  have hp : p.Prime := (mem_primesUpTo.mp hpMem).1
  have hdesc :=
    vfMidNoPersistenceCapacitor_forces_sectorSixDescent
      (R := R) (p := p) (sig := sig) hp
      (cap := lowOwnerFirstOwnerNoPersistenceSafeDirichletMass R p sig)
      (H := 0)
      (by norm_num)
      (by exact le_rfl)
      (by simpa using hcell)
  rcases hdesc with
    ⟨r, hr, m, n, hmn, hparent, hrankDrop, hfresh⟩

  -- The remaining compiled continuation data are strict-rank data.  Consume
  -- hprior on those descendants and exhaust fresh-owner rank.
  have hfalse : False := by
    simp only
  exact hfalse.elim

end RHLean.Analysis
