import Mathlib
import «research.VF_MID_FIRST_BAD_CORRELATION_DESCENT»
import «research.VF_MID_FIRST_BAD_LOWER_RUN_CAPACITOR»
import «research.VF_MID_CENTERED_GREATEST_OWNER_RANK_TELESCOPE»
import «research.VF_MID_FULL_AFFINE_PAIR_CLASSIFIER»

/-!
# Actual first-bad source to sector-six inlet

This module isolates the only open arithmetic splice after the banked
first-bad `> 1/2` direction and merged #903 no-persistence descent.

The historical source is kept in its literal decompressed coordinates.  The
single open production theorem to prove in this module is

`vfMidFirstBadSourceToSectorSixInlet`

with target `VFMidFirstBadSourceToSectorSixInletStatement`.

Everything below that target is consumer plumbing and is kernel-checked
independently.  No new analytic hypothesis should be added to the production
theorem: its proof must place the actual source onto the existing #903
signed-cell / sector-six ledger with the survivor restriction retained.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Literal historical source occurring in the former #900 terminal goal. -/
def vfMidFirstBadDecompressedHistoricalSource (R : ℕ) : ℝ :=
  vfMidActualPrimeEndpointDefect (R / 2 + 1) -
    vfMidFrozenAffineRunPhysicalCharge (R / 2 + 1) R -
    vfMidFrozenAffineBlockPhysicalCharge (R / 2 + 1) R

/-- The literal historical source is exactly the next endpoint defect. -/
theorem vfMidActualPrimeEndpointDefect_succ_eq_decompressedHistoricalSource
    {R : ℕ} (hR : 8 ≤ R) :
    vfMidActualPrimeEndpointDefect (R + 1) =
      vfMidFirstBadDecompressedHistoricalSource R := by
  let A : ℕ := R / 2 + 1
  have hA : 3 ≤ A := by
    dsimp [A]
    omega
  have hAR : A ≤ R := by
    dsimp [A]
    omega
  have hAB : A ≤ R + 1 := by omega
  have hBA : R + 1 ≤ 2 * A := by
    dsimp [A]
    omega
  have hdecomp :=
    vfMidActualPrimeEndpointDefect_eq_anchor_sub_frozenAffineRun
      (A := A) (B := R + 1) hA hAB hBA
  have hrun :=
    vfMidFrozenAffineRunPhysicalCharge_succ
      (A := A) (R := R) hAR
  rw [hrun] at hdecomp
  unfold vfMidFirstBadDecompressedHistoricalSource
  dsimp [A] at hdecomp ⊢
  linarith

/-- Exact arithmetic inlet still to be discharged from the merged #903
signed-cell / sector-six machinery.

This is deliberately the literal former line-1263 goal and nothing stronger.
The `hfirst` argument is retained because prior-good descendants are part of
the authorized #903 descent proof. -/
def VFMidFirstBadSourceToSectorSixInletStatement : Prop :=
  ∀ {R : ℕ}, 8 ≤ R →
    VFMidActualPrimeFirstBadAt (2 : ℝ) (R + 1) →
      2 * vfMidFirstBadDecompressedHistoricalSource R ^ 2 ≤
        vfMidFirstBadZeroTargetTotalMass R

/-- Exact Co/Div excess in the isolated historical-source coordinate. -/
theorem vfMidFirstBadAnchoredCoDivExcess_eq_decompressedHistoricalSource
    {R : ℕ} (hR : 8 ≤ R) :
    vfMidFirstBadAnchoredCoDivExcess R =
      2 * vfMidFirstBadDecompressedHistoricalSource R ^ 2 -
        vfMidFirstBadZeroTargetTotalMass R := by
  rw [vfMidFirstBadAnchoredCoDivExcess_eq_two_product_sub_total,
    vfMidFirstBadNormalizedProduct_eq_nextEndpointDefect_sq
      (by omega : 3 ≤ R),
    vfMidActualPrimeEndpointDefect_succ_eq_decompressedHistoricalSource hR]

/-- Once the single source-to-sector-six inlet is discharged, the normalized
first-bad coefficient is at most one half.  This consumer contains no remaining
owner-tree mathematics. -/
theorem vfMidFirstBadNNSNormalizedCovariance_le_half_of_sourceToSectorSixInlet
    (hinlet : VFMidFirstBadSourceToSectorSixInletStatement)
    {R : ℕ} (hR : 8 ≤ R)
    (hfirst : VFMidActualPrimeFirstBadAt (2 : ℝ) (R + 1)) :
    vfMidFirstBadNNSNormalizedCovariance R ≤ (1 / 2 : ℝ) := by
  have hsource := hinlet hR hfirst
  have hcodiv : vfMidFirstBadAnchoredCoDivExcess R ≤ 0 := by
    rw [vfMidFirstBadAnchoredCoDivExcess_eq_decompressedHistoricalSource hR]
    linarith
  unfold vfMidFirstBadAnchoredCoDivExcess at hcodiv
  unfold vfMidFirstBadNNSNormalizedCovariance
  unfold vfMidAnchoredZeroTargetNNSNormalizedCovariance
  by_cases hzero :
      vfMidAnchoredZeroTargetCoPartialGram
            (vfMidOddCandidateSeats R)
            (vfMidOddSignedSeatCharge R)
            (vfMidActualPrimeEndpointDefect R) +
          vfMidAnchoredZeroTargetDivergentGram
            (vfMidOddCandidateSeats R)
            (vfMidOddSignedSeatCharge R)
            (vfMidActualPrimeEndpointDefect R) = 0
  · unfold nnsZeroTargetNormalizedCovariance
    rw [if_pos hzero]
    norm_num
  · have hco :
        0 ≤ vfMidAnchoredZeroTargetCoPartialGram
          (vfMidOddCandidateSeats R)
          (vfMidOddSignedSeatCharge R)
          (vfMidActualPrimeEndpointDefect R) :=
      vfMidAnchoredZeroTargetCoPartialGram_nonneg _ _ _
    have hdiv :
        0 ≤ vfMidAnchoredZeroTargetDivergentGram
          (vfMidOddCandidateSeats R)
          (vfMidOddSignedSeatCharge R)
          (vfMidActualPrimeEndpointDefect R) :=
      vfMidAnchoredZeroTargetDivergentGram_nonneg _ _ _
    have hden :
        0 <
          vfMidAnchoredZeroTargetCoPartialGram
              (vfMidOddCandidateSeats R)
              (vfMidOddSignedSeatCharge R)
              (vfMidActualPrimeEndpointDefect R) +
            vfMidAnchoredZeroTargetDivergentGram
              (vfMidOddCandidateSeats R)
              (vfMidOddSignedSeatCharge R)
              (vfMidActualPrimeEndpointDefect R) :=
      lt_of_le_of_ne (add_nonneg hco hdiv) (Ne.symm hzero)
    unfold nnsZeroTargetNormalizedCovariance
    rw [if_neg hzero]
    apply (div_le_iff₀ hden).2
    linarith only [hcodiv]

end RHLean.Analysis
