import Mathlib
import «research.ZERO_TARGET_PARTIAL_MOMENT_COVARIANCE»
import «research.VF_MID_FIRST_BAD_HISTORY_COMPRESSION»
import «research.VF_MID_FIRST_BAD_NORMALIZED_PARTIAL_MOMENT»

/-!
# Exact restoration of the compressed historical NNS norm (#915)

The historical seat signs DO cancel exactly in D_R. A decompressed NNS
denominator, however, is *not* the source denominator used by #915.
This module proves the EXACT RESTORING PRICE, directly on the already
compiled original physical historical seats, with NO invented parents:

  M_expanded^2 - M_original^2
    = 4 * U_history * L_history
      + 2 * CurrentAbs *
          (U_history + L_history - |U_history - L_history|).

The enormous "compression leak" is not unaccounted random error: its
first component is exactly the historical opposite-sign UPM/LPM
quadratic interaction. The second is its precise coupling to the
original current-block absolute mass. Restoring these pieces is
compulsory whenever historical pairs are decompressed.

This is an exact identity, not an independent signed arithmetic estimate;
it does NOT prove the first-bad payment or RH.
-/

noncomputable section
open scoped BigOperators
namespace RHLean.Analysis
open RHLean.Arithmetic RHLean.Proof
open RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Upper partial moment of actual history: the earlier anchor and ALL
genuine historical odd seats. There are no fictitious stripped parents. -/
def vfMid915HistoryUpper (A R : ℕ) : ℝ :=
  zeroTargetUpperPart (-vfMidActualPrimeEndpointDefect A) +
    ∑ r ∈ Finset.Ico A R, ∑ n ∈ vfMidOddCandidateSeats r,
      zeroTargetUpperPart (vfMidOddSignedSeatCharge r n)

/-- Lower partial moment on exactly the SAME historical carrier. -/
def vfMid915HistoryLower (A R : ℕ) : ℝ :=
  zeroTargetLowerPart (-vfMidActualPrimeEndpointDefect A) +
    ∑ r ∈ Finset.Ico A R, ∑ n ∈ vfMidOddCandidateSeats r,
      zeroTargetLowerPart (vfMidOddSignedSeatCharge r n)

/-- Original historical total absolute mass BEFORE compression to D_R. -/
def vfMid915HistoryAbs (A R : ℕ) : ℝ :=
  |vfMidActualPrimeEndpointDefect A| +
    ∑ r ∈ Finset.Ico A R, ∑ n ∈ vfMidOddCandidateSeats r,
      |vfMidOddSignedSeatCharge r n|

/-- Original current-block absolute-mass contribution. -/
def vfMid915CurrentAbs (R : ℕ) : ℝ :=
  ∑ n ∈ vfMidOddCandidateSeats R, |vfMidOddSignedSeatCharge R n|

private theorem vfMid915Partial_add (x : ℝ) :
    zeroTargetUpperPart x + zeroTargetLowerPart x = |x| := by
  unfold zeroTargetUpperPart zeroTargetLowerPart
  ring

private theorem vfMid915HistorySums_sub (A R : ℕ) :
    (∑ r ∈ Finset.Ico A R, ∑ n ∈ vfMidOddCandidateSeats r,
       zeroTargetUpperPart (vfMidOddSignedSeatCharge r n)) -
    (∑ r ∈ Finset.Ico A R, ∑ n ∈ vfMidOddCandidateSeats r,
       zeroTargetLowerPart (vfMidOddSignedSeatCharge r n)) =
      vfMidOddRunSeatMass A R := by
  rw [← Finset.sum_sub_distrib]
  unfold vfMidOddRunSeatMass vfMidOddBlockSeatMass
  apply Finset.sum_congr rfl
  intro r _hr
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  exact zeroTargetUpperPart_sub_lowerPart _

private theorem vfMid915HistorySums_add (A R : ℕ) :
    (∑ r ∈ Finset.Ico A R, ∑ n ∈ vfMidOddCandidateSeats r,
       zeroTargetUpperPart (vfMidOddSignedSeatCharge r n)) +
    (∑ r ∈ Finset.Ico A R, ∑ n ∈ vfMidOddCandidateSeats r,
       zeroTargetLowerPart (vfMidOddSignedSeatCharge r n)) =
    ∑ r ∈ Finset.Ico A R, ∑ n ∈ vfMidOddCandidateSeats r,
       |vfMidOddSignedSeatCharge r n| := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  exact vfMid915Partial_add _

/-- Exact signed history compression (not just triangle inequality). -/
theorem vfMid915HistoryUpper_sub_lower_eq_neg_endpoint
    {A R : ℕ} (hA : 2 ≤ A) (hAR : A ≤ R) :
    vfMid915HistoryUpper A R - vfMid915HistoryLower A R =
      -vfMidActualPrimeEndpointDefect R := by
  unfold vfMid915HistoryUpper vfMid915HistoryLower
  have hs := vfMid915HistorySums_sub A R
  have ha := zeroTargetUpperPart_sub_lowerPart
    (-vfMidActualPrimeEndpointDefect A)
  have hd :=
    vfMidActualPrimeEndpointDefect_eq_anchor_sub_oddRunSeatMass hA hAR
  linarith

/-- Exact absolute history decomposition; no triangle bound. -/
theorem vfMid915HistoryUpper_add_lower_eq_abs
    (A R : ℕ) :
    vfMid915HistoryUpper A R + vfMid915HistoryLower A R =
      vfMid915HistoryAbs A R := by
  unfold vfMid915HistoryUpper vfMid915HistoryLower vfMid915HistoryAbs
  have hs := vfMid915HistorySums_add A R
  have ha := vfMid915Partial_add (-vfMidActualPrimeEndpointDefect A)
  rw [abs_neg] at ha
  simpa using (show
      (zeroTargetUpperPart (-vfMidActualPrimeEndpointDefect A) +
        (∑ r ∈ Finset.Ico A R, ∑ n ∈ vfMidOddCandidateSeats r,
          zeroTargetUpperPart (vfMidOddSignedSeatCharge r n))) +
      (zeroTargetLowerPart (-vfMidActualPrimeEndpointDefect A) +
        (∑ r ∈ Finset.Ico A R, ∑ n ∈ vfMidOddCandidateSeats r,
          zeroTargetLowerPart (vfMidOddSignedSeatCharge r n))) =
      |vfMidActualPrimeEndpointDefect A| +
        ∑ r ∈ Finset.Ico A R, ∑ n ∈ vfMidOddCandidateSeats r,
          |vfMidOddSignedSeatCharge r n| by linarith)

/-- Generic exact compensation identity: the new historical norm is
not independent payment; its squared increase is precisely paired
positive/negative historical mass plus its cross-current correction. -/
theorem vfMid915SquaredNormCompression_exact
    (U L C : ℝ) :
    (U + L + C) ^ 2 - (|U - L| + C) ^ 2 =
      4 * U * L + 2 * C * (U + L - |U - L|) := by
  nlinarith [sq_abs (U - L)]

/-- The EXACT difference of the two NNS quadratic excesses also has
the same mandatory restoring price, independent of the signed forcing T. -/
theorem vfMid915CoDivExcessCompression_exact
    (U L C T : ℝ) :
    (2 * (U - L + T) ^ 2 - (|U - L| + C) ^ 2) -
      (2 * (U - L + T) ^ 2 - (U + L + C) ^ 2) =
      4 * U * L + 2 * C * (U + L - |U - L|) := by
  nlinarith [vfMid915SquaredNormCompression_exact U L C]

/-- Source-welded restoration: the EXACT SQUARED norm increase when
one uncompresses the actual physical half-run [A,R) is fully
identified with the two historical NNS masses and original current
odd-seat denominator. No extra denominator capacity is available. -/
theorem vfMid915ActualHistoricalSquaredNormRestoration
    {A R : ℕ} (hA : 2 ≤ A) (hAR : A ≤ R) :
    (vfMid915HistoryAbs A R + vfMid915CurrentAbs R) ^ 2 -
        vfMidFirstBadZeroTargetTotalMass R =
      4 * vfMid915HistoryUpper A R * vfMid915HistoryLower A R +
        2 * vfMid915CurrentAbs R *
          (vfMid915HistoryUpper A R +
            vfMid915HistoryLower A R -
              |vfMid915HistoryUpper A R -
                vfMid915HistoryLower A R|) := by
  have hd := vfMid915HistoryUpper_sub_lower_eq_neg_endpoint hA hAR
  have hs := vfMid915HistoryUpper_add_lower_eq_abs A R
  rw [vfMidFirstBadZeroTargetTotalMass_eq]
  rw [← hs]
  have habs :
      |vfMidActualPrimeEndpointDefect R| =
        |vfMid915HistoryUpper A R -
          vfMid915HistoryLower A R| := by
    rw [hd]
    exact (abs_neg _).symm
  rw [habs]
  exact vfMid915SquaredNormCompression_exact
    (vfMid915HistoryUpper A R)
    (vfMid915HistoryLower A R)
    (vfMid915CurrentAbs R)

/-- Same exact historical restoration at the canonical first-bad half run,
stated without an hfirst premise; thus it is an unconditional arithmetic
normal form on the ACTUAL prime/composite VF carrier. -/
theorem vfMid915ActualHalfRunSquaredNormRestoration
    (R : ℕ) (hR : 8 ≤ R) :
    (vfMid915HistoryAbs (R / 2 + 1) R +
        vfMid915CurrentAbs R) ^ 2 -
      vfMidFirstBadZeroTargetTotalMass R =
      4 * vfMid915HistoryUpper (R / 2 + 1) R *
        vfMid915HistoryLower (R / 2 + 1) R +
      2 * vfMid915CurrentAbs R *
        (vfMid915HistoryUpper (R / 2 + 1) R +
          vfMid915HistoryLower (R / 2 + 1) R -
            |vfMid915HistoryUpper (R / 2 + 1) R -
              vfMid915HistoryLower (R / 2 + 1) R|) := by
  exact vfMid915ActualHistoricalSquaredNormRestoration
    (by omega : 2 ≤ R / 2 + 1)
    (by omega : R / 2 + 1 ≤ R)

end RHLean.Analysis
