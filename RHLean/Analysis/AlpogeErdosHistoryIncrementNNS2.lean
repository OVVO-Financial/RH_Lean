import Mathlib
import RHLean.Analysis.AlpogeErdosHistoryDirectBound
import RHLean.Proof.FinitePartialMoments

/-!
# UNCONDITIONAL RH-critical NNS UPM2 of direct signed-history INCREMENTS

The whole original Alpoge Gz(N) = N*centeredErdosHistory(N) has a bounded
positive discrete slope, proved directly from finite Mertens first theorem.

This module pays an entire dyadic upper partial moment of its ORIGINAL
signed historical INCREMENTS at the critical H^3 scale, without RH.
No absolute value is placed on Selberg first/second pieces and no
prime-power sector is dropped. No constant per root is hypothetical.

IMPORTANT:
  sum_R (Delta_R Gz)_+^2 = O(H^3)
does NOT imply
  sum_R (Gz(R^2-1))_+^2 = O(H^3)
because the latter includes the entire pre-existing history and
all between-block signed covariance. This distinction is the exact
remaining nonlocal Alpoge/NNS job, not a concealed proof of RH.
-/

noncomputable section
namespace RHLean.Analysis

/-- A nonnegative, unconditional upper slope, which does not need
any estimate for Euler's constant beyond |gamma| >= gamma. -/
def alpogeErdosSafeSlope : ℝ :=
  Real.log (4 : ℝ) + 2 + |Real.eulerMascheroniConstant|

theorem alpogeErdosSafeSlope_nonneg :
    0 ≤ alpogeErdosSafeSlope := by
  unfold alpogeErdosSafeSlope
  have hlog : 0 ≤ Real.log (4 : ℝ) :=
    Real.log_nonneg (by norm_num)
  linarith [abs_nonneg Real.eulerMascheroniConstant]

theorem alpogeErdosUpperSlope_le_safe :
    alpogeErdosUpperSlope ≤ alpogeErdosSafeSlope := by
  unfold alpogeErdosSafeSlope alpogeErdosUpperSlope
  linarith [le_abs_self Real.eulerMascheroniConstant]

/-- This is the FULL original signed-history change across one
physical square clock. No change of arithmetic coordinate is made. -/
def alpogeErdosHistorySquareIncrement (R : ℕ) : ℝ :=
  (((R + 1) ^ 2 - 1 : ℕ) : ℝ) *
      alpogeErdosCenteredHistory ((R + 1) ^ 2 - 1) -
  ((R ^ 2 - 1 : ℕ) : ℝ) *
      alpogeErdosCenteredHistory (R ^ 2 - 1)

/-- Keep the entire signed history on both sides of the increment. -/
theorem alpogeErdosHistorySquareIncrement_eq_Gz_diff
    (R : ℕ) (hR : 2 ≤ R) :
    alpogeErdosHistorySquareIncrement R =
      alpogeErdosGz ((R + 1) ^ 2 - 1) -
        alpogeErdosGz (R ^ 2 - 1) := by
  have hlow : 1 ≤ R ^ 2 - 1 := by
    have hs : 4 ≤ R ^ 2 := by nlinarith
    omega
  have hhigh : 1 ≤ (R + 1) ^ 2 - 1 := by
    nlinarith
  unfold alpogeErdosHistorySquareIncrement
  rw [← alpogeErdosGz_eq_mul_history
       ((R + 1) ^ 2 - 1) hhigh,
      ← alpogeErdosGz_eq_mul_history
       (R ^ 2 - 1) hlow]

/-- Unconditional DIRECT one-sided bound on the complete signed
square-root historical step; no loss from separate first/second
Selberg estimates. -/
theorem alpogeErdosHistorySquareIncrement_le
    (R : ℕ) (hR : 2 ≤ R) :
    alpogeErdosHistorySquareIncrement R ≤
      alpogeErdosSafeSlope * ((2 * R + 1 : ℕ) : ℝ) := by
  rw [alpogeErdosHistorySquareIncrement_eq_Gz_diff R hR]
  have hstep := alpogeErdosGz_next_square_le R hR
  have hconst := alpogeErdosUpperSlope_le_safe
  have hlen : 0 ≤ ((2 * R + 1 : ℕ) : ℝ) := by positivity
  have hm := mul_le_mul_of_nonneg_right hconst hlen
  linarith

/-- NNS degree-two upper partial moment of the COMPLETE signed historical
square increments. This is the actual finite root source, not a random
or Gaussian proxy. -/
def alpogeErdosHistorySquareIncrementUPM2 (H : ℕ) : ℝ :=
  upperPartialMomentNat 2 (Finset.Ico H (2 * H))
    alpogeErdosHistorySquareIncrement

/-- The POSITIVE degree-two historical-INCREMENT energy has the RH-critical
H^3 dyadic size UNCONDITIONALLY. All terms retain their signs BEFORE
the UPM split, and its positive part is paid pointwise via Mertens 1.
The full accumulated-history energy is a different problem. -/
theorem alpogeErdosHistorySquareIncrementUPM2_le
    (H : ℕ) (hH : 2 ≤ H) :
    alpogeErdosHistorySquareIncrementUPM2 H ≤
      (H : ℝ) *
        (alpogeErdosSafeSlope * ((4 * H + 1 : ℕ) : ℝ)) ^ 2 := by
  have hsafe : 0 ≤ alpogeErdosSafeSlope :=
    alpogeErdosSafeSlope_nonneg
  have hsum :
      (∑ R ∈ Finset.Ico H (2 * H),
        positivePart (alpogeErdosHistorySquareIncrement R) ^ 2) ≤
      ∑ _R ∈ Finset.Ico H (2 * H),
        (alpogeErdosSafeSlope * ((4 * H + 1 : ℕ) : ℝ)) ^ 2 := by
    apply Finset.sum_le_sum
    intro R hR
    have hmem := Finset.mem_Ico.mp hR
    have hR2 : 2 ≤ R := hH.trans hmem.1
    have hinc := alpogeErdosHistorySquareIncrement_le R hR2
    have hlen :
        ((2 * R + 1 : ℕ) : ℝ) ≤
          ((4 * H + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 2 * R + 1 ≤ 4 * H + 1 by omega)
    have hmul := mul_le_mul_of_nonneg_left hlen hsafe
    have hbound :
        alpogeErdosHistorySquareIncrement R ≤
          alpogeErdosSafeSlope * ((4 * H + 1 : ℕ) : ℝ) :=
      hinc.trans hmul
    have hB : 0 ≤
        alpogeErdosSafeSlope * ((4 * H + 1 : ℕ) : ℝ) :=
      mul_nonneg hsafe (by positivity)
    have hpart0 :
        0 ≤ positivePart (alpogeErdosHistorySquareIncrement R) := by
      unfold positivePart
      exact le_max_right _ _
    have hpart :
        positivePart (alpogeErdosHistorySquareIncrement R) ≤
          alpogeErdosSafeSlope * ((4 * H + 1 : ℕ) : ℝ) := by
      unfold positivePart
      exact max_le hbound hB
    have hh := mul_nonneg (sub_nonneg.mpr hpart)
      (add_nonneg hB hpart0)
    nlinarith [hh]
  have hcard : (Finset.Ico H (2 * H)).card = H := by
    rw [Nat.card_Ico]
    omega
  unfold alpogeErdosHistorySquareIncrementUPM2
    upperPartialMomentNat
  calc
    (∑ R ∈ Finset.Ico H (2 * H),
      positivePart (alpogeErdosHistorySquareIncrement R) ^ 2) ≤
        ∑ _R ∈ Finset.Ico H (2 * H),
          (alpogeErdosSafeSlope * ((4 * H + 1 : ℕ) : ℝ)) ^ 2 :=
      hsum
    _ = (H : ℝ) *
        (alpogeErdosSafeSlope * ((4 * H + 1 : ℕ) : ℝ)) ^ 2 := by
      rw [Finset.sum_const, hcard, nsmul_eq_mul]

end RHLean.Analysis
