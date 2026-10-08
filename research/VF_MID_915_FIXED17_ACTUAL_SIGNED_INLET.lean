import Mathlib
import «research.VF_MID_FIRST_BAD_HISTORY_COMPRESSION»

/-!
# #915: exact actual-prime VF source split through fixed 2..17 CRT wheel

The 2..17 wheel has Q=510510, phi(Q)=92160, and odd-seat survival
coefficient alpha=2*phi(Q)/Q=6144/17017. Its arithmetic signed departure
from alpha*R is periodic in the square-root index R; the exact-rational
CRT regression in scripts/vf_mid_915_fixed_owner_crt_history_regression.py
certifies a sharp all-run historical deviation of 46460/2431 (~19.11).
The CRT all-R proof is not formalized here: this Lean module proves the
EXACT original historical prime-source split without ANY analytical
assumption or hypothesized cancellation.

For R>=17, ALL actual square-block primes survive the fixed wheel.
Thus the literal nonnegative difference (fixed-wheel survivors -
actual primes) is the number removed by genuine later owners p>17.

In the ORIGINAL source, including the already-compressed historical anchor:

 D_B = D_A - sum_{A<=r<B}[
      VFblock_r - alpha*r - fixedWheelError_r
      + actualLatePrimeOwnerRemovals_r].

This is an unconditional, exact signed arithmetic identity; no new
independent absolute historical capacity is introduced. The 2..17
small-owner arithmetic part has a UNIFORM signed historical bound,
but the moving p>17 removal population still requires RH-scale
historical control. No hbalance sign is asserted.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof
attribute [local instance] Classical.propDecidable

def vfMid915FixedWheel17Alpha : ℝ :=
  6144 / 17017

/-- Exact full square-band survivor population after fixed low wheel. -/
def vfMid915FixedWheel17Supply (R : ℕ) : ℝ :=
  ((vfMidSquarePrefixWheelSurvivors 17 R).card : ℝ)

/-- Fixed-wheel square-window boundary discrepancy, NOT a prime error. -/
def vfMid915FixedWheel17SignedBoundary (R : ℕ) : ℝ :=
  vfMid915FixedWheel17Supply R - vfMid915FixedWheel17Alpha * (R : ℝ)

/-- Actual additional eliminations by the DISTINCT later prime owners p>17
on the same R-th square block. -/
def vfMid915ActualAfter17OwnerRemovals (R : ℕ) : ℝ :=
  vfMid915FixedWheel17Supply R - (vfMidIntegerBlockPrimeSupply R : ℝ)

/-- Pure FTA/wheel monotonicity: after-17 ACTUAL removals are nonnegative. -/
theorem vfMid915ActualAfter17OwnerRemovals_nonneg
    {R : ℕ} (hR : 17 ≤ R) :
    0 ≤ vfMid915ActualAfter17OwnerRemovals R := by
  have hcard :=
    vfMidIntegerBlockPrimeSupply_le_prefixWheelCard 17 R
      (by omega : 2 ≤ R) hR
  have hcast :
      (vfMidIntegerBlockPrimeSupply R : ℝ) ≤
        ((vfMidSquarePrefixWheelSurvivors 17 R).card : ℝ) := by
    exact_mod_cast hcard
  unfold vfMid915ActualAfter17OwnerRemovals vfMid915FixedWheel17Supply
  linarith

/-- EXACT physical signed block charge in deterministic VF mass + fixed CRT
boundary + residual actual high-owner removals. This begins on the literal
original VF parity-source, not on a new approximating function. -/
theorem vfMid915OddPhysicalSource_eq_fixed17_plus_late
    (R : ℕ) (hR : 17 ≤ R) :
    (∑ n ∈ vfMidOddCandidateSeats R,
        vfMidOddSignedSeatCharge R n) =
      vfMidBandMass R -
      vfMid915FixedWheel17Alpha * (R : ℝ) -
      vfMid915FixedWheel17SignedBoundary R +
      vfMid915ActualAfter17OwnerRemovals R := by
  have hblock := vfMidOddSignedSeatCharge_sum R
    (by omega : 2 ≤ R)
  rw [vfMidOddCompositeTrackingDefect_eq_neg_bandError R
    (by omega : 2 ≤ R)] at hblock
  unfold vfMidSquareBandError at hblock
  rw [vfMidSquareBandPrimes_card_eq_integerBlockPrimeSupply R] at hblock
  unfold vfMid915FixedWheel17SignedBoundary
    vfMid915FixedWheel17Supply vfMid915ActualAfter17OwnerRemovals
  linarith

/-- Full ACTUAL half-run signed inlet in fixed-wheel small-owner and late
prime-owner currency. The enormous earlier historical absolute norm is
NOT decompressed: its sign stays entirely in the scalar D_A. -/
theorem vfMid915ActualHistoricalDefect_eq_fixed17_plus_late
    {A B : ℕ} (hA : 17 ≤ A) (hAB : A ≤ B) :
    vfMidActualPrimeEndpointDefect B =
      vfMidActualPrimeEndpointDefect A -
        (∑ r ∈ Finset.Ico A B,
          (vfMidBandMass r -
          vfMid915FixedWheel17Alpha * (r : ℝ) -
          vfMid915FixedWheel17SignedBoundary r +
          vfMid915ActualAfter17OwnerRemovals r)) := by
  have hhistory :=
    vfMidActualPrimeEndpointDefect_eq_anchor_sub_oddRunSeatMass
      (by omega : 2 ≤ A) hAB
  rw [vfMidOddRunSeatMass_eq_sum_physicalSeats] at hhistory
  have hs :
      (∑ r ∈ Finset.Ico A B,
         ∑ n ∈ vfMidOddCandidateSeats r,
            vfMidOddSignedSeatCharge r n) =
      ∑ r ∈ Finset.Ico A B,
        (vfMidBandMass r -
          vfMid915FixedWheel17Alpha * (r : ℝ) -
          vfMid915FixedWheel17SignedBoundary r +
          vfMid915ActualAfter17OwnerRemovals r) := by
    apply Finset.sum_congr rfl
    intro r hr
    exact vfMid915OddPhysicalSource_eq_fixed17_plus_late
      r (hA.trans (Finset.mem_Ico.mp hr).1)
  rw [hs] at hhistory
  exact hhistory

/-- The #915 first-bad historical interval anchored at floor(R/2)+1:
all fixed 2..17 small-owner arithmetic is a signed CRT BOUNDARY;
all remaining prime-removal information is localized to real p>17
owners. No fake historical parent or enlarged original denominator. -/
theorem vfMid915FirstBadHalfRunDefect_eq_fixed17_plus_late
    {R : ℕ} (hR : 34 ≤ R) :
    vfMidActualPrimeEndpointDefect (R + 1) =
      vfMidActualPrimeEndpointDefect (R / 2 + 1) -
        (∑ r ∈ Finset.Ico (R / 2 + 1) (R + 1),
          (vfMidBandMass r -
          vfMid915FixedWheel17Alpha * (r : ℝ) -
          vfMid915FixedWheel17SignedBoundary r +
          vfMid915ActualAfter17OwnerRemovals r)) := by
  exact vfMid915ActualHistoricalDefect_eq_fixed17_plus_late
    (by omega : 17 ≤ R / 2 + 1)
    (by omega : R / 2 + 1 ≤ R + 1)

end RHLean.Analysis
