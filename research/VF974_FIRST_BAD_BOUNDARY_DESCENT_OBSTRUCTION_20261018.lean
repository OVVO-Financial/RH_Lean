import Mathlib
import «research.SQUARE_BLOCK_EULER_ANCESTRY_COVARIANCE_20261017»
import «research.VF_MID_FIRST_BAD_EXACT_BUDGET_CLOSE»
import «research.VF_MID_FIRST_BAD_FINAL_AGGREGATE_CONTRACTION»

/-!
# #974 -> #915: source-admission obstruction and exact boundary pressure

This file records what is independently provable from the REAL original VF
first-bad carrier after the new fixed-square Möbius parity formalization.

1. The direct cofactor of a current-block high-prime extension lies STRICTLY
   below the lower square of the original half-run R/2+1..R.  An arithmetic
   sign reversal at that cofactor is NOT a legal already-paid historical VF
   occurrence.  The compressed D_A anchor must be restored and accounted for.
2. Two physical composites at R=18 have opposite Möbius signs but identical
   positive original VF charges.  Möbius parity is not a sign reversal of
   the original VF seat field.
3. The previously compiled exact first-bad boundary identity is sharpened
   into an explicit 2*UPM - 6*LPM formula, retaining the global residual.
   Under a hypothetical first bad, the residual plus positive boundary
   MUST exceed the negative payment.  This is a necessary condition,
   NOT an arithmetic upper bound, descent selector, or RH proof.
4. A purely algebraic dominance test shows why local current-seat payment
   cannot be assumed once the compressed historical anchor overwhelms its
   current block.  No expansion of the historical absolute norm is allowed.

The still-open result is an occurrence-faithful, quantitative historical
return / contiguous CHILD-RUN estimate preserving the anchored denominator.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

open RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- First-bad #915 half-run begins at this square index. -/
def vf974HalfRunStart (R : ℕ) : ℕ := R / 2 + 1

/-- The entire direct high-prime cofactor range lies BELOW the first
historical square.  This is strict even at the first valid R=8. -/
theorem vf974_root_lt_halfRunStart_square
    {R : ℕ} (hR : 8 ≤ R) :
    R < (vf974HalfRunStart R) ^ 2 := by
  unfold vf974HalfRunStart
  have hdiv : 0 < R / 2 := by omega
  have hRle : R ≤ 2 * (R / 2) + 1 := by omega
  have hsq : 0 < (R / 2) ^ 2 := pow_pos hdiv 2
  nlinarith

/-- A high-prime sign-reversing parent from the current physical square
block is below the ENTIRE original historical [A,R+1) VF source. -/
theorem vf974_highPrimeCofactor_lt_originalHalfRun
    {R n p : ℕ} (hR : 8 ≤ R)
    (hn : n ∈ canonicalSquareBlock R)
    (hp : R < p) (hpd : p ∣ n) :
    n / p < (vf974HalfRunStart R) ^ 2 := by
  exact lt_of_le_of_lt
    (squareBlock_highPrimeCofactor_le hn hp hpd)
    (vf974_root_lt_halfRunStart_square hR)

/-- No direct cofactor parent is a site of ANY square block in the original
uncompressed half-run.  This forbids spending it as an independent current
or historical returned-parent occurrence without explicit anchor transport. -/
theorem vf974_highPrimeCofactor_not_in_originalHistoricalBlock
    {R n p r : ℕ} (hR : 8 ≤ R)
    (hn : n ∈ canonicalSquareBlock R)
    (hp : R < p) (hpd : p ∣ n)
    (hr : vf974HalfRunStart R ≤ r) :
    n / p ∉ canonicalSquareBlock r := by
  intro hmem
  have hlow : r ^ 2 ≤ n / p :=
    (Finset.mem_Ico.mp hmem).1
  have hsquares :
      (vf974HalfRunStart R) ^ 2 ≤ r ^ 2 :=
    Nat.pow_le_pow_left hr 2
  have hstrict := vf974_highPrimeCofactor_lt_originalHalfRun
    hR hn hp hpd
  omega

/-- At R=18 the complete square-wheel carrier contains opposite actual
Möbius signs on genuine high-prime composites, while original positive
VF-minus-prime charges AGREE.  Neither source sign nor admission transports
automatically along #974's Möbius parity involution. -/
theorem vf974_oppositeMoebius_sameVFCharge_at_eighteen :
    μ (327 : ℕ) = (1 : ℤ) ∧
    μ (345 : ℕ) = (-1 : ℤ) ∧
    vfMidOddSignedSeatCharge 18 327 =
      vfMidOddSignedSeatCharge 18 345 := by
  have hmu3 : μ (3 : ℕ) = (-1 : ℤ) :=
    ArithmeticFunction.moebius_apply_prime (by norm_num)
  have hmu15 : μ (15 : ℕ) = (1 : ℤ) := by
    have hflip := highPrimeCofactor_sign_reversal
      (R := 3) (p := 5) (c := 3)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    calc
      μ (15 : ℕ) = μ (5 * 3) := by norm_num
      _ = -μ 3 := hflip
      _ = 1 := by rw [hmu3]; norm_num
  constructor
  · have hflip := highPrimeCofactor_sign_reversal
      (R := 18) (p := 109) (c := 3)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    calc
      μ (327 : ℕ) = μ (109 * 3) := by norm_num
      _ = -μ 3 := hflip
      _ = 1 := by rw [hmu3]; norm_num
  · constructor
    · have hflip := highPrimeCofactor_sign_reversal
        (R := 18) (p := 23) (c := 15)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      calc
        μ (345 : ℕ) = μ (23 * 15) := by norm_num
        _ = -μ 15 := hflip
        _ = -1 := by rw [hmu15]
    · rw [vfMidOddSignedSeatCharge_of_not_prime 18 327 (by norm_num),
        vfMidOddSignedSeatCharge_of_not_prime 18 345 (by norm_num)]

/-- Exact POSITIVE boundary mass represented without a single lost atom:
(H+B)/2, where B and H are the previously compiled original-source signed
and ABSOLUTE three-boundary Fubini sums, on identical physical occurrences. -/
def vf974BoundaryUpperMass (R : ℕ) : ℝ :=
  (vfMidActiveThreeBoundaryAbsMass R +
    vfMidActiveThreeBoundaryMass R) / 2

/-- Exact NEGATIVE boundary magnitude represented on the identical carrier:
(H-B)/2.  These are not decompressed historical source masses. -/
def vf974BoundaryLowerMass (R : ℕ) : ℝ :=
  (vfMidActiveThreeBoundaryAbsMass R -
    vfMidActiveThreeBoundaryMass R) / 2

/-- Original #915 anchored Co/Div excess AFTER all completed legal parent
cancellations.  Only the quarantined G residual and the THREE original
clipped boundary sectors survive.  A positive atom costs +2z and a negative
atom contributes -6|z|; the untouched anchor is NEVER dropped. -/
theorem vf974_firstBadExcess_eq_residual_add_twoUpper_sub_sixLower
    {R : ℕ} (hR : 3 ≤ R) :
    vfMidFirstBadAnchoredCoDivExcess R =
      vfMidActiveGlobalResidualExcess R +
        2 * vf974BoundaryUpperMass R -
        6 * vf974BoundaryLowerMass R := by
  rw [vfMidFirstBadAnchoredCoDivExcess_eq_activeResidual_add_fourBoundary_sub_heat hR]
  unfold vf974BoundaryUpperMass vf974BoundaryLowerMass
  ring

/-- Any hypothetical genuine first bad forces a sharp positive unmatched
pressure in the ORIGINAL compressed norm.  The entire G residual is retained:
this theorem does NOT falsely infer a positive boundary without paying G. -/
theorem vf974_firstBad_forces_positive_unmatched_boundary_pressure
    {R : ℕ} (hR : 8 ≤ R)
    (hfirst : VFMidActualPrimeFirstBadAt (2 : ℝ) (R + 1)) :
    6 * vf974BoundaryLowerMass R <
      vfMidActiveGlobalResidualExcess R +
        2 * vf974BoundaryUpperMass R := by
  have hnormalized :=
    vfMidActualPrimeFirstBadAt_two_succ_nnsNormalized_gt_half hR hfirst
  have htotal :=
    vfMidFirstBadZeroTargetTotalMass_pos_of_firstBad hR hfirst
  have hstrict :
      (1 / 2 : ℝ) * vfMidFirstBadZeroTargetTotalMass R <
      vfMidFirstBadNNSNormalizedCovariance R *
        vfMidFirstBadZeroTargetTotalMass R :=
    mul_lt_mul_of_pos_right hnormalized htotal
  have hexcess : 0 < vfMidFirstBadAnchoredCoDivExcess R := by
    rw [vfMidFirstBadAnchoredCoDivExcess_eq_two_product_sub_total]
    linarith
  rw [vf974_firstBadExcess_eq_residual_add_twoUpper_sub_sixLower
    (by omega : 3 ≤ R)] at hexcess
  linarith

/-- Pure algebra: when the compressed historical anchor is more than six
times the current TOTAL absolute source mass, the original half-scale
normalized gate FAILS for every permitted current sign configuration.
This explains why no local sign-flip proof can dispense with nonlocal
history/anchor compensation.  No arithmetic assumption is used. -/
theorem vf974_halfGate_fails_of_anchor_dominates
    (D X T : ℝ) (hT : 0 ≤ T) (hX : |X| ≤ T)
    (hD : 6 * T < |D|) :
    (|D| + T) ^ 2 < 2 * (D - X) ^ 2 := by
  have htri : |D| ≤ |D - X| + |X| := by
    calc
      |D| = |(D - X) + X| := by congr 1; ring
      _ ≤ |D - X| + |X| := abs_add_le _ _
  have hfloor : |D| - T ≤ |D - X| := by linarith
  have hnonneg : 0 ≤ |D| - T := by linarith [abs_nonneg D]
  have hprod :
      0 ≤ (|D - X| - (|D| - T)) *
        (|D - X| + (|D| - T)) := by
    apply mul_nonneg <;> linarith [abs_nonneg (D-X)]
  have hsq : (|D| - T) ^ 2 ≤ (D - X) ^ 2 := by
    nlinarith [hprod, sq_abs (D - X)]
  have hdom : 0 < |D| * (|D| - 6 * T) := by
    apply mul_pos <;> linarith [abs_nonneg D]
  have hclose :
      (|D| + T) ^ 2 < 2 * (|D| - T) ^ 2 := by
    nlinarith [hdom, sq_nonneg T]
  nlinarith

end RHLean.Analysis

#print axioms RHLean.Analysis.vf974_root_lt_halfRunStart_square
#print axioms RHLean.Analysis.vf974_highPrimeCofactor_not_in_originalHistoricalBlock
#print axioms RHLean.Analysis.vf974_oppositeMoebius_sameVFCharge_at_eighteen
#print axioms RHLean.Analysis.vf974_firstBad_forces_positive_unmatched_boundary_pressure
#print axioms RHLean.Analysis.vf974_halfGate_fails_of_anchor_dominates
