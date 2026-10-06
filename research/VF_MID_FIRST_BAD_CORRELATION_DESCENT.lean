import Mathlib
import «research.VF_MID_FIRST_BAD_RESTORING_DECOMPOSITION»
import «research.VF_MID_OWNER_FIBER_DEGREE_NORMALIZATION»
import «research.GLOBAL_RETURNED_CORE_GREATEST_OWNER_CONTINUATION»
import «research.VF_MID_FINAL_SIGNED_RANK_CONTRACTION»
import «research.ZERO_TARGET_MELLIN_COMPLETE_POST_ROOT_CUBES»

/-!
# First-bad correlation descent

Finite logic for the terminal normalized-covariance contradiction.

The signed observable is the zero-target excess `Co - Div`. Along a genuine
greatest-owner descent the Mobius pair excess reverses sign exactly. A scalar
retained on the raw parent is carried unchanged through that descent, so its
square does not alter the reversal. Terminal pairs and complete post-root
families remain nonpositive after the same retained scaling.

The finite averaging selector records the logical core: if a partitioned signed
numerator exceeds one half of its matching denominator, then some component
does too. Once the actual VF first-bad source is identified with the exhaustive
greatest-owner continuation, a positive global half-excess must therefore
select a strictly lower-rank recursive child unless it exits through a sector
already controlled by zero or by the one-half gate.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Retained scaling preserves the exact greatest-owner zero-target sign
reversal. -/
theorem descendingGreatestOwner_retained_zeroTargetExcess_flip
    {R p m n : ℕ} (hp : p.Prime)
    (hcross : (m, n) ∈ lowOwnerRevealedCrossPairCarrier R
      (lowOwnerRevealedPrimesAbove R p) p)
    (coefficient : ℝ) :
    let um := squarefreePrimeFamilyParent p m
    let un := squarefreePrimeFamilyParent p n
    coefficient ^ 2 * postRootZeroTargetPairExcess (m, n) =
      -(coefficient ^ 2 * postRootZeroTargetPairExcess (um, un)) := by
  have hdesc := descendingGreatestOwner_reciprocal_descent hp hcross
  dsimp only at hdesc ⊢
  rw [postRootZeroTargetPairExcess_eq_weight,
    postRootZeroTargetPairExcess_eq_weight,
    hdesc.2.1]
  ring

/-- Retaining an arbitrary raw-parent scalar cannot turn a terminal zero-target
sector positive. -/
theorem vfMidRetainedFinalRankTerminalPair_zeroTarget_nonpos
    {W : ℕ} {mn : ℕ × ℕ}
    (hmn : mn ∈ postRootCovarianceRemainderTerminalPairCarrier W)
    (coefficient : ℝ) :
    coefficient ^ 2 * postRootZeroTargetPairExcess mn ≤ 0 := by
  exact mul_nonpos_of_nonneg_of_nonpos
    (sq_nonneg coefficient)
    (vfMidFinalRankTerminalPair_zeroTarget_nonpos hmn)

/-- A constant retained scalar on one complete post-root family preserves its
nonpositivity. -/
theorem sum_zeroTargetMellinPhysicalSuperLcmFourCorner_postRoot_retained_nonpos
    {W p : ℕ} {r coefficient : ℝ}
    (hr0 : 0 ≤ r) (hr2 : r ≤ 2)
    (hp : p ∈ postRootPrimeFamilySet W) :
    coefficient ^ 2 *
      (∑ mn ∈ mertensPositivePhysicalPairCarrier (W / p),
        zeroTargetMellinPhysicalSuperLcmFourCorner W p r mn.1 mn.2) ≤ 0 := by
  exact mul_nonpos_of_nonneg_of_nonpos
    (sq_nonneg coefficient)
    (sum_zeroTargetMellinPhysicalSuperLcmFourCorner_postRoot_nonpos
      hr0 hr2 hp)

/-- **Finite half-excess selector.** If a finite numerator exceeds one half of
its matching denominator, some component has the same strict half-excess. -/
theorem exists_half_excess_of_sum_gt_half
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (num den : ι → ℝ)
    (h :
      (1 / 2 : ℝ) * (∑ i ∈ s, den i) <
        ∑ i ∈ s, num i) :
    ∃ i ∈ s, (1 / 2 : ℝ) * den i < num i := by
  by_contra hnone
  push_neg at hnone
  have hle :
      (∑ i ∈ s, num i) ≤
        ∑ i ∈ s, (1 / 2 : ℝ) * den i := by
    apply Finset.sum_le_sum
    intro i hi
    exact hnone i hi
  have hfactor :
      (∑ i ∈ s, (1 / 2 : ℝ) * den i) =
        (1 / 2 : ℝ) * (∑ i ∈ s, den i) := by
    rw [Finset.mul_sum]
  rw [hfactor] at hle
  linarith

/-- A nonpositive stopped sector with nonnegative denominator cannot be the
strict half-excess selector. -/
theorem not_half_excess_of_nonpos_of_den_nonneg
    {num den : ℝ} (hnum : num ≤ 0) (hden : 0 ≤ den) :
    ¬ ((1 / 2 : ℝ) * den < num) := by
  intro h
  nlinarith

/-- A sector already satisfying the half gate cannot be the strict selector. -/
theorem not_half_excess_of_le_half
    {num den : ℝ}
    (hhalf : num ≤ (1 / 2 : ℝ) * den) :
    ¬ ((1 / 2 : ℝ) * den < num) := by
  linarith

end RHLean.Analysis
