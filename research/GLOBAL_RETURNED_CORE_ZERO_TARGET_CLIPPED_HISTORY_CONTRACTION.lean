import Mathlib
import «research.GLOBAL_RETURNED_CORE_GENERIC_GREATEST_OWNER_CONTRACTION»
import «research.GLOBAL_RETURNED_CORE_INHERITED_DETERMINISTIC_CANCELLATION»

/-!
# History-safe clipped zero-target contraction after #792

The remaining zero-target continuation has one genuinely positive local exit:
the companion-clipped owner face. Its critical coefficient already contains
one reciprocal owner factor (1/p) * (1 - 1/p).

For a nonzero parent (a,b), scale the reciprocal pair amplitude by h*a*b.
Then the physical parent product cancels the reciprocal denominator exactly.
The extra critical factor (1-1/p)^2 on a clipped child is at most one, so the
existing clipped greatest-owner congestion theorem yields the 79/162 bound.

This closes the positive clipped-exit channel in the raw zero-target currency.
It does not estimate the quadratic continuation; that continuation must remain
signed and telescope through the already-proved rank descent.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

def lowOwnerZeroTargetHistoryReciprocalScale
    (history : ℝ) (parent : ℕ × ℕ) : ℝ :=
  history * (parent.1 : ℝ) * (parent.2 : ℝ)

private theorem realMoebiusStep_sq_eq_one_history
    {n : ℕ} (hn : realMoebiusStep n ≠ 0) :
    realMoebiusStep n ^ 2 = 1 := by
  rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;>
    simp [realMoebiusStep, h] at hn ⊢

theorem lowOwnerZeroTargetHistoryParentEnergy_eq_rawExcessSq
    {history : ℝ} {parent : ℕ × ℕ}
    (haPos : 0 < parent.1) (hbPos : 0 < parent.2)
    (haMu : realMoebiusStep parent.1 ≠ 0)
    (hbMu : realMoebiusStep parent.2 ≠ 0) :
    lowOwnerRetainedCoefficientParentEnergy
        (lowOwnerZeroTargetHistoryReciprocalScale history parent) parent =
      history ^ 2 * postRootZeroTargetPairExcess parent ^ 2 := by
  have ha0 : (parent.1 : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt haPos)
  have hb0 : (parent.2 : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hbPos)
  have hma := realMoebiusStep_sq_eq_one_history haMu
  have hmb := realMoebiusStep_sq_eq_one_history hbMu
  unfold lowOwnerRetainedCoefficientParentEnergy
    lowOwnerZeroTargetHistoryReciprocalScale
  rw [postRootCovarianceReciprocalPairEnergy_eq_inv_product_sq_of_nonzero
    haMu hbMu]
  rw [postRootZeroTargetPairExcess_eq_weight]
  rw [mul_pow, hma, hmb]
  field_simp [ha0, hb0]
  ring

def lowOwnerZeroTargetHistoryClippedOutgoingEnergy
    (R : ℕ) (history : ℝ) (parent : ℕ × ℕ) : ℝ :=
  ∑ p ∈ primesUpTo (squareRootEndpoint R),
    if squareRootEndpoint R < p * parent.2 then
      ∑ child ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent p,
        (1 - 1 / (p : ℝ)) ^ 2 *
          lowOwnerRetainedCoefficientChildEnergy
            (lowOwnerZeroTargetHistoryReciprocalScale history parent) child
    else 0

private theorem critical_one_sub_reciprocal_sq_le_one
    {p : ℕ} (hp : p.Prime) :
    (1 - 1 / (p : ℝ)) ^ 2 ≤ 1 := by
  have hpRpos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hpRone : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_le
  have hinv0 : 0 ≤ (1 / (p : ℝ)) := by positivity
  have hinv1 : (1 / (p : ℝ)) ≤ 1 := by
    apply (div_le_iff₀ hpRpos).2
    nlinarith
  have hprod :
      0 ≤ (1 / (p : ℝ)) * (1 - 1 / (p : ℝ)) :=
    mul_nonneg hinv0 (sub_nonneg.mpr hinv1)
  nlinarith

theorem lowOwnerZeroTargetHistoryClippedOutgoingEnergy_le_reciprocal
    (R : ℕ) (history : ℝ) (parent : ℕ × ℕ) :
    lowOwnerZeroTargetHistoryClippedOutgoingEnergy R history parent ≤
      (lowOwnerZeroTargetHistoryReciprocalScale history parent) ^ 2 *
        lowOwnerGreatestOwnerClippedOutgoingEnergy R parent := by
  unfold lowOwnerZeroTargetHistoryClippedOutgoingEnergy
    lowOwnerGreatestOwnerClippedOutgoingEnergy
  calc
    (∑ p ∈ primesUpTo (squareRootEndpoint R),
      if squareRootEndpoint R < p * parent.2 then
        ∑ child ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent p,
          (1 - 1 / (p : ℝ)) ^ 2 *
            lowOwnerRetainedCoefficientChildEnergy
              (lowOwnerZeroTargetHistoryReciprocalScale history parent) child
      else 0) ≤
      ∑ p ∈ primesUpTo (squareRootEndpoint R),
        if squareRootEndpoint R < p * parent.2 then
          ∑ child ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent p,
            lowOwnerRetainedCoefficientChildEnergy
              (lowOwnerZeroTargetHistoryReciprocalScale history parent) child
        else 0 := by
      apply Finset.sum_le_sum
      intro p hpMem
      by_cases hclip : squareRootEndpoint R < p * parent.2
      · simp only [hclip, if_true]
        apply Finset.sum_le_sum
        intro child _hchild
        exact mul_le_mul_of_nonneg_right
          (critical_one_sub_reciprocal_sq_le_one
            (mem_primesUpTo.mp hpMem).1)
          (lowOwnerRetainedCoefficientChildEnergy_nonneg
            (lowOwnerZeroTargetHistoryReciprocalScale history parent) child)
      · simp [hclip]
    _ =
      (lowOwnerZeroTargetHistoryReciprocalScale history parent) ^ 2 *
        (∑ p ∈ primesUpTo (squareRootEndpoint R),
          if squareRootEndpoint R < p * parent.2 then
            ∑ child ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent p,
              postRootCovarianceReciprocalPairEnergy child
          else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _hp
      by_cases hclip : squareRootEndpoint R < p * parent.2
      · simp only [hclip, if_true]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro child _hchild
        unfold lowOwnerRetainedCoefficientChildEnergy
      · simp [hclip]
    _ = (lowOwnerZeroTargetHistoryReciprocalScale history parent) ^ 2 *
        lowOwnerGreatestOwnerClippedOutgoingEnergy R parent := by
      rfl

theorem lowOwnerZeroTargetHistoryClippedOutgoingEnergy_le_79_over_162
    {R : ℕ} {history : ℝ} {parent : ℕ × ℕ}
    (haPos : 0 < parent.1) (hbPos : 0 < parent.2)
    (haMu : realMoebiusStep parent.1 ≠ 0)
    (hbMu : realMoebiusStep parent.2 ≠ 0) :
    lowOwnerZeroTargetHistoryClippedOutgoingEnergy R history parent ≤
      (79 / 162 : ℝ) * history ^ 2 *
        postRootZeroTargetPairExcess parent ^ 2 := by
  have hraw :=
    lowOwnerZeroTargetHistoryClippedOutgoingEnergy_le_reciprocal
      R history parent
  have hcontract :=
    lowOwnerGreatestOwnerClippedOutgoingEnergy_le_79_over_162 R parent
  have hscale0 :
      0 ≤ (lowOwnerZeroTargetHistoryReciprocalScale history parent) ^ 2 :=
    sq_nonneg _
  have hscaled :
      (lowOwnerZeroTargetHistoryReciprocalScale history parent) ^ 2 *
          lowOwnerGreatestOwnerClippedOutgoingEnergy R parent ≤
        (lowOwnerZeroTargetHistoryReciprocalScale history parent) ^ 2 *
          ((79 / 162 : ℝ) *
            postRootCovarianceReciprocalPairEnergy parent) :=
    mul_le_mul_of_nonneg_left hcontract hscale0
  have hnorm :=
    lowOwnerZeroTargetHistoryParentEnergy_eq_rawExcessSq
      (history := history) (parent := parent)
      haPos hbPos haMu hbMu
  unfold lowOwnerRetainedCoefficientParentEnergy at hnorm
  calc
    lowOwnerZeroTargetHistoryClippedOutgoingEnergy R history parent ≤
        (lowOwnerZeroTargetHistoryReciprocalScale history parent) ^ 2 *
          lowOwnerGreatestOwnerClippedOutgoingEnergy R parent := hraw
    _ ≤ (lowOwnerZeroTargetHistoryReciprocalScale history parent) ^ 2 *
          ((79 / 162 : ℝ) *
            postRootCovarianceReciprocalPairEnergy parent) := hscaled
    _ = (79 / 162 : ℝ) * history ^ 2 *
          postRootZeroTargetPairExcess parent ^ 2 := by
      rw [mul_assoc]
      rw [← hnorm]
      unfold lowOwnerRetainedCoefficientParentEnergy
      ring

end RHLean.Proof
