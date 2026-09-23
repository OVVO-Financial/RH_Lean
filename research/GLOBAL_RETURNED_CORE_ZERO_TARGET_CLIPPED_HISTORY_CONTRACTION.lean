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
  simp only [mul_pow]
  rw [hma, hmb]
  field_simp [ha0, hb0]

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
        have hchild0 :
            0 ≤ lowOwnerRetainedCoefficientChildEnergy
              (lowOwnerZeroTargetHistoryReciprocalScale history parent) child := by
          exact mul_nonneg
            (sq_nonneg (lowOwnerZeroTargetHistoryReciprocalScale history parent))
            (postRootCovarianceReciprocalPairEnergy_nonneg child)
        simpa only [one_mul] using
          (mul_le_mul_of_nonneg_right
            (critical_one_sub_reciprocal_sq_le_one
              (mem_primesUpTo.mp hpMem).1)
            hchild0)
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
        rfl
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
    _ = (79 / 162 : ℝ) *
          ((lowOwnerZeroTargetHistoryReciprocalScale history parent) ^ 2 *
            postRootCovarianceReciprocalPairEnergy parent) := by ring
    _ = (79 / 162 : ℝ) * history ^ 2 *
          postRootZeroTargetPairExcess parent ^ 2 := by
      rw [hnorm]
      ring

/-! ## First-owner restricted contraction: 1/2 recursive, 1/4 clipped -/

private theorem lowOwnerRevealedPrimesAbove_reciprocalSquareBudget_le_quarter
    {R first : ℕ} (hfirst : first.Prime) :
    (∑ r ∈ lowOwnerRevealedPrimesAbove R first,
      (1 : ℝ) / (r : ℝ) ^ 2) ≤ 1 / 4 := by
  have hsub :
      lowOwnerRevealedPrimesAbove R first ⊆
        (primesUpTo (squareRootEndpoint R)).erase 2 := by
    intro r hr
    rcases Finset.mem_filter.mp hr with ⟨hrMem, hfirstR⟩
    have hne : r ≠ 2 := by
      have hfirst2 : 2 ≤ first := hfirst.two_le
      omega
    exact Finset.mem_erase.mpr ⟨hne, hrMem⟩
  calc
    (∑ r ∈ lowOwnerRevealedPrimesAbove R first,
      (1 : ℝ) / (r : ℝ) ^ 2) ≤
      ∑ r ∈ (primesUpTo (squareRootEndpoint R)).erase 2,
        (1 : ℝ) / (r : ℝ) ^ 2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsub
          intro r _hr _hnot
          positivity
    _ ≤ 1 / 4 :=
      oddPrimeOwnerReciprocalSquareBudgetReal_le_quarter
        (squareRootEndpoint R)

/-- Reciprocal outgoing energy restricted to genuine later owners of one
first-owner cell. -/
def lowOwnerGreatestOwnerAboveFirstReciprocalOutgoingEnergy
    (R first : ℕ) (parent : ℕ × ℕ) : ℝ :=
  ∑ r ∈ lowOwnerRevealedPrimesAbove R first,
    ∑ child ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent r,
      postRootCovarianceReciprocalPairEnergy child

/-- **Half contraction on the actual first-owner chronology.**

Every later owner is odd and each owner has at most two children. -/
theorem lowOwnerGreatestOwnerAboveFirstReciprocalOutgoingEnergy_le_half
    {R first : ℕ} (hfirst : first.Prime) (parent : ℕ × ℕ) :
    lowOwnerGreatestOwnerAboveFirstReciprocalOutgoingEnergy R first parent ≤
      (1 / 2 : ℝ) * postRootCovarianceReciprocalPairEnergy parent := by
  unfold lowOwnerGreatestOwnerAboveFirstReciprocalOutgoingEnergy
  calc
    (∑ r ∈ lowOwnerRevealedPrimesAbove R first,
      ∑ child ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent r,
        postRootCovarianceReciprocalPairEnergy child) =
      ∑ r ∈ lowOwnerRevealedPrimesAbove R first,
        (lowOwnerGreatestOwnerFixedParentChildMultiplicity R parent r : ℝ) /
          (r : ℝ) ^ 2 *
            postRootCovarianceReciprocalPairEnergy parent := by
        apply Finset.sum_congr rfl
        intro r hr
        have hrPrime : r.Prime :=
          (mem_primesUpTo.mp (Finset.mem_filter.mp hr).1).1
        exact sum_lowOwnerGreatestOwnerFixedParentChild_energy_eq
          hrPrime parent
    _ ≤
      ∑ r ∈ lowOwnerRevealedPrimesAbove R first,
        (2 : ℝ) / (r : ℝ) ^ 2 *
          postRootCovarianceReciprocalPairEnergy parent := by
        apply Finset.sum_le_sum
        intro r _hr
        have hmultNat :=
          lowOwnerGreatestOwnerFixedParentChildMultiplicity_le_two
            R parent r
        have hmult :
            (lowOwnerGreatestOwnerFixedParentChildMultiplicity
              R parent r : ℝ) ≤ 2 := by
          exact_mod_cast hmultNat
        have hscale :
            (lowOwnerGreatestOwnerFixedParentChildMultiplicity
              R parent r : ℝ) / (r : ℝ) ^ 2 ≤
              (2 : ℝ) / (r : ℝ) ^ 2 :=
          div_le_div_of_nonneg_right hmult (by positivity)
        exact mul_le_mul_of_nonneg_right hscale
          (postRootCovarianceReciprocalPairEnergy_nonneg parent)
    _ =
      2 * (∑ r ∈ lowOwnerRevealedPrimesAbove R first,
        (1 : ℝ) / (r : ℝ) ^ 2) *
          postRootCovarianceReciprocalPairEnergy parent := by
        rw [← Finset.sum_mul]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _hr
        ring
    _ ≤ (1 / 2 : ℝ) *
        postRootCovarianceReciprocalPairEnergy parent := by
      have hbudget :=
        lowOwnerRevealedPrimesAbove_reciprocalSquareBudget_le_quarter
          (R := R) hfirst
      have hE := postRootCovarianceReciprocalPairEnergy_nonneg parent
      nlinarith

/-- Clipped reciprocal outgoing energy restricted to genuine later owners. -/
def lowOwnerGreatestOwnerAboveFirstClippedOutgoingEnergy
    (R first : ℕ) (parent : ℕ × ℕ) : ℝ :=
  ∑ r ∈ lowOwnerRevealedPrimesAbove R first,
    if squareRootEndpoint R < r * parent.2 then
      ∑ child ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent r,
        postRootCovarianceReciprocalPairEnergy child
    else 0

/-- **Quarter contraction on clipped exits in the actual first-owner
chronology.**  Clipping leaves at most one child per odd later owner. -/
theorem lowOwnerGreatestOwnerAboveFirstClippedOutgoingEnergy_le_quarter
    {R first : ℕ} (hfirst : first.Prime) (parent : ℕ × ℕ) :
    lowOwnerGreatestOwnerAboveFirstClippedOutgoingEnergy R first parent ≤
      (1 / 4 : ℝ) * postRootCovarianceReciprocalPairEnergy parent := by
  unfold lowOwnerGreatestOwnerAboveFirstClippedOutgoingEnergy
  calc
    (∑ r ∈ lowOwnerRevealedPrimesAbove R first,
      if squareRootEndpoint R < r * parent.2 then
        ∑ child ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent r,
          postRootCovarianceReciprocalPairEnergy child
      else 0) ≤
      ∑ r ∈ lowOwnerRevealedPrimesAbove R first,
        (1 / (r : ℝ) ^ 2) *
          postRootCovarianceReciprocalPairEnergy parent := by
        apply Finset.sum_le_sum
        intro r hr
        have hrPrime : r.Prime :=
          (mem_primesUpTo.mp (Finset.mem_filter.mp hr).1).1
        by_cases hclip : squareRootEndpoint R < r * parent.2
        · simp only [hclip, if_true]
          rw [sum_lowOwnerGreatestOwnerFixedParentChild_energy_eq
            hrPrime parent]
          have hmultNat :=
            lowOwnerGreatestOwnerFixedParentChildFiber_card_le_one_of_clipped
              hclip
          have hmult :
              (lowOwnerGreatestOwnerFixedParentChildMultiplicity
                R parent r : ℝ) ≤ 1 := by
            unfold lowOwnerGreatestOwnerFixedParentChildMultiplicity
            exact_mod_cast hmultNat
          have hscale :
              (lowOwnerGreatestOwnerFixedParentChildMultiplicity
                R parent r : ℝ) / (r : ℝ) ^ 2 ≤
                (1 : ℝ) / (r : ℝ) ^ 2 :=
            div_le_div_of_nonneg_right hmult (by positivity)
          exact mul_le_mul_of_nonneg_right hscale
            (postRootCovarianceReciprocalPairEnergy_nonneg parent)
        · simp only [hclip, if_false]
          exact mul_nonneg (by positivity)
            (postRootCovarianceReciprocalPairEnergy_nonneg parent)
    _ =
      (∑ r ∈ lowOwnerRevealedPrimesAbove R first,
        (1 : ℝ) / (r : ℝ) ^ 2) *
          postRootCovarianceReciprocalPairEnergy parent := by
        rw [Finset.sum_mul]
    _ ≤ (1 / 4 : ℝ) *
        postRootCovarianceReciprocalPairEnergy parent := by
      exact mul_le_mul_of_nonneg_right
        (lowOwnerRevealedPrimesAbove_reciprocalSquareBudget_le_quarter
          (R := R) hfirst)
        (postRootCovarianceReciprocalPairEnergy_nonneg parent)

/-- Critical clipped-exit energy with arbitrary prior history, restricted to
the only owners which can actually follow the fixed first owner. -/
def lowOwnerZeroTargetHistoryAboveFirstClippedOutgoingEnergy
    (R first : ℕ) (history : ℝ) (parent : ℕ × ℕ) : ℝ :=
  ∑ r ∈ lowOwnerRevealedPrimesAbove R first,
    if squareRootEndpoint R < r * parent.2 then
      ∑ child ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent r,
        (1 - 1 / (r : ℝ)) ^ 2 *
          lowOwnerRetainedCoefficientChildEnergy
            (lowOwnerZeroTargetHistoryReciprocalScale history parent) child
    else 0

/-- **History-safe quarter bound for the only positive exit.** -/
theorem lowOwnerZeroTargetHistoryAboveFirstClippedOutgoingEnergy_le_quarter
    {R first : ℕ} {history : ℝ} {parent : ℕ × ℕ}
    (hfirst : first.Prime)
    (haPos : 0 < parent.1) (hbPos : 0 < parent.2)
    (haMu : realMoebiusStep parent.1 ≠ 0)
    (hbMu : realMoebiusStep parent.2 ≠ 0) :
    lowOwnerZeroTargetHistoryAboveFirstClippedOutgoingEnergy
        R first history parent ≤
      (1 / 4 : ℝ) * history ^ 2 *
        postRootZeroTargetPairExcess parent ^ 2 := by
  have hdrop :
      lowOwnerZeroTargetHistoryAboveFirstClippedOutgoingEnergy
          R first history parent ≤
        (lowOwnerZeroTargetHistoryReciprocalScale history parent) ^ 2 *
          lowOwnerGreatestOwnerAboveFirstClippedOutgoingEnergy
            R first parent := by
    unfold lowOwnerZeroTargetHistoryAboveFirstClippedOutgoingEnergy
      lowOwnerGreatestOwnerAboveFirstClippedOutgoingEnergy
    calc
      (∑ r ∈ lowOwnerRevealedPrimesAbove R first,
        if squareRootEndpoint R < r * parent.2 then
          ∑ child ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent r,
            (1 - 1 / (r : ℝ)) ^ 2 *
              lowOwnerRetainedCoefficientChildEnergy
                (lowOwnerZeroTargetHistoryReciprocalScale history parent)
                child
        else 0) ≤
        ∑ r ∈ lowOwnerRevealedPrimesAbove R first,
          if squareRootEndpoint R < r * parent.2 then
            ∑ child ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent r,
              lowOwnerRetainedCoefficientChildEnergy
                (lowOwnerZeroTargetHistoryReciprocalScale history parent)
                child
          else 0 := by
            apply Finset.sum_le_sum
            intro r hr
            have hrPrime : r.Prime :=
              (mem_primesUpTo.mp (Finset.mem_filter.mp hr).1).1
            by_cases hclip : squareRootEndpoint R < r * parent.2
            · simp only [hclip, if_true]
              apply Finset.sum_le_sum
              intro child _hchild
              have hchild0 :
                  0 ≤ lowOwnerRetainedCoefficientChildEnergy
                    (lowOwnerZeroTargetHistoryReciprocalScale history parent)
                    child := by
                exact mul_nonneg
                  (sq_nonneg
                    (lowOwnerZeroTargetHistoryReciprocalScale history parent))
                  (postRootCovarianceReciprocalPairEnergy_nonneg child)
              simpa only [one_mul] using
                (mul_le_mul_of_nonneg_right
                  (critical_one_sub_reciprocal_sq_le_one hrPrime)
                  hchild0)
            · simp [hclip]
      _ =
        (lowOwnerZeroTargetHistoryReciprocalScale history parent) ^ 2 *
          (∑ r ∈ lowOwnerRevealedPrimesAbove R first,
            if squareRootEndpoint R < r * parent.2 then
              ∑ child ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent r,
                postRootCovarianceReciprocalPairEnergy child
            else 0) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro r _hr
              by_cases hclip : squareRootEndpoint R < r * parent.2
              · simp only [hclip, if_true]
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro child _hchild
                rfl
              · simp [hclip]
      _ = _ := rfl
  have hquarter :=
    lowOwnerGreatestOwnerAboveFirstClippedOutgoingEnergy_le_quarter
      (R := R) hfirst parent
  have hscale0 :
      0 ≤ (lowOwnerZeroTargetHistoryReciprocalScale history parent) ^ 2 :=
    sq_nonneg _
  have hscaled := mul_le_mul_of_nonneg_left hquarter hscale0
  have hnorm :=
    lowOwnerZeroTargetHistoryParentEnergy_eq_rawExcessSq
      (history := history) (parent := parent)
      haPos hbPos haMu hbMu
  unfold lowOwnerRetainedCoefficientParentEnergy at hnorm
  calc
    lowOwnerZeroTargetHistoryAboveFirstClippedOutgoingEnergy
        R first history parent ≤
      (lowOwnerZeroTargetHistoryReciprocalScale history parent) ^ 2 *
        lowOwnerGreatestOwnerAboveFirstClippedOutgoingEnergy
          R first parent := hdrop
    _ ≤
      (lowOwnerZeroTargetHistoryReciprocalScale history parent) ^ 2 *
        ((1 / 4 : ℝ) *
          postRootCovarianceReciprocalPairEnergy parent) := hscaled
    _ = (1 / 4 : ℝ) *
        ((lowOwnerZeroTargetHistoryReciprocalScale history parent) ^ 2 *
          postRootCovarianceReciprocalPairEnergy parent) := by ring
    _ = (1 / 4 : ℝ) * history ^ 2 *
        postRootZeroTargetPairExcess parent ^ 2 := by
      rw [hnorm]
      ring


end RHLean.Proof
