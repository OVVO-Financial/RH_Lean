import Mathlib
import RHLean.Arithmetic.SquareBlockParityPopulation

/-!
# Collision-cell frontier bound

Once the settled portion of a finite block is partitioned into complete
collision cells, its signed mass is exactly zero.  The whole discrepancy is
therefore supported on the unresolved frontier.  This file proves that finite
reduction abstractly and specializes it to square-block Mobius sums.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

/-- If the complement of `U` in `B` has zero signed mass, then the full sum is
exactly the sum over `U`. -/
theorem sum_eq_frontier_sum_of_complement_zero
    {α : Type*} [DecidableEq α]
    (B U : Finset α) (f : α → ℤ)
    (hU : U ⊆ B)
    (hsettled : ∑ x ∈ B \ U, f x = 0) :
    ∑ x ∈ B, f x = ∑ x ∈ U, f x := by
  have hdisj : Disjoint (B \ U) U := Finset.disjoint_sdiff_left
  have hunion : (B \ U) ∪ U = B := by
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · intro hx
      rcases hx with hx | hx
      · exact hx.1
      · exact hU hx
    · intro hxB
      by_cases hxU : x ∈ U
      · exact Or.inr hxU
      · exact Or.inl ⟨hxB, hxU⟩
  calc
    ∑ x ∈ B, f x = ∑ x ∈ (B \ U) ∪ U, f x := by rw [hunion]
    _ = (∑ x ∈ B \ U, f x) + ∑ x ∈ U, f x := by
      rw [Finset.sum_union hdisj]
    _ = ∑ x ∈ U, f x := by rw [hsettled, zero_add]

/-- If every entry has absolute weight at most one, then a zero-mass settled
region leaves discrepancy at most the frontier cardinality. -/
theorem abs_sum_le_frontier_card_of_complement_zero
    {α : Type*} [DecidableEq α]
    (B U : Finset α) (f : α → ℤ)
    (hU : U ⊆ B)
    (hunit : ∀ x ∈ B, |f x| ≤ 1)
    (hsettled : ∑ x ∈ B \ U, f x = 0) :
    |∑ x ∈ B, f x| ≤ (U.card : ℤ) := by
  rw [sum_eq_frontier_sum_of_complement_zero B U f hU hsettled]
  calc
    |∑ x ∈ U, f x| ≤ ∑ x ∈ U, |f x| := by
      simpa only [Int.norm_eq_abs] using
        (norm_sum_le U (fun x => f x))
    _ ≤ ∑ _x ∈ U, (1 : ℤ) := by
      apply Finset.sum_le_sum
      intro x hx
      exact hunit x (hU hx)
    _ = (U.card : ℤ) := by simp

/-- Square-block specialization.  If the complement of `U` is a disjoint union
of complete collision cells and hence has zero Mobius mass, the block increment
is supported entirely on `U`. -/
theorem abs_squareBlockMoebius_le_frontier_card
    (n : ℕ) (U : Finset ℕ)
    (hU : U ⊆ squareBlockInterval n)
    (hsettled : ∑ x ∈ squareBlockInterval n \ U, μ x = 0) :
    |squareBlockMoebius n| ≤ (U.card : ℤ) := by
  unfold squareBlockMoebius
  apply abs_sum_le_frontier_card_of_complement_zero
      (squareBlockInterval n) U (fun x => μ x) hU
  · intro x hx
    have hbound : |μ x| ≤ (1 : ℤ) := by
      rcases Int.natAbs_eq_zero_or_pos (μ x) with hzero | hpos
      · simpa [Int.natAbs_eq_zero.mp hzero]
      · have hvals : μ x = -1 ∨ μ x = 0 ∨ μ x = 1 := by
          simpa using ArithmeticFunction.moebius_eq_neg_one_or_zero_or_one x
        rcases hvals with h | h | h <;> simp [h]
    exact hbound
  · exact hsettled

/-- Two-error form: if `U` is split into a cell-boundary part and an unresolved
prime-frontier part, then the discrepancy is bounded by the sum of their
cardinalities. -/
theorem abs_squareBlockMoebius_le_boundary_add_unresolved
    (n : ℕ) (boundary unresolved : Finset ℕ)
    (hboundary : boundary ⊆ squareBlockInterval n)
    (hunresolved : unresolved ⊆ squareBlockInterval n)
    (hsettled :
      ∑ x ∈ squareBlockInterval n \ (boundary ∪ unresolved), μ x = 0) :
    |squareBlockMoebius n| ≤
      (boundary.card : ℤ) + (unresolved.card : ℤ) := by
  have hU : boundary ∪ unresolved ⊆ squareBlockInterval n := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hboundary hx
    · exact hunresolved hx
  have hmain := abs_squareBlockMoebius_le_frontier_card
    n (boundary ∪ unresolved) hU hsettled
  calc
    |squareBlockMoebius n| ≤ ((boundary ∪ unresolved).card : ℤ) := hmain
    _ ≤ (boundary.card : ℤ) + (unresolved.card : ℤ) := by
      exact_mod_cast Finset.card_union_le boundary unresolved

end RHLean.Proof
