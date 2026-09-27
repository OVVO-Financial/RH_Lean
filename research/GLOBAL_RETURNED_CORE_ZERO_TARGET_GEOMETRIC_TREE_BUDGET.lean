import Mathlib
import «research.GLOBAL_RETURNED_CORE_ZERO_TARGET_CLIPPED_HISTORY_CONTRACTION»
import «research.GLOBAL_RETURNED_CORE_UNIQUE_OWNER_RANK_DROP»

/-!
# Finite-rank geometric budget for the zero-target continuation tree

The local history-safe estimates now give exactly the two constants needed for
a finite-rank invariant:

* recursive continuation <= one half of incoming energy;
* positive clipped exit <= one quarter of incoming energy.

Because unique greatest-owner descent drops the fresh-pair rank by exactly one,
any actual recursive branch is finite.  The purely quantitative part can be
closed without an infinite geometric series: if E_k is the aggregate energy
remaining at rank generation k and X_k is the positive exit emitted there,
then

  2 * sum_{j < n} X_j + E_n <= E_0.

Hence every finite collection of positive exits is bounded by E_0 / 2,
independently of the depth.  This module records that finite invariant as the
consumer for the forthcoming carrier-level generation reindex.

No RH hypothesis, Mertens magnitude estimate, limit, or asymptotic argument is
used here.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

/-- Abstract finite-rank energy conditions matching the compiled local
zero-target continuation estimates. -/
def LowOwnerZeroTargetGenerationBudget
    (generation exit : ℕ → ℝ) : Prop :=
  (∀ k : ℕ, 0 ≤ generation k) ∧
  (∀ k : ℕ, exit k ≤ (1 / 4 : ℝ) * generation k) ∧
  (∀ k : ℕ, generation (k + 1) ≤ (1 / 2 : ℝ) * generation k)

/-- **Finite-rank geometric invariant.**

Two copies of every accumulated positive exit plus the still-live recursive
energy never exceed the initial energy.  This is stronger than merely summing
a geometric series and is designed for direct induction on the exact
fresh-pair rank. -/
theorem lowOwnerZeroTargetGenerationBudget_invariant
    {generation exit : ℕ → ℝ}
    (hbudget : LowOwnerZeroTargetGenerationBudget generation exit) :
    ∀ n : ℕ,
      2 * (∑ k ∈ Finset.range n, exit k) + generation n ≤ generation 0 := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rcases hbudget with ⟨_hgen, hexit, hrec⟩
      have hx := hexit n
      have hr := hrec n
      rw [Finset.sum_range_succ]
      norm_num at ih ⊢
      nlinarith

/-- Every finite prefix of positive exits costs at most one half of the initial
energy, uniformly in the depth. -/
theorem lowOwnerZeroTargetGenerationBudget_exitPrefix_le_half
    {generation exit : ℕ → ℝ}
    (hbudget : LowOwnerZeroTargetGenerationBudget generation exit)
    (n : ℕ) :
    (∑ k ∈ Finset.range n, exit k) ≤
      (1 / 2 : ℝ) * generation 0 := by
  have hinv :=
    lowOwnerZeroTargetGenerationBudget_invariant hbudget n
  have hgen0 : 0 ≤ generation n := hbudget.1 n
  nlinarith

/-- Root-envelope form: once the initial generation is controlled by some
nonnegative scale B, all positive exits at every finite depth are controlled by
B/2 with no depth-dependent constant. -/
theorem lowOwnerZeroTargetGenerationBudget_exitPrefix_le_half_of_initial
    {generation exit : ℕ → ℝ} {B : ℝ}
    (hbudget : LowOwnerZeroTargetGenerationBudget generation exit)
    (hinit : generation 0 ≤ B)
    (n : ℕ) :
    (∑ k ∈ Finset.range n, exit k) ≤ (1 / 2 : ℝ) * B := by
  have hpref :=
    lowOwnerZeroTargetGenerationBudget_exitPrefix_le_half hbudget n
  linarith

/-- If the recursive tree terminates at generation n, the same invariant gives
a direct finite certificate with no limiting argument. -/
theorem lowOwnerZeroTargetGenerationBudget_terminal_certificate
    {generation exit : ℕ → ℝ}
    (hbudget : LowOwnerZeroTargetGenerationBudget generation exit)
    {n : ℕ} (hterminal : generation n = 0) :
    2 * (∑ k ∈ Finset.range n, exit k) ≤ generation 0 := by
  have hinv :=
    lowOwnerZeroTargetGenerationBudget_invariant hbudget n
  rw [hterminal] at hinv
  linarith

end RHLean.Proof
