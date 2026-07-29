import Mathlib

/-!
# Square-block prefix-comb sweep: blocks 1 through 10

This module recovers the finite construction in which a target square block starts
as dots and is filled by successively overlaying fresh-prime combs from the fixed
old prefix.

The first-cover convention removes redundant factorizations: a block position is
counted only for the least parent whose active comb reaches it. Since the least
parent corresponds to deleting the largest available fresh prime, this is the
finite canonical sweep used by the project.

Blocks `1` and `2` are retained explicitly as seed exceptions. Blocks `3` through
`10` are completely covered by the old parent ceiling and satisfy the exact
first-cover signed recurrence.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Arithmetic

/-- The half-open square block `[n^2,(n+1)^2)`. -/
def prefixCombSquareBlock (n : ℕ) : Finset ℕ :=
  Finset.Icc (n ^ 2) ((n + 1) ^ 2 - 1)

/-- Largest parent available from the preceding completed square prefix. -/
def prefixCombParentCeiling (n : ℕ) : ℕ :=
  (n ^ 2 - 1) / 2

/-- An active fresh-prime comb tooth from parent `c` at position `x`.

The parent must have nonzero Möbius value, `x/c` must be prime, and that prime
must not already divide `c`. -/
def activeFreshPrimeCombHit (c x : ℕ) : Bool :=
  decide (0 < c ∧ μ c ≠ 0 ∧ c ∣ x ∧ Nat.Prime (x / c) ∧ ¬ x / c ∣ c)

/-- Position `x` is first covered by parent `c`: parent `c` hits it and no smaller
parent does. -/
def firstCoveredByPrefixComb (c x : ℕ) : Bool :=
  activeFreshPrimeCombHit c x &&
    !decide (∃ d ∈ Finset.range c, activeFreshPrimeCombHit d x = true)

/-- Genuinely new teeth contributed by parent `c` to block `n`. -/
def firstCoverTeeth (n c : ℕ) : Finset ℕ :=
  (prefixCombSquareBlock n).filter fun x => firstCoveredByPrefixComb c x

/-- Number of genuinely new positions filled by parent `c`. -/
def prefixCombNewCoverageCount (n c : ℕ) : ℕ :=
  (firstCoverTeeth n c).card

/-- Whether a nonzero block position is reached by some parent in the old prefix. -/
def coveredByOldPrefix (n x : ℕ) : Bool :=
  decide (∃ i ∈ Finset.range (prefixCombParentCeiling n),
    activeFreshPrimeCombHit (i + 1) x = true)

/-- Nonzero Möbius positions not reached by the old-prefix comb sweep. -/
def uncoveredSquarefreePositions (n : ℕ) : Finset ℕ :=
  (prefixCombSquareBlock n).filter fun x =>
    decide (μ x ≠ 0) && !coveredByOldPrefix n x

/-- Running signed discrepancy after the first `r` parents have been processed.
Parent `i+1` contributes the opposite of its Möbius sign at every newly covered
position. -/
def prefixCombSweepDiscrepancy (n r : ℕ) : ℤ :=
  (Finset.range r).sum fun i =>
    -(μ (i + 1)) * (prefixCombNewCoverageCount n (i + 1) : ℤ)

/-- The sweep has the exact one-parent recurrence. -/
theorem prefixCombSweepDiscrepancy_succ (n r : ℕ) :
    prefixCombSweepDiscrepancy n (r + 1) =
      prefixCombSweepDiscrepancy n r -
        μ (r + 1) * (prefixCombNewCoverageCount n (r + 1) : ℤ) := by
  simp [prefixCombSweepDiscrepancy]

/-- Actual Möbius increment of square block `n`. -/
def prefixCombBlockIncrement (n : ℕ) : ℤ :=
  (prefixCombSquareBlock n).sum fun x => μ x

/-- Positive nonzero support of a square block. -/
def prefixCombPositiveSupport (n : ℕ) : Finset ℕ :=
  (prefixCombSquareBlock n).filter fun x => decide (μ x = 1)

/-- Negative nonzero support of a square block. -/
def prefixCombNegativeSupport (n : ℕ) : Finset ℕ :=
  (prefixCombSquareBlock n).filter fun x => decide (μ x = -1)

/-! ## Seed blocks -/

theorem prefixComb_block_one_seed :
    prefixCombBlockIncrement 1 = -1 ∧
      uncoveredSquarefreePositions 1 = ([1, 2, 3] : List ℕ).toFinset := by
  native_decide

theorem prefixComb_block_two_seed :
    prefixCombBlockIncrement 2 = -1 ∧
      uncoveredSquarefreePositions 2 = ([6] : List ℕ).toFinset := by
  native_decide

/-! ## Recovered first-cover traces for blocks 3 through 10 -/

theorem prefixComb_block_three_trace :
    firstCoverTeeth 3 1 = ([11, 13] : List ℕ).toFinset ∧
    firstCoverTeeth 3 2 = ([10, 14] : List ℕ).toFinset ∧
    firstCoverTeeth 3 3 = ([15] : List ℕ).toFinset := by
  native_decide

theorem prefixComb_block_four_trace :
    firstCoverTeeth 4 1 = ([17, 19, 23] : List ℕ).toFinset ∧
    firstCoverTeeth 4 2 = ([22] : List ℕ).toFinset ∧
    firstCoverTeeth 4 3 = ([21] : List ℕ).toFinset := by
  native_decide

theorem prefixComb_block_five_trace :
    firstCoverTeeth 5 1 = ([29, 31] : List ℕ).toFinset ∧
    firstCoverTeeth 5 2 = ([26, 34] : List ℕ).toFinset ∧
    firstCoverTeeth 5 3 = ([33] : List ℕ).toFinset ∧
    firstCoverTeeth 5 5 = ([35] : List ℕ).toFinset ∧
    firstCoverTeeth 5 6 = ([30] : List ℕ).toFinset := by
  native_decide

theorem prefixComb_block_six_trace :
    firstCoverTeeth 6 1 = ([37, 41, 43, 47] : List ℕ).toFinset ∧
    firstCoverTeeth 6 2 = ([38, 46] : List ℕ).toFinset ∧
    firstCoverTeeth 6 3 = ([39] : List ℕ).toFinset ∧
    firstCoverTeeth 6 6 = ([42] : List ℕ).toFinset := by
  native_decide

theorem prefixComb_block_seven_trace :
    firstCoverTeeth 7 1 = ([53, 59, 61] : List ℕ).toFinset ∧
    firstCoverTeeth 7 2 = ([58, 62] : List ℕ).toFinset ∧
    firstCoverTeeth 7 3 = ([51, 57] : List ℕ).toFinset ∧
    firstCoverTeeth 7 5 = ([55] : List ℕ).toFinset := by
  native_decide

theorem prefixComb_block_eight_trace :
    firstCoverTeeth 8 1 = ([67, 71, 73, 79] : List ℕ).toFinset ∧
    firstCoverTeeth 8 2 = ([74] : List ℕ).toFinset ∧
    firstCoverTeeth 8 3 = ([69] : List ℕ).toFinset ∧
    firstCoverTeeth 8 5 = ([65] : List ℕ).toFinset ∧
    firstCoverTeeth 8 6 = ([66, 78] : List ℕ).toFinset ∧
    firstCoverTeeth 8 7 = ([77] : List ℕ).toFinset ∧
    firstCoverTeeth 8 10 = ([70] : List ℕ).toFinset := by
  native_decide

theorem prefixComb_block_nine_trace :
    firstCoverTeeth 9 1 = ([83, 89, 97] : List ℕ).toFinset ∧
    firstCoverTeeth 9 2 = ([82, 86, 94] : List ℕ).toFinset ∧
    firstCoverTeeth 9 3 = ([87, 93] : List ℕ).toFinset ∧
    firstCoverTeeth 9 5 = ([85, 95] : List ℕ).toFinset ∧
    firstCoverTeeth 9 7 = ([91] : List ℕ).toFinset := by
  native_decide

theorem prefixComb_block_ten_trace :
    firstCoverTeeth 10 1 = ([101, 103, 107, 109, 113] : List ℕ).toFinset ∧
    firstCoverTeeth 10 2 = ([106, 118] : List ℕ).toFinset ∧
    firstCoverTeeth 10 3 = ([111] : List ℕ).toFinset ∧
    firstCoverTeeth 10 5 = ([115] : List ℕ).toFinset ∧
    firstCoverTeeth 10 6 = ([102, 114] : List ℕ).toFinset ∧
    firstCoverTeeth 10 7 = ([119] : List ℕ).toFinset ∧
    firstCoverTeeth 10 10 = ([110] : List ℕ).toFinset ∧
    firstCoverTeeth 10 15 = ([105] : List ℕ).toFinset := by
  native_decide

/-! ## Exact completion, increments, and mixed signs -/

theorem prefixComb_blocks_three_to_ten_complete :
    uncoveredSquarefreePositions 3 = ∅ ∧
    uncoveredSquarefreePositions 4 = ∅ ∧
    uncoveredSquarefreePositions 5 = ∅ ∧
    uncoveredSquarefreePositions 6 = ∅ ∧
    uncoveredSquarefreePositions 7 = ∅ ∧
    uncoveredSquarefreePositions 8 = ∅ ∧
    uncoveredSquarefreePositions 9 = ∅ ∧
    uncoveredSquarefreePositions 10 = ∅ := by
  native_decide

theorem prefixComb_blocks_three_to_ten_exact_sweep :
    prefixCombSweepDiscrepancy 3 (prefixCombParentCeiling 3) = prefixCombBlockIncrement 3 ∧
    prefixCombSweepDiscrepancy 4 (prefixCombParentCeiling 4) = prefixCombBlockIncrement 4 ∧
    prefixCombSweepDiscrepancy 5 (prefixCombParentCeiling 5) = prefixCombBlockIncrement 5 ∧
    prefixCombSweepDiscrepancy 6 (prefixCombParentCeiling 6) = prefixCombBlockIncrement 6 ∧
    prefixCombSweepDiscrepancy 7 (prefixCombParentCeiling 7) = prefixCombBlockIncrement 7 ∧
    prefixCombSweepDiscrepancy 8 (prefixCombParentCeiling 8) = prefixCombBlockIncrement 8 ∧
    prefixCombSweepDiscrepancy 9 (prefixCombParentCeiling 9) = prefixCombBlockIncrement 9 ∧
    prefixCombSweepDiscrepancy 10 (prefixCombParentCeiling 10) = prefixCombBlockIncrement 10 := by
  native_decide

theorem prefixComb_blocks_one_to_ten_increments :
    prefixCombBlockIncrement 1 = -1 ∧
    prefixCombBlockIncrement 2 = -1 ∧
    prefixCombBlockIncrement 3 = 1 ∧
    prefixCombBlockIncrement 4 = -1 ∧
    prefixCombBlockIncrement 5 = 1 ∧
    prefixCombBlockIncrement 6 = -2 ∧
    prefixCombBlockIncrement 7 = 2 ∧
    prefixCombBlockIncrement 8 = -3 ∧
    prefixCombBlockIncrement 9 = 5 ∧
    prefixCombBlockIncrement 10 = -4 := by
  native_decide

theorem prefixComb_blocks_three_to_ten_mixed_sign :
    prefixCombPositiveSupport 3 ≠ ∅ ∧ prefixCombNegativeSupport 3 ≠ ∅ ∧
    prefixCombPositiveSupport 4 ≠ ∅ ∧ prefixCombNegativeSupport 4 ≠ ∅ ∧
    prefixCombPositiveSupport 5 ≠ ∅ ∧ prefixCombNegativeSupport 5 ≠ ∅ ∧
    prefixCombPositiveSupport 6 ≠ ∅ ∧ prefixCombNegativeSupport 6 ≠ ∅ ∧
    prefixCombPositiveSupport 7 ≠ ∅ ∧ prefixCombNegativeSupport 7 ≠ ∅ ∧
    prefixCombPositiveSupport 8 ≠ ∅ ∧ prefixCombNegativeSupport 8 ≠ ∅ ∧
    prefixCombPositiveSupport 9 ≠ ∅ ∧ prefixCombNegativeSupport 9 ≠ ∅ ∧
    prefixCombPositiveSupport 10 ≠ ∅ ∧ prefixCombNegativeSupport 10 ≠ ∅ := by
  native_decide

end RHLean.Arithmetic
