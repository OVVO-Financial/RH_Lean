import Mathlib

/-!
# Prime-comb discrepancy recurrence

This module records the exact bookkeeping exposed by the progressive square-block
comb sweep.  When a new prime coordinate is added, the signed parity total can
change in only five ways:

* a previously untouched position receives its first prime hit and enters with
  sign `-1`;
* an existing positive squarefree state is hit and flips from `+1` to `-1`;
* an existing negative squarefree state is hit and flips from `-1` to `+1`;
* a positive state is killed by a repeated-prime collision;
* a negative state is killed by a repeated-prime collision.

The exact recurrence is purely finite.  The asymptotic PNT/RH burden is isolated
in quantitative estimates for the signed imbalance of these channels; no such
estimate is assumed to be automatic from cardinality alone.
-/

noncomputable section

namespace RHLean.Proof

/-- Finite channel counts for one successive-prime update. -/
structure PrimeCombUpdate where
  before : ℤ
  after : ℤ
  firstHits : ℕ
  positiveCollisions : ℕ
  negativeCollisions : ℕ
  positiveDeaths : ℕ
  negativeDeaths : ℕ
  updateLaw :
    after = before
      - (firstHits : ℤ)
      - 2 * (positiveCollisions : ℤ)
      + 2 * (negativeCollisions : ℤ)
      - (positiveDeaths : ℤ)
      + (negativeDeaths : ℤ)

/-- Signed collision imbalance of one prime comb.  Positive values mean that the
new comb hits more negative than positive states and therefore restores the
current discrepancy upward. -/
def PrimeCombUpdate.collisionImbalance (u : PrimeCombUpdate) : ℤ :=
  (u.negativeCollisions : ℤ) - (u.positiveCollisions : ℤ)

/-- Signed repeated-prime death imbalance. -/
def PrimeCombUpdate.deathImbalance (u : PrimeCombUpdate) : ℤ :=
  (u.negativeDeaths : ℤ) - (u.positiveDeaths : ℤ)

/-- Exact compact form of the prime-by-prime discrepancy recurrence. -/
theorem PrimeCombUpdate.after_eq_compact (u : PrimeCombUpdate) :
    u.after = u.before - (u.firstHits : ℤ)
      + 2 * u.collisionImbalance + u.deathImbalance := by
  rw [u.updateLaw]
  unfold PrimeCombUpdate.collisionImbalance PrimeCombUpdate.deathImbalance
  ring

/-- Exact increment form. -/
theorem PrimeCombUpdate.increment_eq (u : PrimeCombUpdate) :
    u.after - u.before =
      -(u.firstHits : ℤ) + 2 * u.collisionImbalance + u.deathImbalance := by
  rw [u.after_eq_compact]
  ring

/-- A safe absolute bound which charges only the signed collision and death
imbalances, not the total number of collision teeth. -/
theorem PrimeCombUpdate.abs_after_le (u : PrimeCombUpdate) :
    |u.after| ≤ |u.before| + (u.firstHits : ℤ)
      + 2 * |u.collisionImbalance| + |u.deathImbalance| := by
  rw [u.after_eq_compact]
  have hfirst : 0 ≤ (u.firstHits : ℤ) := by positivity
  calc
    |u.before - (u.firstHits : ℤ) + 2 * u.collisionImbalance + u.deathImbalance|
        ≤ |u.before| + |-(u.firstHits : ℤ)|
          + |2 * u.collisionImbalance| + |u.deathImbalance| := by
            calc
              |u.before - (u.firstHits : ℤ) + 2 * u.collisionImbalance + u.deathImbalance|
                  ≤ |u.before - (u.firstHits : ℤ) + 2 * u.collisionImbalance|
                    + |u.deathImbalance| := abs_add _ _
              _ ≤ (|u.before - (u.firstHits : ℤ)| + |2 * u.collisionImbalance|)
                    + |u.deathImbalance| := by gcongr; exact abs_add _ _
              _ ≤ ((|u.before| + |-(u.firstHits : ℤ)|)
                    + |2 * u.collisionImbalance|) + |u.deathImbalance| := by
                    gcongr
                    simpa [sub_eq_add_neg] using abs_add u.before (-(u.firstHits : ℤ))
    _ = |u.before| + (u.firstHits : ℤ)
          + 2 * |u.collisionImbalance| + |u.deathImbalance| := by
          rw [abs_of_nonneg hfirst]
          simp [abs_mul]
          ring

/-- Quantitative restoring hypothesis for one prime coordinate.

The parameter `alpha` describes the fraction of the old discrepancy removed by
the signed collision imbalance.  `error` contains first-hit and death defects as
well as any failure of exact proportional sampling. -/
def PrimeCombUpdate.HasRestoringEstimate
    (u : PrimeCombUpdate) (alpha error : ℝ) : Prop :=
  |((u.after : ℝ))| ≤ (1 - alpha) * |((u.before : ℝ))| + error

/-- Iterating any proved restoring estimate is the correct route to a global
bound.  This one-step theorem deliberately requires the arithmetic estimate as
a premise rather than deriving it from raw collision cardinalities. -/
theorem PrimeCombUpdate.abs_after_le_of_restoring
    (u : PrimeCombUpdate) {alpha error : ℝ}
    (h : u.HasRestoringEstimate alpha error) :
    |((u.after : ℝ))| ≤ (1 - alpha) * |((u.before : ℝ))| + error := h

/-- Exact block-10 channel data for the `5`-comb after processing `2` and `3`.

Before adding `5`, the provisional squarefree parity total is `-3`.  The new
prime creates one first hit (`115`), flips two negative states (`105`, `110`),
and creates no new live positive collision or death.  Hence the new total is
zero. -/
def blockTenPrimeFiveUpdate : PrimeCombUpdate where
  before := -3
  after := 0
  firstHits := 1
  positiveCollisions := 0
  negativeCollisions := 2
  positiveDeaths := 0
  negativeDeaths := 0
  updateLaw := by norm_num

/-- Machine-checkable block-10 certificate for the restoring `5`-comb step. -/
theorem blockTenPrimeFive_increment :
    blockTenPrimeFiveUpdate.after - blockTenPrimeFiveUpdate.before = 3 := by
  norm_num [blockTenPrimeFiveUpdate]

/-- The compact recurrence reproduces the exact block-10 update `-3 -> 0`. -/
theorem blockTenPrimeFive_after : blockTenPrimeFiveUpdate.after = 0 := by
  norm_num [blockTenPrimeFiveUpdate]

end RHLean.Proof
