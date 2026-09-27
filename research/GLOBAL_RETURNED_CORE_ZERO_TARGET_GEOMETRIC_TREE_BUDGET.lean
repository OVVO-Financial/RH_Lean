import Mathlib
import «research.GLOBAL_RETURNED_CORE_ZERO_TARGET_CLIPPED_HISTORY_CONTRACTION»
import «research.GLOBAL_RETURNED_CORE_UNIQUE_OWNER_RANK_DROP»
import «research.GLOBAL_RETURNED_CORE_RETAINED_COEFFICIENT_OUTGOING_ENERGY»
import «research.GLOBAL_RETURNED_CORE_GREATEST_OWNER_BASEL_CONTRACTION»

/-!
# Finite-rank geometric budgets for reciprocal-weighted downstream trees

This file records two deliberately separated facts.

First, an abstract finite-rank invariant shows that *if* a generation energy
contracts by one half and its positive exit costs one quarter, then accumulated
exits have a uniform half-budget. The current zero-target history module proves
the half estimate only for a reciprocal-weighted diagnostic side ledger, not
for the raw signed quadratic continuation. Therefore this abstract invariant is
not instantiated here as a bound on that signed continuation.

Second, after a legal incidence-energy gate has already placed a coefficient in
reciprocal currency, the repository does have a genuine all-owner contraction
on the literal greatest-owner child graph. The retained-coefficient tree below
iterates that legal downstream currency and obtains a depth-independent finite
constant.

For the abstract invariant, if E_k is the generation energy and X_k the
positive exit, then

  2 * sum_{j < n} X_j + E_n <= E_0.

Hence every finite prefix is bounded by E_0 / 2 independently of depth, under
those stated hypotheses.

No claim is made here that the signed top-scale Stokes/endpoint-gap quantity has
entered reciprocal currency, and no RH hypothesis, Mertens magnitude estimate,
limit, or asymptotic argument is used.
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


/-! ## Actual greatest-owner tree with retained coefficient -/

/-- Finite-depth downstream reciprocal tree on the literal greatest-owner child
fibres.  The coefficient is retained unchanged on every descendant, exactly as
required by `lowOwnerRetainedCoefficientOutgoingEnergy`. -/
def lowOwnerRetainedCoefficientTreeEnergy
    (R depth : ℕ) (parent : ℕ × ℕ) (coefficient : ℝ) : ℝ :=
  match depth with
  | 0 => lowOwnerRetainedCoefficientParentEnergy coefficient parent
  | d + 1 =>
      lowOwnerRetainedCoefficientParentEnergy coefficient parent +
        ∑ r ∈ primesUpTo (squareRootEndpoint R),
          ∑ child ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent r,
            lowOwnerRetainedCoefficientTreeEnergy R d child coefficient

/-- The finite-depth retained-coefficient tree energy is nonnegative. -/
theorem lowOwnerRetainedCoefficientTreeEnergy_nonneg
    (R depth : ℕ) (parent : ℕ × ℕ) (coefficient : ℝ) :
    0 ≤ lowOwnerRetainedCoefficientTreeEnergy R depth parent coefficient := by
  induction depth generalizing parent with
  | zero =>
      simpa [lowOwnerRetainedCoefficientTreeEnergy] using
        (lowOwnerRetainedCoefficientParentEnergy_nonneg coefficient parent)
  | succ d ih =>
      simp only [lowOwnerRetainedCoefficientTreeEnergy]
      apply add_nonneg
      · exact lowOwnerRetainedCoefficientParentEnergy_nonneg coefficient parent
      · apply Finset.sum_nonneg
        intro r _hr
        apply Finset.sum_nonneg
        intro child _hchild
        exact ih child

/-- **Uniform all-depth finite tree bound.**

The already-compiled all-owner retained-coefficient contraction
`79/81 < 1` implies that every finite truncation of the literal downstream
greatest-owner tree costs at most `81/2` times its root reciprocal energy.

No rank cutoff, asymptotic estimate, or limit is used in this inequality. -/
theorem lowOwnerRetainedCoefficientTreeEnergy_le_eightyOneOverTwo
    (R depth : ℕ) (parent : ℕ × ℕ) (coefficient : ℝ) :
    lowOwnerRetainedCoefficientTreeEnergy R depth parent coefficient ≤
      (81 / 2 : ℝ) *
        lowOwnerRetainedCoefficientParentEnergy coefficient parent := by
  induction depth generalizing parent with
  | zero =>
      simp only [lowOwnerRetainedCoefficientTreeEnergy]
      have hnon :=
        lowOwnerRetainedCoefficientParentEnergy_nonneg coefficient parent
      nlinarith
  | succ d ih =>
      simp only [lowOwnerRetainedCoefficientTreeEnergy]
      have hchildren :
          (∑ r ∈ primesUpTo (squareRootEndpoint R),
            ∑ child ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent r,
              lowOwnerRetainedCoefficientTreeEnergy R d child coefficient) ≤
            (81 / 2 : ℝ) *
              lowOwnerRetainedCoefficientOutgoingEnergy R parent coefficient := by
        unfold lowOwnerRetainedCoefficientOutgoingEnergy
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro r _hr
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro child _hchild
        exact ih child
      have hout :=
        lowOwnerRetainedCoefficientOutgoingEnergy_le_79_over_81
          R parent coefficient
      have hparent0 :=
        lowOwnerRetainedCoefficientParentEnergy_nonneg coefficient parent
      calc
        lowOwnerRetainedCoefficientParentEnergy coefficient parent +
            (∑ r ∈ primesUpTo (squareRootEndpoint R),
              ∑ child ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent r,
                lowOwnerRetainedCoefficientTreeEnergy R d child coefficient) ≤
          lowOwnerRetainedCoefficientParentEnergy coefficient parent +
            (81 / 2 : ℝ) *
              lowOwnerRetainedCoefficientOutgoingEnergy R parent coefficient :=
                add_le_add_left hchildren _
        _ ≤ (81 / 2 : ℝ) *
            lowOwnerRetainedCoefficientParentEnergy coefficient parent := by
              nlinarith


/-- **Basel-sharpened all-depth tree bound.**

Using the already-compiled `218/225` all-owner contraction instead of
`79/81`, every finite truncation of the literal retained-coefficient tree is
bounded by `225/7` times its root energy. -/
theorem lowOwnerRetainedCoefficientTreeEnergy_le_twoHundredTwentyFiveOverSeven
    (R depth : ℕ) (parent : ℕ × ℕ) (coefficient : ℝ) :
    lowOwnerRetainedCoefficientTreeEnergy R depth parent coefficient ≤
      (225 / 7 : ℝ) *
        lowOwnerRetainedCoefficientParentEnergy coefficient parent := by
  induction depth generalizing parent with
  | zero =>
      simp only [lowOwnerRetainedCoefficientTreeEnergy]
      have hnon :=
        lowOwnerRetainedCoefficientParentEnergy_nonneg coefficient parent
      nlinarith
  | succ d ih =>
      simp only [lowOwnerRetainedCoefficientTreeEnergy]
      have hchildren :
          (∑ r ∈ primesUpTo (squareRootEndpoint R),
            ∑ child ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent r,
              lowOwnerRetainedCoefficientTreeEnergy R d child coefficient) ≤
            (225 / 7 : ℝ) *
              lowOwnerRetainedCoefficientOutgoingEnergy R parent coefficient := by
        unfold lowOwnerRetainedCoefficientOutgoingEnergy
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro r _hr
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro child _hchild
        exact ih child
      have hout :=
        lowOwnerRetainedCoefficientOutgoingEnergy_le_218_over_225
          R parent coefficient
      calc
        lowOwnerRetainedCoefficientParentEnergy coefficient parent +
            (∑ r ∈ primesUpTo (squareRootEndpoint R),
              ∑ child ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent r,
                lowOwnerRetainedCoefficientTreeEnergy R d child coefficient) ≤
          lowOwnerRetainedCoefficientParentEnergy coefficient parent +
            (225 / 7 : ℝ) *
              lowOwnerRetainedCoefficientOutgoingEnergy R parent coefficient :=
                add_le_add_left hchildren _
        _ ≤ (225 / 7 : ℝ) *
            lowOwnerRetainedCoefficientParentEnergy coefficient parent := by
              nlinarith

end RHLean.Proof
