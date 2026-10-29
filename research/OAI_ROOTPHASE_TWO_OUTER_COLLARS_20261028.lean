import Mathlib

/-!
# Exact TWO-OUTER-collar cardinality and signed amplitude budget

The root-phase identity encodes ALL INTERNAL square-block boundaries
without smoothing them. After moving to ONE dyadic root-phase integral,
the only geometric support collars needed for a smooth outer Mellin
cutoff lie near physical n=H² and n=4H².

A width-W collar has at most 2W ORIGINAL integer sites, NOT H*W
sites. For any fully reassembled signed coefficient/phase difference
of norm at most 1 on those sites, its ENTIRE root-phase amplitude
error is at most 2W for every theta.

Therefore the theta-integrated squared error is <=4W², not H*W².
Taking W~H pays O(H²), strictly below H^(5/2-delta) if delta<1/2.

This bound is UNCONDITIONAL FINITE ARITHMETIC, and does not assert
that the resulting smooth outer cutoff belongs to the pinned
OpenAI inverse / marked profile family. Crucially the internal square
walls remain encoded in the coherent Fourier harmonic modes, whose
mixed k,l covariance cannot be discarded.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

def oaiRootAliasOuterCollarSites (H W : ℕ) : Finset ℕ :=
  Finset.Ico (H ^ 2) (H ^ 2 + W) ∪
    Finset.Ico (4 * H ^ 2 - W) (4 * H ^ 2)

/-- Only two OUTER collars, not H internal square-shell collars. -/
theorem oaiRootAliasOuterCollar_card_le_two (H W : ℕ) :
    (oaiRootAliasOuterCollarSites H W).card ≤ 2 * W := by
  unfold oaiRootAliasOuterCollarSites
  calc
    (Finset.Ico (H ^ 2) (H ^ 2 + W) ∪
        Finset.Ico (4 * H ^ 2 - W) (4 * H ^ 2)).card ≤
        (Finset.Ico (H ^ 2) (H ^ 2 + W)).card +
        (Finset.Ico (4 * H ^ 2 - W) (4 * H ^ 2)).card :=
          Finset.card_union_le _ _
    _ ≤ W + W := by simp; omega
    _ = 2 * W := by omega

/-- Fully signed finite source difference bounded coefficientwise by
one can have at most 2W physical OUTER-collar error. -/
theorem oaiRootAliasOuterCollar_norm_le_two
    (H W : ℕ) (a : ℕ → ℂ)
    (ha : ∀ n ∈ oaiRootAliasOuterCollarSites H W, ‖a n‖ ≤ 1) :
    ‖∑ n ∈ oaiRootAliasOuterCollarSites H W, a n‖ ≤
      (2 * W : ℕ) := by
  calc
    _ ≤ ∑ n ∈ oaiRootAliasOuterCollarSites H W, ‖a n‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _n ∈ oaiRootAliasOuterCollarSites H W, (1 : ℝ) :=
      Finset.sum_le_sum ha
    _ = ((oaiRootAliasOuterCollarSites H W).card : ℝ) := by simp
    _ ≤ (2 * W : ℕ) := by
      exact_mod_cast oaiRootAliasOuterCollar_card_le_two H W

/-- Pointwise squared amplitude of the original signed OUTER-collar
error is O(W²), with no extra factor H. -/
theorem oaiRootAliasOuterCollar_energy_le_four
    (H W : ℕ) (a : ℕ → ℂ)
    (ha : ∀ n ∈ oaiRootAliasOuterCollarSites H W, ‖a n‖ ≤ 1) :
    ‖∑ n ∈ oaiRootAliasOuterCollarSites H W, a n‖ ^ 2 ≤
      ((2 * W : ℕ) : ℝ) ^ 2 := by
  exact pow_le_pow_left₀ (norm_nonneg _)
    (oaiRootAliasOuterCollar_norm_le_two H W a ha) 2

#print axioms oaiRootAliasOuterCollar_card_le_two
#print axioms oaiRootAliasOuterCollar_norm_le_two
#print axioms oaiRootAliasOuterCollar_energy_le_four

end RHLean.Analysis
