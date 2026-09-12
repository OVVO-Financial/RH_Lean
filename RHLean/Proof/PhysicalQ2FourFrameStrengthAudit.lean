import RHLean.Proof.PhysicalQ2FourFrameTerminalSynthesis

/-!
# Strength audit for the factor-four q² recurrence

The post-#674 route isolates `PhysicalCompleteCellOddQ2EnergyStep C 4` as a
sufficient terminal input.  This file records the converse strength of that
input before any further parent-synthesis argument is attempted.

A factor-four step with a fixed additive coefficient is equivalent, up to a
change of constant, to a uniform linear bound for complete-cell Mertens energy.
Thus the factor-four recurrence is not merely a finite-overlap bookkeeping
lemma: proving it unconditionally proves the complete-cell strong Mertens scale
`M(4K)^2 = O(K)`.

The converse is elementary because the recursive daughter energies are
nonnegative.  No analytic input is used here.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

/-- Uniform linear Mertens energy on complete physical four-cells. -/
def CompleteCellMertensLinearBound : Prop :=
  ∃ A : ℚ, 0 ≤ A ∧
    ∀ K : ℕ, mertensEnergy (4 * K) ≤ A * (K : ℚ)

/-- A complete-cell linear Mertens-energy bound trivially supplies a factor-four
q² recurrence: every recursive daughter energy is nonnegative. -/
theorem physicalCompleteCell_fourFrameStep_of_linear
    {A : ℚ} (hA : 0 ≤ A)
    (hlinear : ∀ K : ℕ,
      mertensEnergy (4 * K) ≤ A * (K : ℚ)) :
    PhysicalCompleteCellOddQ2EnergyStep A 4 := by
  intro K
  let S : Finset ℕ := (primesUpTo (4 * K)).erase 2
  have hterm : ∀ q ∈ S,
      0 ≤ mertensEnergy ((4 * K) / (q * q)) := by
    intro q _hq
    unfold mertensEnergy
    positivity
  have hsum :
      0 ≤ ∑ q ∈ S, mertensEnergy ((4 * K) / (q * q)) := by
    exact Finset.sum_nonneg hterm
  have hrec :
      0 ≤ 4 * ∑ q ∈ S, mertensEnergy ((4 * K) / (q * q)) := by
    positivity
  have hparent := hlinear K
  change mertensEnergy (4 * K) ≤ A * (K : ℚ) +
    4 * ∑ q ∈ S, mertensEnergy ((4 * K) / (q * q))
  linarith

/-- **Exact strength equivalence.** Existence of a fixed-coefficient factor-four
physical q² step is equivalent to uniform linear complete-cell Mertens energy.

The forward implication is the sharp `17/72` induction already compiled in
`PhysicalQ2FourFrameTerminalSynthesis`; the reverse implication uses only
nonnegativity of the daughter energies. -/
theorem exists_physicalCompleteCell_fourFrameStep_iff_linear :
    (∃ C : ℚ, 0 ≤ C ∧ PhysicalCompleteCellOddQ2EnergyStep C 4) ↔
      CompleteCellMertensLinearBound := by
  constructor
  · rintro ⟨C, hC, hstep⟩
    refine ⟨35 * (C + 6480), ?_, ?_⟩
    · nlinarith
    · exact physicalCompleteCell_fourFrameStep_implies_linear hC hstep
  · rintro ⟨A, hA, hlinear⟩
    exact ⟨A, hA, physicalCompleteCell_fourFrameStep_of_linear hA hlinear⟩

end RHLean.Proof
