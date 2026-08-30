import Mathlib
import RHLean.Proof.SquareRootLowPrimeSecondToggleCharge

/-!
# Alternating root-fibre compression

The canonical second-toggle charge is the surviving root state of one genuine
alternating displacement corner.  The existing recovery theorem proves that
this root determines the larger pivot, the old base, and then the least failed
smaller pivot.  Therefore two residual alternating units cannot survive over
the same canonical root.

This is the fibrewise form needed by the no-liberty compression: after the
creation/response displacement has been normalized to canonical double-toggle
data, every canonical root carries at most one residual unit.

No estimate, prime-count input, covariance argument, or arbitrary finite-set
equivalence is used here.
-/

noncomputable section

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- **Alternating root-fibre compression.**  In any finite population of
canonical double-toggle displacement states, the fibre over one surviving root
has cardinality at most one. -/
theorem squareRootLowPrimeAlternatingRootFiber_card_le_one
    {K U B r : ℕ}
    (S : Finset SquareRootLowPrimeDoubleToggleState)
    (hdata : ∀ z ∈ S,
      SquareRootLowPrimeCanonicalDoubleToggleData K U B z) :
    (S.filter fun z => squareRootLowPrimeSecondToggleRootCharge z = r).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro x hx y hy
  have hxData := Finset.mem_filter.mp hx
  have hyData := Finset.mem_filter.mp hy
  apply squareRootLowPrimeSecondToggleRootCharge_injective
    (hdata x hxData.1) (hdata y hyData.1)
  exact hxData.2.trans hyData.2.symm

end RHLean.Proof
