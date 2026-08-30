import Mathlib
import RHLean.Proof.SquareRootLowPrimeCanonicalToggleRootCharge

/-!
# Alternating root-fibre compression

The canonical toggle charge is the last still-admissible root state of the
alternating displacement process.  The repository already proves that this one
root recovers the complete residual datum:

* in the no-toggle case it is the canonical first-failure root itself;
* in the unstable case it recovers the larger pivot and old base by canonical
  factorization, then the least failed smaller pivot;
* the two tags cannot share a root because the canonical failing prime lies on
  opposite sides of the root's largest prime factor.

Therefore two residual alternating units cannot survive over the same
canonical root.  This is the fibrewise compression required by the no-liberty
gate: after creation/response displacement has been normalized to canonical
toggle data, every canonical root carries at most one residual unit.

No estimate, prime-count input, covariance argument, or arbitrary finite-set
equivalence is used here.
-/

noncomputable section

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- The unstable-only fibre statement, exposed for downstream displacement
arguments that have already selected the double-toggle orientation. -/
theorem squareRootLowPrimeAlternatingUnstableRootFiber_card_le_one
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

/-- **Alternating root-fibre compression.**  Canonical no-toggle and unstable
residuals together have at most one surviving unit over any fixed root. -/
theorem squareRootLowPrimeAlternatingRootFiber_card_le_one
    {K U B r : ℕ}
    (S : Finset SquareRootLowPrimeCanonicalToggleState)
    (hdata : ∀ z ∈ S,
      SquareRootLowPrimeCanonicalToggleData K U B z) :
    (S.filter fun z => squareRootLowPrimeCanonicalToggleRootCharge z = r).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro x hx y hy
  have hxData := Finset.mem_filter.mp hx
  have hyData := Finset.mem_filter.mp hy
  apply squareRootLowPrimeCanonicalToggleRootCharge_injective
    (hdata x hxData.1) (hdata y hyData.1)
  exact hxData.2.trans hyData.2.symm

end RHLean.Proof
