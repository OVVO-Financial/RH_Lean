import Mathlib
import «research.GLOBAL_RETURNED_CORE_STOKES_TERMINAL_CLASSIFICATION»
import «research.GLOBAL_RETURNED_CORE_SIGNED_OWNER_TELESCOPE»
import «research.GLOBAL_RETURNED_CORE_SYNTHESIS»

/-!
# Final signed Stokes boundary to the existing RH consumer

The signed-first program has already reduced the aggregate first-owner telescope
exactly to one final physical boundary ledger.  This file name-locks the sole
remaining quantitative statement directly on that ledger and proves that it is
exactly sufficient for the existing returned-core RH consumer.

No new estimate is made here.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Root-scale upper bound on the *final signed Stokes boundary*.

This is intentionally one-sided: the downstream Gram/RH consumer only needs an
upper bound.  No absolute value and no packetwise norm is inserted. -/
def LowOwnerFinalStokesBoundaryBound (C : ℝ) : Prop :=
  ∀ R : ℕ, ∀ K : ℝ,
    56 ≤ R →
    LowerMertensCriticalEnvelope R K →
    lowOwnerCanonicalSignedStokesFinalBoundary R ≤
      C * (R : ℝ) ^ 2 * K

/-- The final signed Stokes boundary bound is literally the existing aggregate
first-owner Gram bound, after the two compiled exact identities are rewritten. -/
theorem firstOwnerGramBound_of_finalStokesBoundaryBound
    {C : ℝ}
    (hBoundary : LowOwnerFinalStokesBoundaryBound C) :
    LowOwnerFirstOwnerGramBound C := by
  intro R K hR hK
  have hOwner :=
    two_mul_sum_lowOwnerZeroFrequencyFirstOwnerGram_eq_signedOwnerTelescope R
  have hStokes :=
    sum_lowOwnerFirstOwnerSignedCellTelescope_eq_finalStokesBoundary
      (R := R) (by omega : 2 ≤ R)
  calc
    2 * (∑ p ∈ primesUpTo (squareRootEndpoint R),
        lowOwnerZeroFrequencyFirstOwnerGram R p) =
      lowOwnerCanonicalSignedStokesFinalBoundary R := by
        rw [hOwner, hStokes]
    _ ≤ C * (R : ℝ) ^ 2 * K := hBoundary R K hR hK

/-- Conversely, the existing first-owner bound immediately bounds the same
final signed boundary.  Thus the two quantitative seams are definitionally
separate names for the same compiled signed quantity. -/
theorem finalStokesBoundaryBound_of_firstOwnerGramBound
    {C : ℝ}
    (hGram : LowOwnerFirstOwnerGramBound C) :
    LowOwnerFinalStokesBoundaryBound C := by
  intro R K hR hK
  have hOwner :=
    two_mul_sum_lowOwnerZeroFrequencyFirstOwnerGram_eq_signedOwnerTelescope R
  have hStokes :=
    sum_lowOwnerFirstOwnerSignedCellTelescope_eq_finalStokesBoundary
      (R := R) (by omega : 2 ≤ R)
  have h := hGram R K hR hK
  rw [hOwner, hStokes] at h
  exact h

/-- **Final signed-boundary RH closure.**  Any nonnegative absolute constant
controlling the explicit final Stokes ledger at root scale closes the already
compiled returned-core chain to RH. -/
theorem riemannHypothesis_of_finalStokesBoundaryBound
    {C : ℝ} (hC : 0 ≤ C)
    (hBoundary : LowOwnerFinalStokesBoundaryBound C) :
    RiemannHypothesis :=
  riemannHypothesis_of_firstOwnerGramBound hC
    (firstOwnerGramBound_of_finalStokesBoundaryBound hBoundary)

end RHLean.Proof
