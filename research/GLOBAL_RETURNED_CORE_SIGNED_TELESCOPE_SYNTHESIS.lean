import Mathlib
import «research.GLOBAL_RETURNED_CORE_SIGNED_OWNER_TELESCOPE»
import «research.GLOBAL_RETURNED_CORE_SYNTHESIS»

/-!
# Signed owner telescope as the sole quantitative seam

The exact finite Fubini and compensated-cell identities remove the aggregate
first-owner Gram as a separate object.  This file name-locks the remaining
estimate directly on the signed telescope

  (L-J)^2 - L^2 - J^2 - 2 C J

summed over actual first-separation owners and lower-signature cells.

This is definitionally equivalent to the existing `LowOwnerFirstOwnerGramBound`
with the same constant, hence any root-scale bound on this full signed quantity
feeds the already-compiled factor-four/RH consumer without another loss.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Root-scale bound on the *full signed* first-owner telescope.  Complete
chronology and the mixed clipped exit remain coupled in the hypothesis. -/
def LowOwnerSignedOwnerTelescopeBound (C : ℝ) : Prop :=
  ∀ R : ℕ, ∀ K : ℝ,
    56 ≤ R →
    LowerMertensCriticalEnvelope R K →
    (∑ p ∈ primesUpTo (squareRootEndpoint R),
      ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
        lowOwnerFirstOwnerSignedCellTelescope R p sig) ≤
      C * (R : ℝ) ^ 2 * K

/-- The new signed-telescope target is exactly the old aggregate first-owner
Gram target, not a stronger surrogate and not a weaker bookkeeping statement. -/
theorem lowOwnerSignedOwnerTelescopeBound_iff_firstOwnerGramBound
    (C : ℝ) :
    LowOwnerSignedOwnerTelescopeBound C ↔
      LowOwnerFirstOwnerGramBound C := by
  constructor
  · intro htel R K hR hK
    have h := htel R K hR hK
    rw [← two_mul_sum_lowOwnerZeroFrequencyFirstOwnerGram_eq_signedOwnerTelescope]
      at h
    exact h
  · intro hgram R K hR hK
    have h := hgram R K hR hK
    rw [two_mul_sum_lowOwnerZeroFrequencyFirstOwnerGram_eq_signedOwnerTelescope]
      at h
    exact h

/-- Direct conversion to the already-compiled first-owner seam. -/
theorem firstOwnerGramBound_of_signedOwnerTelescopeBound
    {C : ℝ} (h : LowOwnerSignedOwnerTelescopeBound C) :
    LowOwnerFirstOwnerGramBound C :=
  (lowOwnerSignedOwnerTelescopeBound_iff_firstOwnerGramBound C).mp h

/-- **Signed-telescope RH closure.**  It is now sufficient to bound the exact
joint chronology quantity; no parent=daughters identity or ownerwise frame
bound is needed downstream. -/
theorem riemannHypothesis_of_signedOwnerTelescopeBound
    {C : ℝ} (hC : 0 ≤ C)
    (h : LowOwnerSignedOwnerTelescopeBound C) :
    RiemannHypothesis :=
  riemannHypothesis_of_firstOwnerGramBound hC
    (firstOwnerGramBound_of_signedOwnerTelescopeBound h)

end RHLean.Proof
