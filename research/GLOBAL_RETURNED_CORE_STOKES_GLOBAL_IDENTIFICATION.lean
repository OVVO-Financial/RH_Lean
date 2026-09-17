import Mathlib
import «research.GLOBAL_RETURNED_CORE_STOKES_TWO_STEP_BOUNDARY_NORMAL_FORM»
import «research.GLOBAL_RETURNED_CORE_STOKES_CROSS_AMPLITUDE_NORMAL_FORM»

/-!
# Global identification gate before any endpoint-frequency estimate

This file is the algebraic gate between the signed Stokes reduction and every
later harmonic estimate.  It deliberately contains no norm, square bound,
triangle inequality, frame estimate, or conductor estimate.

The final signed Stokes boundary is identified in two exact currencies:

* the global pair-weighted Dirichlet-polarization ledger on the actual
  first-owner/signature cells;
* the global base/returned cross-amplitude ledger `-2 B_{p,sigma} J_{p,sigma}`.

Any endpoint-frequency or corrected-conductor argument must first prove an
additional exact rewrite from one of these identified ledgers to its own
physical boundary packet.  The prime-period frame is not imported here.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Global Dirichlet-polarization ledger on the literal first-owner/signature
pair carriers. -/
def lowOwnerCanonicalSignedStokesDirichletPolarizationLedger
    (R : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo (squareRootEndpoint R),
    ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
      pairWeightedStokesMass
        (lowOwnerFirstOwnerSignedCellPairCarrier R p sig)
        (lowOwnerFirstOwnerDirichletPolarizationScalar R p)

/-- **Exact global Stokes/Dirichlet identification.**

After the signed Stokes telescope has been carried all the way to its physical
boundary, the final boundary is still exactly the original global
Dirichlet-polarization ledger.  No frequency model has been substituted. -/
theorem lowOwnerCanonicalSignedStokesFinalBoundary_eq_dirichletPolarizationLedger
    {R : ℕ} (hR : 2 ≤ R) :
    lowOwnerCanonicalSignedStokesFinalBoundary R =
      lowOwnerCanonicalSignedStokesDirichletPolarizationLedger R := by
  rw [← sum_lowOwnerFirstOwnerSignedCellTelescope_eq_finalStokesBoundary hR]
  unfold lowOwnerCanonicalSignedStokesDirichletPolarizationLedger
  apply Finset.sum_congr rfl
  intro p hpMem
  have hp : p.Prime := (mem_primesUpTo.mp hpMem).1
  apply Finset.sum_congr rfl
  intro sig _hsig
  exact lowOwnerFirstOwnerSignedCellTelescope_eq_pairWeightedStokesMass hp

/-- Global pure base/returned cross-amplitude ledger. -/
def lowOwnerCanonicalSignedStokesCrossAmplitudeLedger
    (R : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo (squareRootEndpoint R),
    ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
      (-2 * lowOwnerFirstOwnerBaseAmplitude R p sig *
        lowOwnerFirstOwnerReturnedChildParentAmplitude R p sig)

/-- **Exact global cross-amplitude identification.**  This is the quantity a
later frame is allowed to see: one signed `-2 B J` ledger, not three separately
bounded squares. -/
theorem lowOwnerCanonicalSignedStokesFinalBoundary_eq_crossAmplitudeLedger
    {R : ℕ} (hR : 2 ≤ R) :
    lowOwnerCanonicalSignedStokesFinalBoundary R =
      lowOwnerCanonicalSignedStokesCrossAmplitudeLedger R := by
  rw [← sum_lowOwnerFirstOwnerSignedCellTelescope_eq_finalStokesBoundary hR]
  simpa [lowOwnerCanonicalSignedStokesCrossAmplitudeLedger] using
    (sum_signedCellTelescope_eq_neg_two_sum_base_mul_returned R)

/-- The final boundary is, definitionally, the physically identified clip
ledger plus the exact zero/one-owner terminal ledger. -/
theorem lowOwnerCanonicalSignedStokesFinalBoundary_eq_clip_add_topTerminal
    (R : ℕ) :
    lowOwnerCanonicalSignedStokesFinalBoundary R =
      lowOwnerCanonicalSignedStokesClipBoundary R +
        lowOwnerCanonicalSignedStokesTopTerminalBoundary R := by
  rfl

end RHLean.Proof
