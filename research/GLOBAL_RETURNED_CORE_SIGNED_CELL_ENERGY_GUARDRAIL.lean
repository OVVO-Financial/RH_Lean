import Mathlib
import «research.GLOBAL_RETURNED_CORE_SIGNATURE_FILTRATION»
import «research.GLOBAL_RETURNED_CORE_SIGNED_CELL_TELESCOPE»

/-!
# Legal cell-level energy guardrail

The signed cell telescope is a quadratic polarization decrement.  It is not the
square of one next-owner four-corner.  The strongest immediate nonnegative
majorant at the whole-cell level is instead the square of the full Dirichlet
incidence / signature-cell amplitude.

This file records that legal inequality explicitly.  It is useful as a
regression guardrail: any future owner-energy conversion must improve on this
only after preserving the prime-filtration telescope; summing this positive
majorant blindly over first owners would discard the inter-prime cancellation.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- **Whole-cell polarization is bounded by the full Dirichlet incidence
square.**  This is just `D^2 - B^2 - J^2 <= D^2`; it introduces no clipped
square. -/
theorem lowOwnerFirstOwnerSignedCellTelescope_le_dirichletIncidence_sq
    {R p : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    lowOwnerFirstOwnerSignedCellTelescope R p sig ≤
      lowOwnerFirstOwnerDirichletIncidenceAmplitude R p sig ^ 2 := by
  rw [← two_mul_lowOwnerFirstOwnerCellGram_eq_completeTelescope_sub_clippedCross hp]
  rw [two_mul_lowOwnerFirstOwnerCellGram_eq_dirichletIncidence_sq_sub_branches hp]
  have hb := sq_nonneg (lowOwnerFirstOwnerBaseAmplitude R p sig)
  have hj := sq_nonneg (lowOwnerFirstOwnerChildAmplitude R p sig)
  nlinarith

/-- In the existing signature coordinate, the same majorant is literally one
signature-cell square. -/
theorem lowOwnerFirstOwnerSignedCellTelescope_le_signatureCell_sq
    {R p : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    lowOwnerFirstOwnerSignedCellTelescope R p sig ≤
      lowOwnerFirstOwnerSignatureCellAmplitude R p sig ^ 2 := by
  rw [← lowOwnerFirstOwnerDirichletIncidenceAmplitude_eq_signatureCellAmplitude hp]
  exact lowOwnerFirstOwnerSignedCellTelescope_le_dirichletIncidence_sq hp

/-- Summing over one fixed first owner gives the corresponding pre-split
signature energy.  This is intentionally *not* summed over all owners here. -/
theorem sum_lowOwnerFirstOwnerSignedCellTelescope_le_signatureEnergy
    {R p : ℕ} (hp : p.Prime) :
    (∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
      lowOwnerFirstOwnerSignedCellTelescope R p sig) ≤
      lowOwnerFirstOwnerSignatureEnergy R p := by
  unfold lowOwnerFirstOwnerSignatureEnergy
  exact Finset.sum_le_sum fun sig _ =>
    lowOwnerFirstOwnerSignedCellTelescope_le_signatureCell_sq hp

end RHLean.Proof
