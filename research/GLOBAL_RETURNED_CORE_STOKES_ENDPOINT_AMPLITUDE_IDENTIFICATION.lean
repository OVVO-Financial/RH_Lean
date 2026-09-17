import Mathlib
import «research.GLOBAL_RETURNED_CORE_STOKES_GLOBAL_IDENTIFICATION»
import «research.GLOBAL_RETURNED_CORE_SIGNED_OWNER_TELESCOPE»
import «research.LOW_OWNER_AMPLITUDE_MELLIN_LEDGER_SPLICE»

/-!
# Final Stokes boundary as the exact endpoint Mertens amplitude

This is the last algebraic identification required before an endpoint-frequency
estimate is allowed to enter.

The signed Stokes theorem identifies the global first-owner telescope with the
literal physical boundary.  Independently, the one-amplitude Gram identity says
that the squared physical AMP remainder is the elementary diagonal plus that
same signed telescope.  Finally the Mellin splice identifies the remainder at
zero frequency with

  Corr_R - sum_q M(Y_q)/q.

Combining those exact identities gives

  B_R^Stokes = ||Corr_R - sum_q M(Y_q)/q||^2 - Diag_R.

Thus the Stokes boundary has genuinely recombined to the repository's actual
endpoint Mertens amplitude before any Fourier/frame bound is used.  No
inequality appears in this file.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- The final physical Stokes boundary is exactly the full AMP remainder energy
minus the already-isolated diagonal. -/
theorem lowOwnerCanonicalSignedStokesFinalBoundary_eq_remainderNormSq_sub_diagonal
    {R : ℕ} (hR : 56 ≤ R) :
    lowOwnerCanonicalSignedStokesFinalBoundary R =
      ‖lowOwnerPhysicalAmplitudeRemainder R 0‖ ^ 2 -
        lowOwnerZeroFrequencyMobiusDiagonal R := by
  have hsq :=
    norm_sq_lowOwnerPhysicalAmplitudeRemainder_zero_eq_diagonal_add_signedOwnerTelescope
      R hR
  have hboundary :=
    sum_lowOwnerFirstOwnerSignedCellTelescope_eq_finalStokesBoundary
      (R := R) (by omega)
  rw [hboundary] at hsq
  linarith

/-- **Exact endpoint-Mertens recombination of the final Stokes boundary.** -/
theorem lowOwnerCanonicalSignedStokesFinalBoundary_eq_endpointGapNormSq_sub_diagonal
    {R : ℕ} (hR : 56 ≤ R) :
    lowOwnerCanonicalSignedStokesFinalBoundary R =
      ‖squareRootCanonicalRoughCorrelation R -
          lowOwnerReciprocalMertensColumn R‖ ^ 2 -
        lowOwnerZeroFrequencyMobiusDiagonal R := by
  rw [lowOwnerCanonicalSignedStokesFinalBoundary_eq_remainderNormSq_sub_diagonal hR,
    lowOwnerPhysicalAmplitudeRemainder_zero_eq_correlation_sub_reciprocalColumn
      R hR]

/-- Same endpoint identity in the forward daughter-column orientation. -/
theorem lowOwnerCanonicalSignedStokesFinalBoundary_eq_reciprocalColumnGapNormSq_sub_diagonal
    {R : ℕ} (hR : 56 ≤ R) :
    lowOwnerCanonicalSignedStokesFinalBoundary R =
      ‖lowOwnerReciprocalMertensColumn R -
          squareRootCanonicalRoughCorrelation R‖ ^ 2 -
        lowOwnerZeroFrequencyMobiusDiagonal R := by
  rw [lowOwnerCanonicalSignedStokesFinalBoundary_eq_endpointGapNormSq_sub_diagonal hR]
  have hrev :
      ‖squareRootCanonicalRoughCorrelation R -
          lowOwnerReciprocalMertensColumn R‖ =
        ‖lowOwnerReciprocalMertensColumn R -
          squareRootCanonicalRoughCorrelation R‖ :=
    norm_sub_rev _ _
  rw [hrev]

end RHLean.Proof
