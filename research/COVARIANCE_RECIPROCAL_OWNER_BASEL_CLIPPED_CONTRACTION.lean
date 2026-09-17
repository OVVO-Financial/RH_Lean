import Mathlib
import «research.COVARIANCE_RECIPROCAL_OWNER_BASEL_CONTRACTION»
import «research.ZERO_TARGET_CLIPPED_OWNER_ENERGY_CONTRACTION»

/-!
# Basel-sharpened contraction on the actual clipped covariance exit

The critical clipped outgoing energy is already proved to be a nonnegative
sub-energy of the full reciprocal owner graph.  The Basel sharpening therefore
passes to the physical clipped exit without any new estimate.
-/

noncomputable section

namespace RHLean.Proof

/-- The genuinely clipped critical exit inherits the sharpened `218/225`
coefficient. -/
theorem postRootCovarianceCriticalClippedOutgoingEnergy_le_218_over_225
    (W : ℕ) (parent : ℕ × ℕ) :
    postRootCovarianceCriticalClippedOutgoingEnergy W parent ≤
      (218 / 225 : ℝ) * postRootCovarianceReciprocalPairEnergy parent := by
  exact le_trans
    (postRootCovarianceCriticalClippedOutgoingEnergy_le_outgoingEnergy W parent)
    (postRootCovarianceReciprocalOutgoingEnergy_le_218_over_225 W parent)

end RHLean.Proof
