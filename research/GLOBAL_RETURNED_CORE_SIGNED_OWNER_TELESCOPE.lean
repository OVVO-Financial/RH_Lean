import Mathlib
import «research.GLOBAL_RETURNED_CORE_FIRST_OWNER_GRAM_TO_CELLS»

/-!
# Global signed first-owner telescope

After the exact unordered-to-cell Fubini, the local compensated cell identity
can be summed without loss.  This file records the resulting global normal
form for the actual AMP first-owner Gram.

For one owner/signature cell:

  2 G = (L - J)^2 - L^2 - J^2 - 2 C J,

where `L - J` is the literal daughter-crossing minus root-crossing amplitude
and `C` is the clipped p-child exit.  Summing first over signatures and then
over the actual prime owners gives the exact off-diagonal AMP covariance in
this form.  No absolute value, norm estimate, independence hypothesis, or
frame bound enters.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Signed telescope contribution of one first-owner cell. -/
def lowOwnerFirstOwnerSignedCellTelescope
    (R p : ℕ) (sig : Finset ℕ) : ℝ :=
  lowOwnerFirstOwnerCompensatedInteriorAmplitude R p sig ^ 2 -
    lowOwnerFirstOwnerAdmittedBaseAmplitude R p sig ^ 2 -
    lowOwnerFirstOwnerReturnedChildParentAmplitude R p sig ^ 2 -
    2 * lowOwnerFirstOwnerClippedAmplitude R p sig *
      lowOwnerFirstOwnerReturnedChildParentAmplitude R p sig

/-- For one genuine prime owner, twice the actual AMP first-owner Gram is the
sum of the exact signed cell telescopes. -/
theorem two_mul_lowOwnerZeroFrequencyFirstOwnerGram_eq_sum_signedCellTelescope
    {R p : ℕ} (hp : p.Prime) :
    2 * lowOwnerZeroFrequencyFirstOwnerGram R p =
      ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
        lowOwnerFirstOwnerSignedCellTelescope R p sig := by
  rw [lowOwnerZeroFrequencyFirstOwnerGram_eq_sum_cells hp, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro sig _hsig
  unfold lowOwnerFirstOwnerSignedCellTelescope
  exact
    two_mul_lowOwnerFirstOwnerCellGram_eq_completeTelescope_sub_clippedCross hp

/-- **Global signed-owner telescope.**  The complete off-diagonal first-owner
coherence of the AMP amplitude is exactly the sum of the compensated cell
energy increments and mixed clipped exits. -/
theorem two_mul_sum_lowOwnerZeroFrequencyFirstOwnerGram_eq_signedOwnerTelescope
    (R : ℕ) :
    2 * (∑ p ∈ primesUpTo (squareRootEndpoint R),
      lowOwnerZeroFrequencyFirstOwnerGram R p) =
      ∑ p ∈ primesUpTo (squareRootEndpoint R),
        ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
          lowOwnerFirstOwnerSignedCellTelescope R p sig := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hpMem
  exact
    two_mul_lowOwnerZeroFrequencyFirstOwnerGram_eq_sum_signedCellTelescope
      (mem_primesUpTo.mp hpMem).1

/-- The actual zero-frequency AMP remainder energy is diagonal plus the global
signed owner telescope.  This is the pre-estimate form needed by the factor-four
closure: the positive owner coherence is no longer isolated from chronology. -/
theorem norm_sq_lowOwnerPhysicalAmplitudeRemainder_zero_eq_diagonal_add_signedOwnerTelescope
    (R : ℕ) (hR : 56 ≤ R) :
    ‖lowOwnerPhysicalAmplitudeRemainder R 0‖ ^ 2 =
      lowOwnerZeroFrequencyMobiusDiagonal R +
        ∑ p ∈ primesUpTo (squareRootEndpoint R),
          ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
            lowOwnerFirstOwnerSignedCellTelescope R p sig := by
  rw [norm_sq_lowOwnerPhysicalAmplitudeRemainder_zero_eq_diagonal_add_firstOwners
      R hR,
    two_mul_sum_lowOwnerZeroFrequencyFirstOwnerGram_eq_signedOwnerTelescope]

end RHLean.Proof
