import Mathlib
import «research.GLOBAL_RETURNED_CORE_FIRST_OWNER_GRAM_TO_CELLS»
import «research.GLOBAL_RETURNED_CORE_SIGNED_CELL_TELESCOPE»

/-!
# Global signed first-owner telescope

After the exact unordered-to-cell Fubini, the local compensated cell identity
can be summed without loss.  The cell telescope itself is defined in the local
cell module; this file only performs the global owner/signature reindexing.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

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
  exact
    two_mul_lowOwnerFirstOwnerCellGram_eq_completeTelescope_sub_clippedCross hp

/-- **Global signed-owner telescope.** -/
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
signed owner telescope. -/
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
