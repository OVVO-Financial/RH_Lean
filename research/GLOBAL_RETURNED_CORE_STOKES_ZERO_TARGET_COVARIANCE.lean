import Mathlib
import «research.GLOBAL_RETURNED_CORE_STOKES_GLOBAL_IDENTIFICATION»
import «research.GLOBAL_RETURNED_CORE_SIGNED_OWNER_TELESCOPE»
import «research.ZERO_TARGET_PARTIAL_MOMENT_COVARIANCE»

/-!
# Final Stokes boundary in NNS zero-target covariance currency

The target-zero partial-moment identity separates the diagonal self-energy from
the signed off-diagonal covariance exactly.  On a self pair the divergent
partial moments vanish and the co-partial mass is `x^2`; hence the diagonal in
the one-amplitude Gram is pure self-energy, not part of the RH-critical signed
cancellation.

Combining the already-compiled first-owner Gram Fubini with the global signed
Stokes identification gives

  FinalStokes_R = 2 * Gram_R
                = 2 * (CoPartialCross_0 - DivergentCross_0).

Thus every later owner-cube argument may work directly on the off-diagonal
same-sign versus opposite-sign excess.  No estimate is introduced here.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- At target zero a self pair has no divergent partial-moment mass. -/
@[simp] theorem zeroTargetDivergentPair_self (x : ℝ) :
    zeroTargetDivergentPair x x = 0 := by
  by_cases hx : 0 ≤ x
  · simp [zeroTargetDivergentPair, zeroTargetDLPM, zeroTargetDUPM,
      zeroTargetLowerPart, zeroTargetUpperPart, abs_of_nonneg hx]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    simp [zeroTargetDivergentPair, zeroTargetDLPM, zeroTargetDUPM,
      zeroTargetLowerPart, zeroTargetUpperPart, abs_of_nonpos hx']

/-- Consequently the zero-target co-partial self mass is exactly the square. -/
@[simp] theorem zeroTargetCoPartialPair_self (x : ℝ) :
    zeroTargetCoPartialPair x x = x ^ 2 := by
  have h := zeroTargetCoPartial_sub_divergent_eq_mul x x
  rw [zeroTargetDivergentPair_self] at h
  simpa [pow_two] using h

/-- The one-amplitude diagonal is literally the sum of target-zero co-partial
self masses. -/
theorem lowOwnerZeroFrequencyMobiusDiagonal_eq_zeroTargetCoPartialSelf
    (R : ℕ) :
    lowOwnerZeroFrequencyMobiusDiagonal R =
      ∑ n ∈ Finset.range (squareRootEndpoint R + 1),
        zeroTargetCoPartialPair
          (lowOwnerZeroFrequencyMobiusSite R n)
          (lowOwnerZeroFrequencyMobiusSite R n) := by
  unfold lowOwnerZeroFrequencyMobiusDiagonal signedBlockEnergy
  apply Finset.sum_congr rfl
  intro n _hn
  rw [zeroTargetCoPartialPair_self]

/-- The full one-amplitude off-diagonal Gram is exactly the NNS target-zero
co-partial excess. -/
theorem lowOwnerZeroFrequencyMobiusGram_eq_zeroTargetCrossExcess
    (R : ℕ) :
    lowOwnerZeroFrequencyMobiusGram R =
      zeroTargetCoPartialCross
          (lowOwnerZeroFrequencyMobiusSite R)
          (squareRootEndpoint R + 1) -
        zeroTargetDivergentCross
          (lowOwnerZeroFrequencyMobiusSite R)
          (squareRootEndpoint R + 1) := by
  unfold lowOwnerZeroFrequencyMobiusGram
  exact signedBlockCrossCovariance_eq_zeroTargetCoPartial_sub_divergent
    (lowOwnerZeroFrequencyMobiusSite R) (squareRootEndpoint R + 1)

/-- **Diagonal-free final Stokes identity.**  The physical Stokes boundary is
twice the actual off-diagonal Gram; the self-energy diagonal has cancelled
exactly before any inequality is applied. -/
theorem lowOwnerCanonicalSignedStokesFinalBoundary_eq_two_mul_mobiusGram
    {R : ℕ} (hR : 2 ≤ R) :
    lowOwnerCanonicalSignedStokesFinalBoundary R =
      2 * lowOwnerZeroFrequencyMobiusGram R := by
  rw [← sum_lowOwnerFirstOwnerSignedCellTelescope_eq_finalStokesBoundary hR]
  rw [← two_mul_sum_lowOwnerZeroFrequencyFirstOwnerGram_eq_signedOwnerTelescope]
  rw [← lowOwnerZeroFrequencyMobiusGram_eq_sum_firstOwnerGram]

/-- **NNS zero-target form of the final Stokes boundary.** -/
theorem lowOwnerCanonicalSignedStokesFinalBoundary_eq_two_zeroTargetCrossExcess
    {R : ℕ} (hR : 2 ≤ R) :
    lowOwnerCanonicalSignedStokesFinalBoundary R =
      2 *
        (zeroTargetCoPartialCross
            (lowOwnerZeroFrequencyMobiusSite R)
            (squareRootEndpoint R + 1) -
          zeroTargetDivergentCross
            (lowOwnerZeroFrequencyMobiusSite R)
            (squareRootEndpoint R + 1)) := by
  rw [lowOwnerCanonicalSignedStokesFinalBoundary_eq_two_mul_mobiusGram hR,
    lowOwnerZeroFrequencyMobiusGram_eq_zeroTargetCrossExcess]

end RHLean.Proof
