import Mathlib
import «research.STABLE_FAR_GLOBAL_RETURNED_MEMORY_FUBINI»
import «research.LOW_OWNER_AMPLITUDE_MELLIN_LEDGER_SPLICE»
import «research.LOW_OWNER_PHYSICAL_CENSUS_CORRELATION»

/-!
# Global returned-coordinate normal form of the AMP remainder

The returned-fibre reciprocal normalization is globalized by
`STABLE_FAR_GLOBAL_RETURNED_MEMORY_FUBINI`.  This file splices that identity
back into the full stable-far census and then into the zero-frequency AMP
remainder before any norm is taken.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis

attribute [local instance] Classical.propDecidable

def stableFarGlobalReturnedReciprocalMass (R : ℕ) : ℂ :=
  ∑ rp ∈ stableFarReturnedCoordinatePairs R,
    stableFarReturnedPhysicalReciprocalCenteredMass R rp.1 rp.2

def stableFarGlobalReturnedEulerMemoryMass (R : ℕ) : ℂ :=
  ∑ rp ∈ stableFarReturnedCoordinatePairs R,
    stableFarReturnedPhysicalEulerMemoryMass R rp.1 rp.2

theorem farFourQ2CenteredTower_eq_globalReturnedReciprocal_add_memory
    (R : ℕ) :
    farFourQ2CenteredTower R =
      stableFarGlobalReturnedReciprocalMass R +
        stableFarGlobalReturnedEulerMemoryMass R := by
  simpa [stableFarGlobalReturnedReciprocalMass,
    stableFarGlobalReturnedEulerMemoryMass] using
    farFourQ2CenteredTower_eq_sum_reciprocal_add_memory R

theorem lowWheelFrozenTopFarResidual_eq_neg_globalReturnedReciprocal_sub_memory_sub_terminal
    (R : ℕ) (hR : 56 ≤ R) :
    lowWheelFrozenTopFarResidual R =
      -stableFarGlobalReturnedReciprocalMass R -
        stableFarGlobalReturnedEulerMemoryMass R -
        farFourTerminalRemainder R := by
  rw [lowWheelFrozenTopFarResidual_eq_neg_q2CenteredTower_sub_terminal R hR,
    farFourQ2CenteredTower_eq_globalReturnedReciprocal_add_memory R]
  ring

theorem lowOwnerPhysicalFarCensus_eq_neg_globalReturnedReciprocal_sub_memory_sub_terminal
    (R : ℕ) (hR : 56 ≤ R) :
    lowOwnerPhysicalFarCensus R =
      -stableFarGlobalReturnedReciprocalMass R -
        stableFarGlobalReturnedEulerMemoryMass R -
        farFourTerminalRemainder R := by
  rw [lowOwnerPhysicalFarCensus_eq_frozenTopFarResidual R hR,
    lowWheelFrozenTopFarResidual_eq_neg_globalReturnedReciprocal_sub_memory_sub_terminal
      R hR]

theorem squareRootCanonicalRoughCorrelation_eq_neg_globalReturnedPackets_sub_root
    (R : ℕ) (hR : 56 ≤ R) :
    squareRootCanonicalRoughCorrelation R =
      -stableFarGlobalReturnedReciprocalMass R -
        stableFarGlobalReturnedEulerMemoryMass R -
        farFourTerminalRemainder R -
        frozenTopFarRoughRootCorrection R := by
  rw [squareRootCanonicalRoughCorrelation_eq_physicalFarCensus_sub_root R hR,
    lowOwnerPhysicalFarCensus_eq_neg_globalReturnedReciprocal_sub_memory_sub_terminal
      R hR]

def lowOwnerReturnedAmplitudeCore (R : ℕ) : ℂ :=
  lowOwnerReciprocalMertensColumn R +
    stableFarGlobalReturnedReciprocalMass R +
    stableFarGlobalReturnedEulerMemoryMass R +
    farFourTerminalRemainder R

theorem lowOwnerPhysicalAmplitudeRemainder_zero_eq_neg_returnedCore_sub_root
    (R : ℕ) (hR : 56 ≤ R) :
    lowOwnerPhysicalAmplitudeRemainder R 0 =
      -lowOwnerReturnedAmplitudeCore R -
        frozenTopFarRoughRootCorrection R := by
  rw [lowOwnerPhysicalAmplitudeRemainder_zero_eq_correlation_sub_reciprocalColumn
      R hR,
    squareRootCanonicalRoughCorrelation_eq_neg_globalReturnedPackets_sub_root
      R hR]
  unfold lowOwnerReturnedAmplitudeCore
  ring

theorem norm_returnedAmplitudeRootCorrection_le_eight_root
    (R : ℕ) (hR : 56 ≤ R) :
    ‖frozenTopFarRoughRootCorrection R‖ ≤ 8 * (R : ℝ) :=
  norm_frozenTopFarRoughRootCorrection_le_eight_root R hR

end RHLean.Proof
