import Mathlib
import RHLean.Proof.StableFarRenewalOwnerDifferenceFubini
import RHLean.Proof.PostRootPartnerLogAlignment

/-!
# Final stable-far mismatch after the renewal transport collapse

The exact odd ChildFar cancellation and the global production Fubini remove the
many-to-one renewal chronology from the transport/far mismatch.

What remains is one coupled signed packet:

* near q2 high transport;
* the q2-or-deeper intermediate-prime tower;
* the multiplicity-one squarefree physical renewal boundary;
* the explicit owner-two correction;
* the terminal remainder.

No norm or estimate is introduced.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- **Complete renewal/terminal chronology collapse.**  After the odd ChildFar
population cancels, the original crossing-renewal plus terminal-product columns
are exactly the physical multiplicity-one renewal boundary, the explicit
owner-two centered correction, minus owner-two ChildFar, plus the coupled
terminal remainder.

The terminal remainder stays signed and assembled; it is not normed here. -/
theorem stableFarRenewalColumn_add_terminal_eq_physicalBoundary_add_ownerTwo
    (R : ℕ) (hR : 3 ≤ R) :
    stableFarRenewalColumn R + stableFarTerminalProductColumn R =
      stableFarRenewalProductionSignedBoundaryMass R +
        stableFarRenewalOwnerTwoCenteredTower R -
        (∑ dp ∈ lowWheelFarPrimeQ2ChildFarSlice R 2,
          canonicalMoebiusWeight dp.1) +
        farFourTerminalRemainder R := by
  have hinc :=
    stableFarRenewal_incidence_after_oddChildFar_cancellation R hR
  rw [stableFarRenewalOddOwnerDifferenceTower_eq_signedPhysicalBoundary] at hinc
  have hterminal :=
    lowWheelFarWallTerminalProducts_mass_eq_unit_add_owned R
  unfold stableFarRenewalColumn stableFarTerminalProductColumn
  rw [hterminal]
  unfold farFourTerminalRemainder
  linear_combination hinc

/-- **Corrected transport/far mismatch after the #786/#787 collapse.**
The odd ChildFar bulk and odd renewal multiplicities have disappeared
algebraically before energy. -/
theorem q2TransportFarMismatch_eq_near_sub_tower_sub_physicalBoundary_ownerTwo
    (R : ℕ) (hR : 56 ≤ R) :
    q2TransportFarMismatch R =
      (((squareEndpointQ2NearHighTransportColumn R : ℤ) : ℂ)) -
        (((squareEndpointQ2IntermediatePrimeTower R : ℤ) : ℂ)) -
        stableFarRenewalProductionSignedBoundaryMass R -
        stableFarRenewalOwnerTwoCenteredTower R +
        (∑ dp ∈ lowWheelFarPrimeQ2ChildFarSlice R 2,
          canonicalMoebiusWeight dp.1) -
        farFourTerminalRemainder R := by
  have hmis :=
    q2TransportFarMismatch_eq_compiled_near_sub_tower_sub_renewal_sub_terminal
      R hR
  have hchron :=
    stableFarRenewalColumn_add_terminal_eq_physicalBoundary_add_ownerTwo
      R (by omega)
  linear_combination hmis - hchron

/-- The final q2 survivor correction in the same physical normal form. -/
theorem finalQ2SurvivorCorrection_eq_root_sub_near_add_tower_add_physicalBoundary
    (R : ℕ) (hR : 56 ≤ R) :
    finalQ2SurvivorCorrection R =
      finalQ2RootReassemblyBoundary R -
        (((squareEndpointQ2NearHighTransportColumn R : ℤ) : ℂ)) +
        (((squareEndpointQ2IntermediatePrimeTower R : ℤ) : ℂ)) +
        stableFarRenewalProductionSignedBoundaryMass R +
        stableFarRenewalOwnerTwoCenteredTower R -
        (∑ dp ∈ lowWheelFarPrimeQ2ChildFarSlice R 2,
          canonicalMoebiusWeight dp.1) +
        farFourTerminalRemainder R := by
  rw [finalQ2SurvivorCorrection_eq_root_sub_q2TransportFarMismatch R hR,
    q2TransportFarMismatch_eq_near_sub_tower_sub_physicalBoundary_ownerTwo
      R hR]
  ring

/-- The exact final low/high comparison after all odd stable-far bulk has been
removed.  The lower Mertens daughter column is untouched; every other
non-root term is displayed in the single physical packet above. -/
theorem finalCompensatedLowHighDifference_eq_neg_mertensColumn_add_reducedPacket
    (R : ℕ) (hR : 56 ≤ R) :
    finalCompensatedLowHighDifference R =
      -(((squareEndpointQ2MertensColumn R : ℤ) : ℂ)) +
        finalQ2RootReassemblyBoundary R -
        (((squareEndpointQ2NearHighTransportColumn R : ℤ) : ℂ)) +
        (((squareEndpointQ2IntermediatePrimeTower R : ℤ) : ℂ)) +
        stableFarRenewalProductionSignedBoundaryMass R +
        stableFarRenewalOwnerTwoCenteredTower R -
        (∑ dp ∈ lowWheelFarPrimeQ2ChildFarSlice R 2,
          canonicalMoebiusWeight dp.1) +
        farFourTerminalRemainder R := by
  rw [finalCompensatedLowHighDifference_eq_neg_mertensColumn_add_survivor
      R hR,
    finalQ2SurvivorCorrection_eq_root_sub_near_add_tower_add_physicalBoundary
      R hR]
  ring

end RHLean.Proof
