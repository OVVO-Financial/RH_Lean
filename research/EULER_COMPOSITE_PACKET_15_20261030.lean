import Mathlib
import «research.EULER_PHYSICAL_COMPLETE_PACKET_20261030»

/-!
# A CLOSED actual composite packet: original products 15 and 30

Unlike a symbolic binary packet with an assumed coefficient c, the weights
here are COMPUTED from the original Mobius factor pairs:
alpha_15=+2 (owners (1,15) and (3,5));
alpha_30=-4 (owners (1,30),(2,15),(3,10),(5,6)).

The first root with ALL these original pairs admitted is R=31. Before that,
the source retains nonzero signed moving-admission corrections. This module
certifies both the ACTUAL completed principal and the individual composite
coefficient pairing; no generic alpha_(2d) identity is assumed.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0

noncomputable section
namespace RHLean.Proof

theorem eulerCompletedProductCoeff_fifteen :
    eulerCompletedProductCoeff 15 = 2 := by
  decide +kernel

theorem eulerCompletedProductCoeff_thirty :
    eulerCompletedProductCoeff 30 = -4 := by
  decide +kernel

theorem eulerPacketRootPrincipal_fifteen :
    eulerPacketRootPrincipal 15 = 14 / 45 := by
  decide +kernel

theorem eulerPacketRootPrincipal_thirty :
    eulerPacketRootPrincipal 30 = 73 / 180 := by
  decide +kernel

/-- The actual odd-composite and even-composite coefficients close together,
not by assuming a generic arithmetic coefficient relation. -/
theorem eulerDoublingCoeffMismatch_fifteen :
    eulerDoublingCoeffMismatch 15 = 0 := by
  norm_num [eulerDoublingCoeffMismatch,
    eulerCompletedProductCoeff_fifteen,
    eulerCompletedProductCoeff_thirty]

/-- The positive-root principal means obey the true completed pairing law. -/
theorem eulerCompletedPacketPrincipalDefect_fifteen :
    eulerCompletedPacketPrincipalDefect 15 = 0 := by
  norm_num [eulerCompletedPacketPrincipalDefect,
    eulerCompletedProductCoeff_fifteen,
    eulerPacketRootPrincipal_fifteen,
    eulerPacketRootPrincipal_thirty]

/-- Principal completed mass is -2, NOT a centered zero. -/
theorem eulerCompletedPacketPrincipal_fifteen :
    eulerCompletedPacketPrincipal 15 = -2 := by
  norm_num [eulerCompletedPacketPrincipal,
    eulerCompletedProductCoeff_fifteen,
    eulerCompletedProductCoeff_thirty,
    eulerPacketRootPrincipal_fifteen,
    eulerPacketRootPrincipal_thirty]

/-- Every root, even before all original owners are admitted, is the exact
two-composite binary packet PLUS the signed missing-owner activation. -/
theorem eulerPhysicalOddPacket_fifteen_all_roots (R : ℕ) :
    eulerPhysicalOddPacket R 15 =
      nativeEulerOddDoublingPacket 2 15 R +
      eulerPacketActivationCorrection R 15 := by
  rw [eulerPhysicalOddPacket_exact_decomposition]
  rw [eulerCompletedProductCoeff_fifteen,
    eulerDoublingCoeffMismatch_fifteen]
  ring

/-- Once all 30-sized originals are admitted, the true physical packet is
exactly the completed packet and its actual physical principal is -2. -/
theorem eulerPhysicalOddPacket_fifteen_after_last_owner
    (R : ℕ) (hR : 30 < R) :
    eulerPhysicalOddPacket R 15 =
      nativeEulerOddDoublingPacket 2 15 R := by
  rw [eulerPhysicalOddPacket_fifteen_all_roots,
    eulerPacketActivationCorrection_eq_zero R 15 (by omega)]
  ring

theorem eulerPhysicalPacketPrincipal_fifteen_after_last_owner
    (R : ℕ) (hR : 30 < R) :
    eulerPhysicalPacketPrincipal R 15 = -2 := by
  have h15 := eulerMovingProductCoeff_eq_completed R 15 (by omega)
  have h30 := eulerMovingProductCoeff_eq_completed R 30 hR
  unfold eulerPhysicalPacketPrincipal
  rw [h15, h30]
  exact eulerCompletedPacketPrincipal_fifteen

/-- Actual period-normalized square energy is exactly 4 at every physical
root where both composite product families are fully admitted. -/
theorem eulerPhysicalOddPacket_fifteen_energy
    (R : ℕ) (hR : 30 < R) :
    (eulerPhysicalOddPacket R 15 + 2) ^ 2 = 4 := by
  rw [eulerPhysicalOddPacket_fifteen_after_last_owner R hR]
  have h := nativeEulerOddDoublingPacket_centered_sq (2 : ℚ)
    (d := 15) (R := R) (by norm_num : (0 : ℕ) < 15)
  norm_num at h
  exact h

/-- Exact original-source admission already occurs before root 31, so a
completed coefficient cannot replace the physical 30-column prematurely. -/
theorem eulerMovingProductCoeff_twenty_fifteen :
    eulerMovingProductCoeff 20 15 = 2 := by
  decide +kernel

theorem eulerMovingProductCoeff_twenty_thirty :
    eulerMovingProductCoeff 20 30 = -3 := by
  decide +kernel

theorem eulerPhysicalOddPacket_twenty_fifteen :
    eulerPhysicalOddPacket 20 15 = 3 / 5 := by
  decide +kernel

#print axioms eulerCompletedProductCoeff_fifteen
#print axioms eulerCompletedProductCoeff_thirty
#print axioms eulerPhysicalOddPacket_fifteen_all_roots
#print axioms eulerPhysicalPacketPrincipal_fifteen_after_last_owner
#print axioms eulerPhysicalOddPacket_fifteen_energy

end RHLean.Proof
