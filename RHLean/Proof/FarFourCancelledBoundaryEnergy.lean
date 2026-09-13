import Mathlib
import RHLean.Proof.PostRootPartnerLogAlignment

/-!
# FAR-4 on the fully cancelled stable-far carrier

The stable-far routing is already exact before energy:

`frozenTopFar = descended q^2 packet + cancelled boundary packet`.

This module keeps those two signed packets together and rewrites FAR-4 as the
single off-diagonal cancellation inequality between them.  No triangle
inequality, separate packet bound, new arithmetic hypothesis, or change of
carrier is introduced.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

/-- Literal true-product q^2-descended packet from the stable-far census. -/
def farFourDescendedPacket (R : ℕ) : ℂ :=
  ∑ x ∈ lowWheelFarPrimeDescendedProductCarrier R,
    canonicalMoebiusWeight x.2

/-- Fully reassembled signed complement after the legitimate unit/crossing
cancellations have already been performed occurrence-by-occurrence. -/
def farFourCancelledBoundaryPacket (R : ℕ) : ℂ :=
  ∑ n ∈ lowWheelFarWallBoundaryProductHomes R,
    (lowWheelFarWallCancelledBoundaryCoefficient R n : ℂ) *
      canonicalMoebiusWeight n

/-- The genuine whole-daughter energy used by the existing FAR-4 terminal
consumer.  The owner `2` is erased exactly as in the terminal statement. -/
def farFourOddQ2DaughterEnergy (R : ℕ) : ℝ :=
  ∑ q ∈ (primesUpTo (R - 1)).erase 2,
    rawQ2ChildEnergyReal R q

/-- The merged signed census, written only in the two packets on which the
remaining energy cancellation acts. -/
theorem lowWheelFrozenTopFarResidual_eq_farFourDescended_add_cancelled
    (R : ℕ) (hR : 56 ≤ R) :
    lowWheelFrozenTopFarResidual R =
      farFourDescendedPacket R + farFourCancelledBoundaryPacket R := by
  simpa [farFourDescendedPacket, farFourCancelledBoundaryPacket] using
    lowWheelFrozenTopFarResidual_eq_descended_add_cancelledBoundary R hR

/-- Off-diagonal energy of the exact two-packet synthesis.  It is defined by
polarization at the already-assembled scalar level, so no coordinatewise
absolute value is taken. -/
def farFourCancelledCrossEnergy (R : ℕ) : ℝ :=
  ‖farFourDescendedPacket R + farFourCancelledBoundaryPacket R‖ ^ 2 -
    ‖farFourDescendedPacket R‖ ^ 2 -
    ‖farFourCancelledBoundaryPacket R‖ ^ 2

/-- Exact Gram expansion for the two signed packets. -/
theorem farFour_jointEnergy_eq_diagonal_add_cross (R : ℕ) :
    ‖farFourDescendedPacket R + farFourCancelledBoundaryPacket R‖ ^ 2 =
      ‖farFourDescendedPacket R‖ ^ 2 +
      ‖farFourCancelledBoundaryPacket R‖ ^ 2 +
      farFourCancelledCrossEnergy R := by
  unfold farFourCancelledCrossEnergy
  ring

/-- The remaining quantitative statement with the cancellation isolated in the
single cross-energy term.  This is not an extra hypothesis beyond FAR-4: the
next theorem proves literal equivalence. -/
def FarFourCancelledCrossEnergyStatement : Prop :=
  ∃ CF : ℝ, 0 ≤ CF ∧
    ∀ R : ℕ, ∀ K : ℝ,
      56 ≤ R →
      LowerMertensCriticalEnvelope R K →
      farFourCancelledCrossEnergy R ≤
        4 * farFourOddQ2DaughterEnergy R +
          CF * (R : ℝ) ^ 2 * K -
          ‖farFourDescendedPacket R‖ ^ 2 -
          ‖farFourCancelledBoundaryPacket R‖ ^ 2

/-- **Exact localization of FAR-4.**  After the merged signed reassembly, FAR-4
is equivalent to one off-diagonal cancellation inequality between the literal
q^2-descended packet and the fully cancelled boundary packet.  In particular,
there is no legitimate route through separate unsigned estimates of the two
packets: their cross energy is exactly the missing quantity. -/
theorem farFourCancelledCrossEnergy_iff_frozenTopFarFourEnergy :
    FarFourCancelledCrossEnergyStatement ↔
      FrozenTopFarFourEnergyStatement := by
  constructor
  · rintro ⟨CF, hCF, hcross⟩
    refine ⟨CF, hCF, ?_⟩
    intro R K hR hK
    have hc := hcross R K hR hK
    rw [lowWheelFrozenTopFarResidual_eq_farFourDescended_add_cancelled R hR]
    change
      ‖farFourDescendedPacket R + farFourCancelledBoundaryPacket R‖ ^ 2 ≤
        4 * farFourOddQ2DaughterEnergy R + CF * (R : ℝ) ^ 2 * K
    unfold farFourCancelledCrossEnergy at hc
    linarith
  · rintro ⟨CF, hCF, hfar⟩
    refine ⟨CF, hCF, ?_⟩
    intro R K hR hK
    have hf := hfar R K hR hK
    rw [lowWheelFrozenTopFarResidual_eq_farFourDescended_add_cancelled R hR] at hf
    change
      ‖farFourDescendedPacket R + farFourCancelledBoundaryPacket R‖ ^ 2 ≤
        4 * farFourOddQ2DaughterEnergy R + CF * (R : ℝ) ^ 2 * K at hf
    unfold farFourCancelledCrossEnergy
    linarith

end RHLean.Proof
