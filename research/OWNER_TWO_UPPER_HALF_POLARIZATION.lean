import Mathlib
import «research.GLOBAL_RETURNED_CORE_OWNER_TWO_CLIPPED_EXIT»
import «research.DYADIC_SMOOTH_HIGH_JOINT_PACKET»
import RHLean.Proof.VanishingTransitionRelevanceBase

/-!
# Owner-two upper-half smooth/transport polarization

The owner-two clipped exit is the complete odd dyadic annulus

    X_R / 2 < m <= X_R,  m odd,

and is exactly the top Mertens value.  This file keeps that signed annulus
assembled and rewrites its energy before any triangle inequality.

The exact square-prefix decomposition is

    M(X_R) = S_R - T_R,

where

* `S_R = squareRootSmoothMass (R-1)` is the complete R-smooth stopped state;
* `T_R = squareRootTransportCofactorFirst R` is the complete post-root
  high-prime transport.

Therefore the missing owner-two energy estimate is exactly a lower bound on
the smooth/high cross covariance.  Bounding `S_R` and `T_R` separately is
the wrong inequality: their positive energies are cancelled by the cross term.

No quantitative estimate is asserted here.  The point is to identify the
precise signed quantity that a successful owner-two attack must control.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- The complete owner-two odd dyadic annulus is exactly the stopped smooth
state minus the complete post-root transport. -/
theorem squareRootDyadicJointPacket_eq_smooth_sub_transport
    (R : ℕ) (hR : 1 ≤ R) :
    squareRootDyadicJointPacket R =
      squareRootSmoothMass (R - 1) -
        squareRootTransportCofactorFirst R := by
  rw [squareRootDyadicJointPacket_eq_squarePrefixMertens R hR,
    squarePrefixMertens_eq_squareRootSmooth_sub_transport,
    squareRootTransportMass_pred_eq_cofactorFirst R hR]

/-- Twice the real smooth/high covariance.  This is the cross term that is
lost if the smooth and post-root packets are normed separately. -/
def ownerTwoSmoothTransportCross (R : ℕ) : ℝ :=
  2 *
    (starRingEnd ℂ (squareRootSmoothMass (R - 1)) *
      squareRootTransportCofactorFirst R).re

/-- Exact polarization of the complete owner-two annulus. -/
theorem squareRootDyadicJointPacket_normSq_eq_smooth_transport_polarization
    (R : ℕ) (hR : 1 ≤ R) :
    Complex.normSq (squareRootDyadicJointPacket R) =
      Complex.normSq (squareRootSmoothMass (R - 1)) +
        Complex.normSq (squareRootTransportCofactorFirst R) -
          ownerTwoSmoothTransportCross R := by
  rw [squareRootDyadicJointPacket_eq_smooth_sub_transport R hR]
  unfold ownerTwoSmoothTransportCross
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- The repository's real square-endpoint Mertens energy is exactly the norm
square of the physical owner-two odd dyadic annulus. -/
theorem squareEndpointMertensEnergyReal_eq_ownerTwoJointPacket_normSq
    {R : ℕ} (hR : 2 ≤ R) :
    squareEndpointMertensEnergyReal R =
      Complex.normSq (squareRootDyadicJointPacket R) := by
  rw [squareRootDyadicJointPacket_eq_squarePrefixMertens R (by omega),
    Complex.normSq_eq_norm_sq]
  unfold RHLean.Analysis.squarePrefixMertens
  have hend :
      RHLean.Analysis.squarePrefixEndpoint (R - 1) =
        squareRootEndpoint R := by
    unfold RHLean.Analysis.squarePrefixEndpoint squareRootEndpoint
    rw [Nat.sub_add_cancel (by omega : 1 ≤ R)]
  rw [hend, ← mertensSummatoryInt_cast (squareRootEndpoint R),
    Complex.norm_intCast]
  exact (sq_abs (((mertensSummatoryInt (squareRootEndpoint R) : ℤ) : ℝ))).symm

/-- **Owner-two energy identity.**  The entire open square-endpoint energy is
the two positive smooth/transport energies minus their signed cross covariance.
This is the pre-norm form that must be preserved in any direct owner-two
attack. -/
theorem squareEndpointMertensEnergyReal_eq_smooth_transport_polarization
    {R : ℕ} (hR : 2 ≤ R) :
    squareEndpointMertensEnergyReal R =
      Complex.normSq (squareRootSmoothMass (R - 1)) +
        Complex.normSq (squareRootTransportCofactorFirst R) -
          ownerTwoSmoothTransportCross R := by
  rw [squareEndpointMertensEnergyReal_eq_ownerTwoJointPacket_normSq hR,
    squareRootDyadicJointPacket_normSq_eq_smooth_transport_polarization
      R (by omega)]

/-- A direct owner-two formulation of the missing recurrence: the signed
smooth/high cross covariance must absorb the two large positive packet energies
up to the already-allowed root-envelope and odd-q² daughter budgets. -/
def OwnerTwoSmoothTransportCovarianceStep (C : ℝ) : Prop :=
  ∀ R : ℕ, ∀ K : ℝ,
    2 ≤ R →
    LowerMertensCriticalEnvelope R K →
    Complex.normSq (squareRootSmoothMass (R - 1)) +
        Complex.normSq (squareRootTransportCofactorFirst R) -
        (C * (R : ℝ) ^ 2 * K +
          4 * ∑ q ∈ (primesUpTo (R - 1)).erase 2,
            squareEndpointMertensEnergyReal (roundedQ2ChildRoot R q)) ≤
      ownerTwoSmoothTransportCross R

/-- **Exact seam equivalence.**  The packaged q² recurrence is neither a bound
on the smooth packet nor on the high packet separately.  With the same
constant and quantifiers it is exactly the covariance lower bound above. -/
theorem squareEndpointRoundedOddQ2EnergyStep_iff_ownerTwoSmoothTransportCovariance
    (C : ℝ) :
    SquareEndpointRoundedOddQ2EnergyStep C ↔
      OwnerTwoSmoothTransportCovarianceStep C := by
  constructor
  · intro h R K hR hK
    have hs := h R K hR hK
    rw [squareEndpointMertensEnergyReal_eq_smooth_transport_polarization hR] at hs
    linarith
  · intro h R K hR hK
    have hs := h R K hR hK
    rw [squareEndpointMertensEnergyReal_eq_smooth_transport_polarization hR]
    linarith

end RHLean.Proof
