import RHLean.Proof.DyadicSurvivorMertensInvariant
import RHLean.Proof.MatchedFarSurvivorBridge

/-!
# Dyadic survivor splice into the matched square-root channel

The x=210 autopsy and its formal survivor invariant identify the complete
post-root transport with the negative physical dyadic survivor mass.

This file removes the abstract transport symbol from the matched
born-smooth/transport channel.  Every statement here is an exact rewrite:
no norm, triangle inequality, or new estimate is introduced.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

/-- **Physical form of the matched channel.**

The matched born-smooth/transport object is literally born-smooth plus the
signed physical dyadic survivor population. -/
theorem squareRootMatchedBornSmoothTransport_eq_bornSmooth_add_dyadicSurvivor
    (R : ℕ) (hR : 0 < R) :
    squareRootMatchedBornSmoothTransport R =
      squareRootBornSmoothMass R + squareRootDyadicSurvivorMass R := by
  unfold squareRootMatchedBornSmoothTransport
  rw [squareRootDyadicSurvivorMass_eq_neg_transport R hR]
  ring

/-- Above the production threshold, the whole physical dyadic survivor
population is exactly the far-upper survivor minus the seven-coordinate
near-prime strip. -/
theorem squareRootDyadicSurvivorMass_eq_farSurvivor_sub_near
    (R : ℕ) (hR : 56 ≤ R) :
    squareRootDyadicSurvivorMass R =
      survivorSixteenFarUpperPrimeMass (R - 1) -
        squareRootNearPrimeTransport R := by
  rw [squareRootDyadicSurvivorMass_eq_neg_transport R (by omega),
    squareRootTransportPrimeFirst_eq_near_sub_farSurvivor R hR]
  ring

/-- The matched channel in completely physical survivor coordinates. -/
theorem squareRootMatchedBornSmoothTransport_eq_bornSmooth_add_farDyadicSurvivor_sub_near
    (R : ℕ) (hR : 56 ≤ R) :
    squareRootMatchedBornSmoothTransport R =
      squareRootBornSmoothMass R +
        survivorSixteenFarUpperPrimeMass (R - 1) -
          squareRootNearPrimeTransport R := by
  rw [squareRootMatchedBornSmoothTransport_eq_bornSmooth_add_dyadicSurvivor
      R (by omega),
    squareRootDyadicSurvivorMass_eq_farSurvivor_sub_near R hR]

/-- RH-scale boundedness statement written only in physical born-smooth and
dyadic-survivor coordinates. -/
def SquareRootBornDyadicSurvivorBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ R : ℕ, 2 ≤ R →
        ‖squareRootBornSmoothMass R + squareRootDyadicSurvivorMass R‖ ^ 2 ≤
          C * Real.rpow (R : ℝ) (2 + ε)

/-- The physical survivor statement is exactly equivalent to the existing
matched-transport statement.  Thus replacing transport by its survivor
autopsy loses no cancellation and changes no analytic strength. -/
theorem squareRootBornDyadicSurvivorBoundedStatement_iff_matchedTransport
    :
    SquareRootBornDyadicSurvivorBoundedStatement ↔
      SquareRootMatchedTransportBoundedStatement := by
  constructor
  · intro h ε hε
    rcases h ε hε with ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro R hR
    rw [squareRootMatchedBornSmoothTransport_eq_bornSmooth_add_dyadicSurvivor
      R (by omega)]
    exact hbound R hR
  · intro h ε hε
    rcases h ε hε with ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro R hR
    rw [← squareRootMatchedBornSmoothTransport_eq_bornSmooth_add_dyadicSurvivor
      R (by omega)]
    exact hbound R hR

/-- The only difference between the physical matched channel and the
born-smooth plus far-survivor core is the already-bounded seven-coordinate
near-prime strip. -/
theorem norm_bornSmooth_add_dyadicSurvivor_sub_bornSmooth_add_farSurvivor_le
    (R : ℕ) (hR : 56 ≤ R) :
    ‖(squareRootBornSmoothMass R + squareRootDyadicSurvivorMass R) -
        (squareRootBornSmoothMass R +
          survivorSixteenFarUpperPrimeMass (R - 1))‖ ≤
      7 * (R : ℝ) := by
  rw [squareRootDyadicSurvivorMass_eq_farSurvivor_sub_near R hR]
  have hnear := norm_squareRootNearPrimeTransport_le R hR
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hnear

end RHLean.Proof
