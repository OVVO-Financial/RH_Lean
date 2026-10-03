import Mathlib
import «research.VF_MID_PHYSICAL_FORCING_MOBIUS_DECODER»
import RHLean.Proof.ExceptionalTransportCoboundary
import RHLean.Proof.FinalCompensatedParentReduction
import RHLean.Proof.SquareRootLowPrimeGoWallStripTelescope

/-!
# Cubic phase law for the physical q^2 forcing frontier

PR #874 identified the centered actual-minus-Li forcing with the physical
Mobius field on the cubic depth-two carrier and proved that the first loss of
that carrier occurs exactly when the q^2 daughter reaches its owner:

  X / q^2 < q  <->  X < q^3.

The repository already contains both sides of the q^2 daughter dynamics:

* below the owner, the Go square residual is exactly the completed lower
  Mertens state M(X/q^2);
* once the daughter reaches the owner, the chronological high-prime column is
  an exact prime-insertion coboundary

      HighTransport = GoResidual - M(X/q^2).

This file composes those results into one named two-phase law.  No norm,
triangle inequality, density estimate, PNT error bound, RH hypothesis, sorry,
admit, or local axiom is introduced.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- **Inactive cubic phase.**
Before q^3 enters the endpoint, the q^2 daughter is already a completed
lower-scale Mertens state. -/
theorem vfMidQ2Daughter_eq_mertens_of_endpoint_lt_primeCube
    {X q : ℕ} (hq : q.Prime) (hX : X < q ^ 3) :
    squareRootLowPrimeGoWallSquareResidual q X =
      mertensSummatoryInt (X / (q * q)) := by
  have hcomplete :
      X / (q * q) < q :=
    (vfMidSquareDaughter_lt_owner_iff_endpoint_lt_primeCube hq).2 hX
  exact
    squareRootLowPrimeGoWallSquareResidual_eq_mertensSummatoryInt
      hq hcomplete

/-- **Inactive owners carry no high transport.**
The all-cutoff coboundary theorem plus completion below q^3 makes the
high-prime transport column identically zero, not merely small. -/
theorem vfMidQ2HighTransport_eq_zero_of_endpoint_lt_primeCube
    {X q : ℕ} (hq : q.Prime) (hX : X < q ^ 3) :
    q2DaughterHighTransport q X = 0 := by
  rw [q2DaughterHighTransport_eq_go_sub_mertens_all hq,
    vfMidQ2Daughter_eq_mertens_of_endpoint_lt_primeCube hq hX,
    sub_self]

/-- **Activated cubic phase.**
As soon as q^3 lies in the endpoint, the q^2 daughter has reached the owner.
The entire newly opened high-prime channel is exactly the pre-existing
prime-insertion coboundary. -/
theorem vfMidQ2HighTransport_eq_go_sub_mertens_of_primeCube_le
    {X q : ℕ} (hq : q.Prime) (hX : q ^ 3 ≤ X) :
    q2DaughterHighTransport q X =
      squareRootLowPrimeGoWallSquareResidual q X -
        mertensSummatoryInt (X / (q * q)) := by
  have hqle :
      q ≤ X / (q * q) :=
    (vfMidPrimeCube_le_iff_owner_le_squareDaughter hq).1 hX
  have hcut :
      q - 1 ≤ X / (q * q) := by
    omega
  exact q2DaughterHighTransport_eq_go_sub_mertens hcut

/-- Duhamel form of the activated phase: the recursive q^2 daughter is the
completed lower state plus one explicit chronological transport frontier. -/
theorem vfMidQ2Daughter_eq_mertens_add_highTransport_of_primeCube_le
    {X q : ℕ} (hq : q.Prime) (hX : q ^ 3 ≤ X) :
    squareRootLowPrimeGoWallSquareResidual q X =
      mertensSummatoryInt (X / (q * q)) +
        q2DaughterHighTransport q X := by
  have h :=
    vfMidQ2HighTransport_eq_go_sub_mertens_of_primeCube_le hq hX
  linear_combination h

/-- **Exact cubic phase dichotomy.**
There is no third local behavior at one prime coordinate:

* below q^3: the square daughter has already returned to lower Mertens;
* at/above q^3: the same lower Mertens state is retained and the only new term
  is the explicit prime-insertion high-transport coboundary.

This packages the empirical prime-cube frontier discovered in #874 as a
kernel-checkable state-transition law. -/
theorem vfMidQ2Daughter_cubicPhaseDichotomy
    {X q : ℕ} (hq : q.Prime) :
    (X < q ^ 3 ∧
      squareRootLowPrimeGoWallSquareResidual q X =
        mertensSummatoryInt (X / (q * q))) ∨
    (q ^ 3 ≤ X ∧
      squareRootLowPrimeGoWallSquareResidual q X =
        mertensSummatoryInt (X / (q * q)) +
          q2DaughterHighTransport q X) := by
  by_cases hX : X < q ^ 3
  · left
    exact ⟨hX, vfMidQ2Daughter_eq_mertens_of_endpoint_lt_primeCube hq hX⟩
  · right
    have hcube : q ^ 3 ≤ X := by omega
    exact
      ⟨hcube,
        vfMidQ2Daughter_eq_mertens_add_highTransport_of_primeCube_le
          hq hcube⟩

/-- The full square-endpoint high-transport column may be restricted
pointwise to the cubic-active owner gate.  Owners with q^3 above the endpoint
contribute exactly zero. -/
theorem squareEndpointQ2HighTransportColumn_eq_cubicActive
    (R : ℕ) :
    squareEndpointQ2HighTransportColumn R =
      ∑ q ∈ primesUpTo (R - 1),
        if q ^ 3 ≤ squareRootEndpoint R then
          q2DaughterHighTransport q (squareRootEndpoint R)
        else 0 := by
  unfold squareEndpointQ2HighTransportColumn
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hactive : q ^ 3 ≤ squareRootEndpoint R
  · simp [hactive]
  · have hqPrime : q.Prime := (mem_primesUpTo.mp hq).1
    have hinactive : squareRootEndpoint R < q ^ 3 := by omega
    have hz :=
      vfMidQ2HighTransport_eq_zero_of_endpoint_lt_primeCube
        hqPrime hinactive
    simp [hactive, hz]

/-- Critical-coordinate image of the activated coboundary.  The physical
frontier is transported with exactly the already-solved critical multiplier
q^(-1/2); no new multiplier is introduced by the actual-prime system. -/
theorem vfMidCriticalQ2HighTransport_eq_weightedCoboundary_of_primeCube_le
    {X q : ℕ} (hq : q.Prime) (hX : q ^ 3 ≤ X) :
    criticalSqrtWeight q *
        (((q2DaughterHighTransport q X : ℤ) : ℂ)) =
      criticalSqrtWeight q *
        ((((squareRootLowPrimeGoWallSquareResidual q X : ℤ) : ℂ) -
          ((mertensSummatoryInt (X / (q * q)) : ℤ) : ℂ))) := by
  rw [vfMidQ2HighTransport_eq_go_sub_mertens_of_primeCube_le hq hX]
  push_cast

/-- Reciprocal-coordinate image of the activated coboundary.  The same
physical frontier enters with the exact q^(-1) multiplier used by the solved
reciprocal/Abel coordinate. -/
theorem vfMidReciprocalQ2HighTransport_eq_weightedCoboundary_of_primeCube_le
    {X q : ℕ} (hq : q.Prime) (hX : q ^ 3 ≤ X) :
    reciprocalWeight q *
        (((q2DaughterHighTransport q X : ℤ) : ℂ)) =
      reciprocalWeight q *
        ((((squareRootLowPrimeGoWallSquareResidual q X : ℤ) : ℂ) -
          ((mertensSummatoryInt (X / (q * q)) : ℤ) : ℂ))) := by
  rw [vfMidQ2HighTransport_eq_go_sub_mertens_of_primeCube_le hq hX]
  push_cast

end RHLean.Analysis
