import Mathlib
import «research.VF_MID_VON_KOCH_BRIDGE»

/-!
# Direct signed dynamics of the VF-mid square-band error

This file attacks the remaining VF-mid arithmetic discrepancy directly.
There is no sieve, Mertens transform, Li allocation model, or composite
recurrence here.

For one square band, write

  epsilon_R = P_R - V_R,

where P_R is the exact prime population and V_R is the VF midpoint mass.
The prime population is then logarithmically reweighted by the band Chebyshev
mass.  This separates epsilon_R into

  (Theta_R - (2R+1)) / log(m_R)

plus a prime-location correction measuring only where the primes sit inside
the already-fixed square band.

The purpose is to prove that the location correction is lower order, so the
only RH-scale cancellation left is the signed cumulative Chebyshev band mass.
-/

noncomputable section

open scoped BigOperators Nat.Prime

namespace RHLean.Analysis

/-- Primes that enter the prime-counting staircase between consecutive square
endpoints.  Defining the band as a finset difference keeps this file completely
independent of the composite/sieve bridge. -/
def vfMidDirectPrimeBand (R : ℕ) : Finset ℕ :=
  Nat.primesLE ((R + 1) ^ 2) \ Nat.primesLE (R ^ 2)

/-- Real cardinality of the direct prime band. -/
def vfMidDirectPrimeBandCount (R : ℕ) : ℝ :=
  ((vfMidDirectPrimeBand R).card : ℝ)

/-- Logarithmically weighted prime mass in one square band. -/
def vfMidDirectThetaBandMass (R : ℕ) : ℝ :=
  ∑ p ∈ vfMidDirectPrimeBand R, Real.log p

/-- Signed prime-count error in one complete VF-mid square band. -/
def vfMidDirectBandError (R : ℕ) : ℝ :=
  vfMidDirectPrimeBandCount R - vfMidBandMass R

/-- Centered logarithmic prime mass of one complete square band. -/
def vfMidDirectThetaBandError (R : ℕ) : ℝ :=
  vfMidDirectThetaBandMass R - (2 * (R : ℝ) + 1)

/-- Difference between raw prime population and the same population after
reweighting every prime by log(p)/log(midpoint).  This depends only on where
the primes lie inside the fixed band. -/
def vfMidDirectLogPositionError (R : ℕ) : ℝ :=
  vfMidDirectPrimeBandCount R -
    vfMidDirectThetaBandMass R / Real.log (vfMidBandMidpoint R)

/-- Prime-band cardinality is exactly the increment of the prime-counting
staircase across the two square endpoints. -/
theorem vfMidDirectPrimeBandCount_eq_primeCounting_sub (R : ℕ) :
    vfMidDirectPrimeBandCount R =
      (Nat.primeCounting ((R + 1) ^ 2) : ℝ) -
        (Nat.primeCounting (R ^ 2) : ℝ) := by
  classical
  have hsq : R ^ 2 ≤ (R + 1) ^ 2 := by nlinarith
  have hsub :
      Nat.primesLE (R ^ 2) ⊆ Nat.primesLE ((R + 1) ^ 2) :=
    Nat.primesLE_mono hsq
  unfold vfMidDirectPrimeBandCount vfMidDirectPrimeBand
  rw [Finset.cast_card_sdiff (R := ℝ) hsub]
  simp

/-- The direct band log-mass is exactly the increment of Chebyshev theta. -/
theorem vfMidDirectThetaBandMass_eq_theta_sub (R : ℕ) :
    vfMidDirectThetaBandMass R =
      Chebyshev.theta ((R + 1) ^ 2) - Chebyshev.theta (R ^ 2) := by
  classical
  have hsq : R ^ 2 ≤ (R + 1) ^ 2 := by nlinarith
  have hsub :
      Nat.primesLE (R ^ 2) ⊆ Nat.primesLE ((R + 1) ^ 2) :=
    Nat.primesLE_mono hsq
  unfold vfMidDirectThetaBandMass vfMidDirectPrimeBand
  rw [Chebyshev.theta_eq_sum_primesLE_log,
    Chebyshev.theta_eq_sum_primesLE_log]
  rw [← Finset.sum_sdiff hsub]

/-- **Exact direct split of the band error.**

The first term is the centered logarithmic prime mass.  The second term is
only the within-band log-position correction.  No estimate is used here. -/
theorem vfMidDirectBandError_eq_theta_add_position (R : ℕ) :
    vfMidDirectBandError R =
      vfMidDirectThetaBandError R / Real.log (vfMidBandMidpoint R) +
        vfMidDirectLogPositionError R := by
  unfold vfMidDirectBandError vfMidDirectThetaBandError
    vfMidDirectLogPositionError vfMidBandMass
  ring

/-- Square-endpoint Chebyshev error. -/
def vfMidDirectThetaEndpointError (R : ℕ) : ℝ :=
  Chebyshev.theta (R ^ 2) - (R : ℝ) ^ 2

/-- The centered band log-mass is the exact first difference of the
square-endpoint Chebyshev error. -/
theorem vfMidDirectThetaBandError_eq_endpoint_diff (R : ℕ) :
    vfMidDirectThetaBandError R =
      vfMidDirectThetaEndpointError (R + 1) -
        vfMidDirectThetaEndpointError R := by
  rw [vfMidDirectThetaBandError, vfMidDirectThetaBandMass_eq_theta_sub]
  unfold vfMidDirectThetaEndpointError
  push_cast
  ring

end RHLean.Analysis
