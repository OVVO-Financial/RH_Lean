import Mathlib
import «research.VF_MID_VON_KOCH_BRIDGE»
import RHLean.Analysis.NativePNTChebyshev

/-!
# Direct signed dynamics of the VF-mid square-band error

This file attacks the remaining VF-mid arithmetic discrepancy directly.
There is no sieve, Mertens transform, Li allocation model, or composite
recurrence here.

For one square band, write

  epsilon_R = P_R - V_R,

where P_R is the exact prime population and V_R is the VF midpoint mass.
The same exact primes are logarithmically reweighted. This separates epsilon_R
into

  (Theta_R - (2R+1)) / log(m_R)

plus a prime-location correction measuring only where the primes sit inside
the already-fixed square band.

The purpose is to remove within-band placement as a possible RH-scale
obstruction and leave only signed cumulative prime log-mass.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

/-- Primes entering the prime-counting staircase between consecutive square
endpoints. -/
def vfMidDirectPrimeBand (R : ℕ) : Finset ℕ :=
  (Finset.Ioc (R ^ 2) ((R + 1) ^ 2)).filter Nat.Prime

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
reweighting every prime by log(p)/log(midpoint). This depends only on where
the primes lie inside the fixed square band. -/
def vfMidDirectLogPositionError (R : ℕ) : ℝ :=
  vfMidDirectPrimeBandCount R -
    vfMidDirectThetaBandMass R / Real.log (vfMidBandMidpoint R)

/-- The repository's exact finite prime set has cardinality pi(N).  This is a
local copy of the elementary cardinality argument, kept here so the direct
attack does not import any PNT transfer theorem. -/
private theorem vfMidDirect_nativePrimeSet_card_eq_primeCounting (N : ℕ) :
    (nativePrimeSet N).card = Nat.primeCounting N := by
  have hset :
      nativePrimeSet N = (Finset.range (N + 1)).filter Nat.Prime := by
    unfold nativePrimeSet
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range,
      Nat.lt_succ_iff]
    constructor
    · rintro ⟨⟨_hp1, hpN⟩, hpPrime⟩
      exact ⟨hpN, hpPrime⟩
    · rintro ⟨hpN, hpPrime⟩
      exact ⟨⟨hpPrime.one_le, hpN⟩, hpPrime⟩
  unfold Nat.primeCounting Nat.primeCounting'
  rw [Nat.count_eq_card_filter_range]
  exact congrArg Finset.card hset

/-- Exact partition of the prime coordinates at the upper square endpoint into
the already-seen primes and the newly entered square band. -/
theorem vfMidDirect_nativePrimeSet_split (R : ℕ) :
    nativePrimeSet ((R + 1) ^ 2) =
      nativePrimeSet (R ^ 2) ∪ vfMidDirectPrimeBand R := by
  have hsq : R ^ 2 ≤ (R + 1) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  unfold nativePrimeSet vfMidDirectPrimeBand
  ext p
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc,
    Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hp1, hpU⟩, hpPrime⟩
    by_cases hpL : p ≤ R ^ 2
    · exact Or.inl ⟨⟨hp1, hpL⟩, hpPrime⟩
    · exact Or.inr ⟨⟨lt_of_not_ge hpL, hpU⟩, hpPrime⟩
  · rintro (h | h)
    · exact ⟨⟨h.1.1, h.1.2.trans hsq⟩, h.2⟩
    · exact ⟨⟨by omega, h.1.2⟩, h.2⟩

/-- The old-prime block and the new square-band block are disjoint. -/
theorem vfMidDirect_nativePrimeSet_disjoint_band (R : ℕ) :
    Disjoint (nativePrimeSet (R ^ 2)) (vfMidDirectPrimeBand R) := by
  rw [Finset.disjoint_left]
  intro p hpOld hpBand
  rcases Finset.mem_filter.mp hpOld with ⟨hpOldIcc, _⟩
  rcases Finset.mem_filter.mp hpBand with ⟨hpBandIoc, _⟩
  rcases Finset.mem_Icc.mp hpOldIcc with ⟨_, hpL⟩
  rcases Finset.mem_Ioc.mp hpBandIoc with ⟨hpGt, _⟩
  omega

/-- Prime-band cardinality is exactly the increment of the prime-counting
staircase across the two square endpoints. -/
theorem vfMidDirectPrimeBand_card_add_primeCounting_eq (R : ℕ) :
    (vfMidDirectPrimeBand R).card + Nat.primeCounting (R ^ 2) =
      Nat.primeCounting ((R + 1) ^ 2) := by
  have hcard := congrArg Finset.card (vfMidDirect_nativePrimeSet_split R)
  rw [Finset.card_union_of_disjoint
    (vfMidDirect_nativePrimeSet_disjoint_band R)] at hcard
  rw [vfMidDirect_nativePrimeSet_card_eq_primeCounting,
    vfMidDirect_nativePrimeSet_card_eq_primeCounting] at hcard
  omega

/-- Real-valued version of the exact prime-count increment. -/
theorem vfMidDirectPrimeBandCount_eq_primeCounting_sub (R : ℕ) :
    vfMidDirectPrimeBandCount R =
      (Nat.primeCounting ((R + 1) ^ 2) : ℝ) -
        (Nat.primeCounting (R ^ 2) : ℝ) := by
  have h := vfMidDirectPrimeBand_card_add_primeCounting_eq R
  have hR :
      ((vfMidDirectPrimeBand R).card : ℝ) +
          (Nat.primeCounting (R ^ 2) : ℝ) =
        (Nat.primeCounting ((R + 1) ^ 2) : ℝ) := by
    exact_mod_cast h
  unfold vfMidDirectPrimeBandCount
  linarith

/-- The same finite partition gives an exact additive identity for the
log-weighted prime mass. -/
theorem vfMidDirectThetaBandMass_add_nativeTheta_eq (R : ℕ) :
    vfMidDirectThetaBandMass R + nativeTheta (R ^ 2) =
      nativeTheta ((R + 1) ^ 2) := by
  have hsplit := vfMidDirect_nativePrimeSet_split R
  have hdisj := vfMidDirect_nativePrimeSet_disjoint_band R
  unfold nativeTheta vfMidDirectThetaBandMass
  rw [hsplit, Finset.sum_union hdisj]
  ring

/-- The direct band log-mass is the increment of the exact finite theta mass. -/
theorem vfMidDirectThetaBandMass_eq_theta_sub (R : ℕ) :
    vfMidDirectThetaBandMass R =
      nativeTheta ((R + 1) ^ 2) - nativeTheta (R ^ 2) := by
  linarith [vfMidDirectThetaBandMass_add_nativeTheta_eq R]

/-- **Exact direct split of the band error.**

The first term is the centered logarithmic prime mass. The second term is only
the within-band log-position correction. No estimate is used here. -/
theorem vfMidDirectBandError_eq_theta_add_position (R : ℕ) :
    vfMidDirectBandError R =
      vfMidDirectThetaBandError R / Real.log (vfMidBandMidpoint R) +
        vfMidDirectLogPositionError R := by
  unfold vfMidDirectBandError vfMidDirectThetaBandError
    vfMidDirectLogPositionError vfMidBandMass
  ring

/-- Square-endpoint exact theta discrepancy. -/
def vfMidDirectThetaEndpointError (R : ℕ) : ℝ :=
  nativeTheta (R ^ 2) - (R : ℝ) ^ 2

/-- The centered band log-mass is the exact first difference of the
square-endpoint theta error. -/
theorem vfMidDirectThetaBandError_eq_endpoint_diff (R : ℕ) :
    vfMidDirectThetaBandError R =
      vfMidDirectThetaEndpointError (R + 1) -
        vfMidDirectThetaEndpointError R := by
  rw [vfMidDirectThetaBandError, vfMidDirectThetaBandMass_eq_theta_sub]
  unfold vfMidDirectThetaEndpointError
  push_cast
  ring

end RHLean.Analysis
