import Mathlib
import «research.VF_MID_VON_KOCH_BRIDGE»
import RHLean.Proof.LowWheelHighPrimeSurvivor
import RHLean.Analysis.SquareRootPrimeCountGap

/-!
# VF-mid square-band composite complement

This file rewrites the exact prime population in one complete square band as
the complement of the composite population, and then identifies the same prime
population with survival under the completed low-prime wheel.

There is no PNT, equidistribution, or asymptotic input here.  The point is to
put the arithmetic increment of the VF-mid discrepancy directly on the finite
composite sieve.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Proof

/-- Interior integer sites in the square band `(R^2,(R+1)^2)`.
The upper square is deliberately excluded; for `R >= 2` both endpoints are
composite, so this contains every prime contributing between the two square
endpoints. -/
def vfMidSquareBandSites (R : ℕ) : Finset ℕ :=
  Finset.Ioo (R ^ 2) ((R + 1) ^ 2)

/-- Prime sites in the complete square band. -/
def vfMidSquareBandPrimes (R : ℕ) : Finset ℕ :=
  (vfMidSquareBandSites R).filter Nat.Prime

/-- Composite sites in the complete square band.  On this band every site is
greater than one once `R >= 2`, so `¬ n.Prime` is literally compositeness. -/
def vfMidSquareBandComposites (R : ℕ) : Finset ℕ :=
  (vfMidSquareBandSites R).filter fun n => ¬ n.Prime

/-- A complete square band has exactly `2R` interior integer sites. -/
theorem vfMidSquareBandSites_card (R : ℕ) :
    (vfMidSquareBandSites R).card = 2 * R := by
  unfold vfMidSquareBandSites
  rw [Nat.card_Ioo]
  omega

/-- Prime and composite sites partition the complete square band exactly. -/
theorem vfMidSquareBand_prime_composite_partition (R : ℕ) :
    vfMidSquareBandPrimes R ∪ vfMidSquareBandComposites R =
      vfMidSquareBandSites R := by
  classical
  ext n
  simp only [vfMidSquareBandPrimes, vfMidSquareBandComposites,
    Finset.mem_union, Finset.mem_filter]
  constructor
  · intro hn
    by_cases hp : n.Prime
    · exact Or.inl ⟨hn, hp⟩
    · exact Or.inr ⟨hn, hp⟩
  · rintro (h | h)
    · exact h.1
    · exact h.1

/-- The prime and composite populations in one complete square band are
disjoint. -/
theorem vfMidSquareBand_prime_composite_disjoint (R : ℕ) :
    Disjoint (vfMidSquareBandPrimes R) (vfMidSquareBandComposites R) := by
  classical
  rw [Finset.disjoint_left]
  intro n hp hc
  exact (Finset.mem_filter.mp hc).2 (Finset.mem_filter.mp hp).2

/-- **Exact composite complement.**  In the square band the prime count plus
the composite count is the deterministic band length `2R`. -/
theorem vfMidSquareBand_prime_card_add_composite_card (R : ℕ) :
    (vfMidSquareBandPrimes R).card +
        (vfMidSquareBandComposites R).card = 2 * R := by
  have hcard := congrArg Finset.card (vfMidSquareBand_prime_composite_partition R)
  rw [Finset.card_union_of_disjoint
    (vfMidSquareBand_prime_composite_disjoint R)] at hcard
  simpa [vfMidSquareBandSites_card] using hcard

/-- Prime-count increment across consecutive square endpoints is exactly the
prime population of the intervening square band. -/
theorem vfMidSquareBand_prime_card_add_primeCounting_sq (R : ℕ) :
    (vfMidSquareBandPrimes R).card + Nat.primeCounting (R ^ 2) =
      Nat.primeCounting ((R + 1) ^ 2) := by
  have h :=
    RHLean.Proof.primeCard_Ioc_add_primeCounting_eq
      (a := R ^ 2) (b := (R + 1) ^ 2) (by nlinarith : R ^ 2 ≤ (R + 1) ^ 2)
  have hset :
      ((Finset.Ioc (R ^ 2) ((R + 1) ^ 2)).filter Nat.Prime) =
        vfMidSquareBandPrimes R := by
    classical
    ext n
    simp only [vfMidSquareBandPrimes, vfMidSquareBandSites,
      Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Ioo]
    constructor
    · rintro ⟨⟨hlow, hhigh⟩, hp⟩
      have hne : n ≠ (R + 1) ^ 2 := by
        intro hn
        subst n
        have hcomp : ¬ ((R + 1) ^ 2).Prime := by
          intro hsqPrime
          have hexp := hsqPrime.eq_one_of_pow
          omega
        exact hcomp hp
      exact ⟨⟨hlow, lt_of_le_of_ne hhigh hne⟩, hp⟩
    · rintro ⟨⟨hlow, hhigh⟩, hp⟩
      exact ⟨⟨hlow, hhigh.le⟩, hp⟩
  rw [hset] at h
  exact h

/-- The completed low wheel through `R` detects every composite in the next
square band: surviving all prime divisibility coordinates at most `R` is
equivalent to primality. -/
theorem vfMidSquareBand_lowWheelSurvivor_iff_prime
    {R n : ℕ} (hR : 2 ≤ R)
    (hn : n ∈ vfMidSquareBandSites R) :
    lowWheelHighSurvivor (R + 1) n ↔ n.Prime := by
  have hnI := Finset.mem_Ioo.mp hn
  have hlow : R + 1 < n := by
    have hsq : R + 1 ≤ R ^ 2 := by nlinarith
    omega
  have hhigh : n ≤ squareRootEndpoint (R + 1) := by
    unfold squareRootEndpoint
    omega
  exact lowWheelHighSurvivor_iff_prime (R := R + 1) (q := n)
    (by omega) hlow hhigh

/-- Survivor set for the completed low wheel used by the legacy
square-band bridge. -/
def vfMidSquareBandLowWheelSurvivors (R : ℕ) : Finset ℕ := by
  classical
  exact (vfMidSquareBandSites R).filter (lowWheelHighSurvivor (R + 1))

/-- The prime population of a square band is exactly the survivor population
of the completed low wheel.  This is the finite sieve form of the
prime/composite complement. -/
theorem vfMidSquareBandPrimes_eq_lowWheelSurvivors
    (R : ℕ) (hR : 2 ≤ R) :
    vfMidSquareBandPrimes R = vfMidSquareBandLowWheelSurvivors R := by
  classical
  ext n
  simp only [vfMidSquareBandPrimes, vfMidSquareBandLowWheelSurvivors,
    Finset.mem_filter]
  constructor
  · rintro ⟨hn, hp⟩
    exact ⟨hn, (vfMidSquareBand_lowWheelSurvivor_iff_prime hR hn).2 hp⟩
  · rintro ⟨hn, hs⟩
    exact ⟨hn, (vfMidSquareBand_lowWheelSurvivor_iff_prime hR hn).1 hs⟩

/-- Signed arithmetic increment of the VF-mid prime discrepancy across one
complete square band. -/
def vfMidSquareBandError (R : ℕ) : ℝ :=
  ((vfMidSquareBandPrimes R).card : ℝ) - vfMidBandMass R

/-- The same band error written entirely as deterministic band length minus
the composite population minus the VF midpoint mass. -/
theorem vfMidSquareBandError_eq_compositeComplement (R : ℕ) :
    vfMidSquareBandError R =
      (2 * (R : ℝ) - ((vfMidSquareBandComposites R).card : ℝ)) -
        vfMidBandMass R := by
  have hcard := vfMidSquareBand_prime_card_add_composite_card R
  have hcardR :
      ((vfMidSquareBandPrimes R).card : ℝ) +
          ((vfMidSquareBandComposites R).card : ℝ) = 2 * (R : ℝ) := by
    exact_mod_cast hcard
  unfold vfMidSquareBandError
  linarith

/-- Square-endpoint VF-mid discrepancy. -/
def vfMidSquareEndpointError (R : ℕ) : ℝ :=
  (Nat.primeCounting (R ^ 2) : ℝ) - vfMidFinishedMass R

/-- **Exact square-band recurrence.**  Advancing one square adds precisely the
band prime excess over the VF midpoint mass. -/
theorem vfMidSquareEndpointError_succ
    (R : ℕ) (hR : 2 ≤ R) :
    vfMidSquareEndpointError (R + 1) =
      vfMidSquareEndpointError R + vfMidSquareBandError R := by
  have hp := vfMidSquareBand_prime_card_add_primeCounting_sq R
  have hpR :
      ((vfMidSquareBandPrimes R).card : ℝ) +
          (Nat.primeCounting (R ^ 2) : ℝ) =
        (Nat.primeCounting ((R + 1) ^ 2) : ℝ) := by
    exact_mod_cast hp
  unfold vfMidSquareEndpointError vfMidSquareBandError
  rw [vfMidFinishedMass_succ hR]
  linarith

/-- The recurrence can be written with no prime indicator at all: the next
VF-mid discrepancy is driven by the centered composite population. -/
theorem vfMidSquareEndpointError_succ_eq_composite
    (R : ℕ) (hR : 2 ≤ R) :
    vfMidSquareEndpointError (R + 1) =
      vfMidSquareEndpointError R +
        ((2 * (R : ℝ) - ((vfMidSquareBandComposites R).card : ℝ)) -
          vfMidBandMass R) := by
  rw [vfMidSquareEndpointError_succ R hR,
    vfMidSquareBandError_eq_compositeComplement]

/-- Exact quadratic-energy update for the square-endpoint discrepancy.  This
is the natural interface for a future signed self-correction estimate. -/
theorem vfMidSquareEndpointError_sq_succ
    (R : ℕ) (hR : 2 ≤ R) :
    vfMidSquareEndpointError (R + 1) ^ 2 -
        vfMidSquareEndpointError R ^ 2 =
      2 * vfMidSquareEndpointError R * vfMidSquareBandError R +
        vfMidSquareBandError R ^ 2 := by
  rw [vfMidSquareEndpointError_succ R hR]
  ring

end RHLean.Analysis
