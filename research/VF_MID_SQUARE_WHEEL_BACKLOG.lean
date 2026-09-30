import Mathlib
import «research.VF_MID_INTEGER_BLOCK_CAPTURE»
import «research.VF_MID_SQUARE_BAND_COMPOSITE_BRIDGE»
import RHLean.Arithmetic.PrimesUpToFrontier

/-!
# VF-mid square-wheel backlog dynamics

This file formalizes the elementary finite mechanism behind the square blocks.

For an interior integer n in the square block

  R^2 < n < (R+1)^2,

every composite n has a prime divisor at most R.  Therefore primality on the
whole block is exactly survival under the same finite divisibility wheel
consisting of all primes at most R.

The integer VF-mid level is

  K_R = floor(vfMidFinishedMass R).

We introduce three finite quantities:

  B_R = K_R - pi(R^2)                    (signed backlog),
  Q_R = K_(R+1) - K_R                    (integer VF demand),
  P_R = number of common-wheel survivors (exact prime supply).

They satisfy the exact conservation law

  B_(R+1) = B_R + Q_R - P_R.

Moreover, capture of K_R by its own square block is exactly

  0 <= B_R <= P_R,

and the integer demand differs from the real midpoint band mass by less than
one count:

  |Q_R - vfMidBandMass R| < 1.

No prime-number theorem rate or probabilistic independence assumption appears.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

/-! ## The common finite sieve on one square block -/

/-- On the interior of one square block, primality is exactly survival under
one and the same low-prime wheel through R.  This is the square-root factor
criterion in finite form. -/
theorem vfMidSquareBand_commonWheelSurvivor_iff_prime
    {R n : ℕ} (hR : 2 ≤ R)
    (hn : n ∈ vfMidSquareBandSites R) :
    lowWheelHighSurvivor R n ↔ n.Prime := by
  have hnI := Finset.mem_Ioo.mp hn
  have hRltSq : R < R ^ 2 := by
    nlinarith
  have hRn : R < n := hRltSq.trans hnI.1
  have hnX : n ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    omega
  exact lowWheelHighSurvivor_iff_prime hR hRn hnX

/-- Every composite interior site is eliminated by at least one prime
coordinate belonging to the common wheel through R. -/
theorem vfMidSquareBand_composite_has_commonWheel_divisor
    {R n : ℕ} (hR : 2 ≤ R)
    (hn : n ∈ vfMidSquareBandSites R)
    (hcomp : ¬ n.Prime) :
    ∃ p ∈ primesUpTo R, p ∣ n := by
  by_contra hnone
  have hsurv : lowWheelHighSurvivor R n := by
    intro p hp hpd
    apply hnone
    exact ⟨p, hp, hpd⟩
  exact hcomp
    ((vfMidSquareBand_commonWheelSurvivor_iff_prime hR hn).1 hsurv)

/-- The exact common-wheel survivor population in square block R. -/
def vfMidSquareBandCommonWheelSurvivors (R : ℕ) : Finset ℕ :=
  (vfMidSquareBandSites R).filter (lowWheelHighSurvivor R)

/-- On a complete square block, the common-wheel survivors are literally the
prime sites. -/
theorem vfMidSquareBandCommonWheelSurvivors_eq_primes
    (R : ℕ) (hR : 2 ≤ R) :
    vfMidSquareBandCommonWheelSurvivors R = vfMidSquareBandPrimes R := by
  classical
  ext n
  simp only [vfMidSquareBandCommonWheelSurvivors, vfMidSquareBandPrimes,
    Finset.mem_filter]
  constructor
  · rintro ⟨hn, hsurv⟩
    exact ⟨hn, (vfMidSquareBand_commonWheelSurvivor_iff_prime hR hn).1 hsurv⟩
  · rintro ⟨hn, hp⟩
    exact ⟨hn, (vfMidSquareBand_commonWheelSurvivor_iff_prime hR hn).2 hp⟩

/-! ## Exact prime supply -/

/-- Exact prime supply of one square block, expressed as common-wheel
survivor cardinality. -/
def vfMidIntegerBlockPrimeSupply (R : ℕ) : ℕ :=
  (vfMidSquareBandCommonWheelSurvivors R).card

/-- The common-wheel supply is the literal prime population of the block. -/
theorem vfMidIntegerBlockPrimeSupply_eq_primeCard
    (R : ℕ) (hR : 2 ≤ R) :
    vfMidIntegerBlockPrimeSupply R = (vfMidSquareBandPrimes R).card := by
  unfold vfMidIntegerBlockPrimeSupply
  rw [vfMidSquareBandCommonWheelSurvivors_eq_primes R hR]

/-- Supply plus the old endpoint count is exactly the next endpoint count. -/
theorem vfMidIntegerBlockPrimeSupply_add_primeCounting
    (R : ℕ) (hR : 2 ≤ R) :
    vfMidIntegerBlockPrimeSupply R + Nat.primeCounting (R ^ 2) =
      Nat.primeCounting ((R + 1) ^ 2) := by
  rw [vfMidIntegerBlockPrimeSupply_eq_primeCard R hR]
  exact vfMidSquareBand_prime_card_add_primeCounting_sq R

/-- The exact supply is at most the 2R interior sites. -/
theorem vfMidIntegerBlockPrimeSupply_le_two_mul
    (R : ℕ) (hR : 2 ≤ R) :
    vfMidIntegerBlockPrimeSupply R ≤ 2 * R := by
  rw [vfMidIntegerBlockPrimeSupply_eq_primeCard R hR]
  have hpart := vfMidSquareBand_prime_card_add_composite_card R
  omega

/-! ## Integer backlog and demand -/

/-- Signed number of integer VF-mid counts still above the prime staircase at
the left endpoint R^2.  Negative values mean the staircase has already passed
the integer VF-mid level. -/
def vfMidIntegerBlockBacklog (R : ℕ) : ℤ :=
  (vfMidIntegerBlockLevel R : ℤ) - (Nat.primeCounting (R ^ 2) : ℤ)

/-- Signed integer increment of the VF-mid block level. -/
def vfMidIntegerBlockDemand (R : ℕ) : ℤ :=
  (vfMidIntegerBlockLevel (R + 1) : ℤ) -
    (vfMidIntegerBlockLevel R : ℤ)

/-- Exact conservation law: next backlog = old backlog + new VF demand -
actual common-wheel prime supply. -/
theorem vfMidIntegerBlockBacklog_succ
    (R : ℕ) (hR : 2 ≤ R) :
    vfMidIntegerBlockBacklog (R + 1) =
      vfMidIntegerBlockBacklog R +
        vfMidIntegerBlockDemand R -
          (vfMidIntegerBlockPrimeSupply R : ℤ) := by
  have hp := vfMidIntegerBlockPrimeSupply_add_primeCounting R hR
  have hpZ :
      (vfMidIntegerBlockPrimeSupply R : ℤ) +
          (Nat.primeCounting (R ^ 2) : ℤ) =
        (Nat.primeCounting ((R + 1) ^ 2) : ℤ) := by
    exact_mod_cast hp
  unfold vfMidIntegerBlockBacklog vfMidIntegerBlockDemand
  omega

/-- Square-block capture is exactly the statement that the backlog is
nonnegative and no larger than the exact survivor supply in that block. -/
theorem vfMidIntegerBlockCaptured_iff_backlog_le_supply
    (R : ℕ) (hR : 2 ≤ R) :
    VFMidIntegerBlockCaptured R ↔
      0 ≤ vfMidIntegerBlockBacklog R ∧
        vfMidIntegerBlockBacklog R ≤
          (vfMidIntegerBlockPrimeSupply R : ℤ) := by
  have hp := vfMidIntegerBlockPrimeSupply_add_primeCounting R hR
  have hpZ :
      (vfMidIntegerBlockPrimeSupply R : ℤ) +
          (Nat.primeCounting (R ^ 2) : ℤ) =
        (Nat.primeCounting ((R + 1) ^ 2) : ℤ) := by
    exact_mod_cast hp
  unfold VFMidIntegerBlockCaptured vfMidIntegerBlockBacklog
  omega

/-! ## Flooring costs less than one count -/

/-- Integer VF demand differs from the real midpoint mass assigned to the same
square band by strictly less than one count. -/
theorem abs_vfMidIntegerBlockDemand_sub_bandMass_lt_one
    (R : ℕ) (hR : 2 ≤ R) :
    |((vfMidIntegerBlockDemand R : ℤ) : ℝ) - vfMidBandMass R| < 1 := by
  have hroundR := vfMidIntegerBlock_rounding_error R
  have hroundS := vfMidIntegerBlock_rounding_error (R + 1)
  have hsucc := vfMidFinishedMass_succ hR
  have hcast :
      ((vfMidIntegerBlockDemand R : ℤ) : ℝ) =
        (vfMidIntegerBlockLevel (R + 1) : ℝ) -
          (vfMidIntegerBlockLevel R : ℝ) := by
    simp [vfMidIntegerBlockDemand]
  rw [hcast, abs_lt]
  constructor <;> linarith

/-- The signed integer backlog is the negative real VF-mid endpoint discrepancy
up to the same sub-unit flooring error. -/
theorem abs_vfMidIntegerBlockBacklog_add_directError_lt_one
    (R : ℕ) :
    |((vfMidIntegerBlockBacklog R : ℤ) : ℝ) +
        vfMidDirectSquareEndpointError R| < 1 := by
  have hround := vfMidIntegerBlock_rounding_error R
  have hcast :
      ((vfMidIntegerBlockBacklog R : ℤ) : ℝ) =
        (vfMidIntegerBlockLevel R : ℝ) -
          (Nat.primeCounting (R ^ 2) : ℝ) := by
    simp [vfMidIntegerBlockBacklog]
  rw [hcast]
  unfold vfMidDirectSquareEndpointError
  rw [abs_lt]
  constructor <;> linarith

/-- The backlog increment is the negative real square-band prime excess, up to
less than one count.  Thus the finite backlog dynamics and the existing real
VF-mid dynamics are the same mechanism modulo flooring. -/
theorem abs_vfMidIntegerBlockBacklog_increment_add_bandError_lt_one
    (R : ℕ) (hR : 2 ≤ R) :
    |((((vfMidIntegerBlockBacklog (R + 1) -
          vfMidIntegerBlockBacklog R : ℤ)) : ℝ) +
        vfMidSquareBandError R)| < 1 := by
  have hrec := vfMidIntegerBlockBacklog_succ R hR
  have hdemand := abs_vfMidIntegerBlockDemand_sub_bandMass_lt_one R hR
  have hsupply := vfMidIntegerBlockPrimeSupply_eq_primeCard R hR
  have hcast :
      (((vfMidIntegerBlockBacklog (R + 1) -
          vfMidIntegerBlockBacklog R : ℤ)) : ℝ) =
        ((vfMidIntegerBlockDemand R : ℤ) : ℝ) -
          (vfMidIntegerBlockPrimeSupply R : ℝ) := by
    have hrec' :
        vfMidIntegerBlockBacklog (R + 1) -
            vfMidIntegerBlockBacklog R =
          vfMidIntegerBlockDemand R -
            (vfMidIntegerBlockPrimeSupply R : ℤ) := by
      omega
    rw [hrec']
    push_cast
    rfl
  rw [hcast]
  unfold vfMidSquareBandError
  rw [hsupply]
  have hsupplyCast :
      ((vfMidIntegerBlockPrimeSupply R : ℕ) : ℝ) =
        (((vfMidSquareBandPrimes R).card : ℕ) : ℝ) := by
    exact_mod_cast hsupply
  rw [hsupplyCast]
  linarith

/-- Immediate capture gives the sharper 2R+1 real endpoint bound because the
upper square is composite and the actual prime supply lives on only 2R
interior sites. -/
theorem vfMidIntegerBlockCaptured_abs_directError_lt_two_mul_add_one
    (R : ℕ) (hR : 2 ≤ R)
    (hcap : VFMidIntegerBlockCaptured R) :
    |vfMidDirectSquareEndpointError R| < 2 * (R : ℝ) + 1 := by
  have hcap' :=
    (vfMidIntegerBlockCaptured_iff_backlog_le_supply R hR).1 hcap
  have hclose := abs_vfMidIntegerBlockBacklog_add_directError_lt_one R
  have hsupply := vfMidIntegerBlockPrimeSupply_le_two_mul R hR
  have hB0 : (0 : ℝ) ≤ (vfMidIntegerBlockBacklog R : ℝ) := by
    exact_mod_cast hcap'.1
  have hBle :
      (vfMidIntegerBlockBacklog R : ℝ) ≤ 2 * (R : ℝ) := by
    have h1 :
        vfMidIntegerBlockBacklog R ≤ (2 * R : ℕ) := by
      exact hcap'.2.trans (by exact_mod_cast hsupply)
    exact_mod_cast h1
  rw [abs_lt] at hclose ⊢
  constructor <;> linarith

/-! ## The wheel changes only at a newly admitted prime -/

/-- If R+1 is composite, advancing the square clock adds no divisibility
coordinate to the common wheel. -/
theorem vfMidPrimesUpTo_succ_eq_of_not_prime
    (R : ℕ) (hnot : ¬ (R + 1).Prime) :
    primesUpTo (R + 1) = primesUpTo R := by
  ext p
  simp only [mem_primesUpTo]
  constructor
  · rintro ⟨hpPrime, hpLe⟩
    refine ⟨hpPrime, ?_⟩
    have hpNe : p ≠ R + 1 := by
      intro h
      subst p
      exact hnot hpPrime
    omega
  · rintro ⟨hpPrime, hpLe⟩
    exact ⟨hpPrime, by omega⟩

/-- If R+1 is prime, advancing the square clock adds exactly that one fresh
prime coordinate and no other coordinate. -/
theorem vfMidPrimesUpTo_succ_eq_insert_of_prime
    (R : ℕ) (hprime : (R + 1).Prime) :
    primesUpTo (R + 1) = insert (R + 1) (primesUpTo R) := by
  classical
  ext p
  simp only [mem_primesUpTo, Finset.mem_insert]
  constructor
  · rintro ⟨hpPrime, hpLe⟩
    by_cases hpEq : p = R + 1
    · exact Or.inl hpEq
    · exact Or.inr ⟨hpPrime, by omega⟩
  · rintro (hpEq | hpOld)
    · subst p
      exact ⟨hprime, le_rfl⟩
    · exact ⟨hpOld.1, by omega⟩

/-- Exact Euler renewal law for the common square-block wheel. -/
theorem vfMidPrimesUpTo_succ
    (R : ℕ) :
    primesUpTo (R + 1) =
      if (R + 1).Prime then insert (R + 1) (primesUpTo R)
      else primesUpTo R := by
  by_cases hprime : (R + 1).Prime
  · rw [if_pos hprime]
    exact vfMidPrimesUpTo_succ_eq_insert_of_prime R hprime
  · rw [if_neg hprime]
    exact vfMidPrimesUpTo_succ_eq_of_not_prime R hprime

end RHLean.Analysis
