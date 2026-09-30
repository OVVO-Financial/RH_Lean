import Mathlib
import «research.VF_MID_INTEGER_BLOCK_CAPTURE»
import RHLean.Arithmetic.PrimesUpToFrontier
import RHLean.Proof.LowWheelHighPrimeSurvivor

/-!
# VF-mid square-wheel backlog dynamics

For an interior integer n in the square block

  R^2 < n < (R+1)^2,

every composite n has a prime divisor at most R.  Thus primality throughout
the block is exactly survival under one common finite divisibility wheel:
all primes at most R.

The repository's direct prime block is (R^2,(R+1)^2].  Its upper endpoint is
a square and hence contributes no prime, so it has exactly the same prime
population as the open interior carrier used for the common-wheel statement.

With

  K_R = floor(vfMidFinishedMass R),
  B_R = K_R - pi(R^2),
  Q_R = K_(R+1) - K_R,
  P_R = exact square-block prime/common-wheel survivor supply,

the exact conservation law is

  B_(R+1) = B_R + Q_R - P_R.

Capture is exactly 0 <= B_R <= P_R, while the integer demand satisfies

  |Q_R - vfMidBandMass R| < 1.

No PNT-rate or probabilistic independence assumption appears.  Persistence of
positive backlog is deliberately left as the next arithmetic target.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

/-! ## One square block has one common factor wheel -/

/-- Interior integer carrier of the R-th square block. -/
def vfMidSquareWheelSites (R : ℕ) : Finset ℕ :=
  Finset.Ioo (R ^ 2) ((R + 1) ^ 2)

/-- Prime sites on the interior square carrier. -/
def vfMidSquareWheelPrimes (R : ℕ) : Finset ℕ :=
  (vfMidSquareWheelSites R).filter Nat.Prime

/-- Common-wheel survivors on the interior square carrier. -/
def vfMidSquareWheelSurvivors (R : ℕ) : Finset ℕ :=
  (vfMidSquareWheelSites R).filter (lowWheelHighSurvivor R)

/-- On one square block, every interior integer is tested against the same
prime coordinates <= R: survival under that wheel is exactly primality. -/
theorem vfMidSquareBand_commonWheelSurvivor_iff_prime
    {R n : ℕ} (hR : 2 ≤ R)
    (hn : n ∈ vfMidSquareWheelSites R) :
    lowWheelHighSurvivor R n ↔ n.Prime := by
  have hnI := Finset.mem_Ioo.mp hn
  have hRltSq : R < R ^ 2 := by
    nlinarith
  have hRn : R < n := hRltSq.trans hnI.1
  have hnX : n ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    omega
  exact lowWheelHighSurvivor_iff_prime hR hRn hnX

/-- Fundamental-factorization form: every composite interior site is killed by
at least one prime coordinate in the common wheel through R. -/
theorem vfMidSquareBand_composite_has_commonWheel_divisor
    {R n : ℕ} (hR : 2 ≤ R)
    (hn : n ∈ vfMidSquareWheelSites R)
    (hcomp : ¬ n.Prime) :
    ∃ p ∈ primesUpTo R, p ∣ n := by
  by_contra hnone
  have hsurv : lowWheelHighSurvivor R n := by
    intro p hp hpd
    apply hnone
    exact ⟨p, hp, hpd⟩
  exact hcomp
    ((vfMidSquareBand_commonWheelSurvivor_iff_prime hR hn).1 hsurv)

/-- Common-wheel survivors are literally the prime sites of the interior
square carrier. -/
theorem vfMidSquareWheelSurvivors_eq_primes
    (R : ℕ) (hR : 2 ≤ R) :
    vfMidSquareWheelSurvivors R = vfMidSquareWheelPrimes R := by
  classical
  ext n
  simp only [vfMidSquareWheelSurvivors, vfMidSquareWheelPrimes,
    Finset.mem_filter]
  constructor
  · rintro ⟨hn, hsurv⟩
    exact ⟨hn, (vfMidSquareBand_commonWheelSurvivor_iff_prime hR hn).1 hsurv⟩
  · rintro ⟨hn, hp⟩
    exact ⟨hn, (vfMidSquareBand_commonWheelSurvivor_iff_prime hR hn).2 hp⟩

/-- The repository direct block (R^2,(R+1)^2] has the same prime population
as the open interior carrier: the only extra site is the composite upper
square. -/
theorem vfMidDirectPrimeBand_eq_squareWheelPrimes (R : ℕ) :
    vfMidDirectPrimeBand R = vfMidSquareWheelPrimes R := by
  classical
  ext n
  simp only [vfMidDirectPrimeBand, vfMidSquareWheelPrimes,
    vfMidSquareWheelSites, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Ioo]
  constructor
  · rintro ⟨⟨hlow, hhigh⟩, hp⟩
    have hne : n ≠ (R + 1) ^ 2 := by
      intro hn
      subst n
      have hcomp : ¬ ((R + 1) ^ 2).Prime := by
        exact Nat.not_prime_pow' (R + 1) 2 (by omega)
      exact hcomp hp
    exact ⟨⟨hlow, lt_of_le_of_ne hhigh (Ne.symm hne)⟩, hp⟩
  · rintro ⟨⟨hlow, hhigh⟩, hp⟩
    exact ⟨⟨hlow, hhigh.le⟩, hp⟩

/-! ## Exact prime/common-wheel supply -/

/-- Exact prime supply in one repository square block. -/
def vfMidIntegerBlockPrimeSupply (R : ℕ) : ℕ :=
  (vfMidDirectPrimeBand R).card

/-- The direct prime supply is exactly the common-wheel survivor cardinality. -/
theorem vfMidIntegerBlockPrimeSupply_eq_commonWheelCard
    (R : ℕ) (hR : 2 ≤ R) :
    vfMidIntegerBlockPrimeSupply R =
      (vfMidSquareWheelSurvivors R).card := by
  unfold vfMidIntegerBlockPrimeSupply
  rw [vfMidDirectPrimeBand_eq_squareWheelPrimes,
    ← vfMidSquareWheelSurvivors_eq_primes R hR]

/-- Supply plus the old endpoint count is exactly the next endpoint count. -/
theorem vfMidIntegerBlockPrimeSupply_add_primeCounting
    (R : ℕ) :
    vfMidIntegerBlockPrimeSupply R + Nat.primeCounting (R ^ 2) =
      Nat.primeCounting ((R + 1) ^ 2) := by
  unfold vfMidIntegerBlockPrimeSupply
  exact vfMidDirectPrimeBand_card_add_primeCounting_eq R

/-- The repository block has 2R+1 integer seats, so its prime supply cannot
exceed that deterministic width. -/
theorem vfMidIntegerBlockPrimeSupply_le_two_mul_add_one
    (R : ℕ) :
    vfMidIntegerBlockPrimeSupply R ≤ 2 * R + 1 := by
  have hpc := vfMid_primeCounting_add_le (R ^ 2) (2 * R + 1)
  have hsq : R ^ 2 + (2 * R + 1) = (R + 1) ^ 2 := by
    ring
  rw [hsq] at hpc
  have hband := vfMidIntegerBlockPrimeSupply_add_primeCounting R
  omega

/-! ## Integer backlog and demand -/

/-- Signed number of integer VF-mid counts still above the prime staircase at
the left square endpoint. -/
def vfMidIntegerBlockBacklog (R : ℕ) : ℤ :=
  (vfMidIntegerBlockLevel R : ℤ) - (Nat.primeCounting (R ^ 2) : ℤ)

/-- Signed integer increment of the VF-mid square-block level. -/
def vfMidIntegerBlockDemand (R : ℕ) : ℤ :=
  (vfMidIntegerBlockLevel (R + 1) : ℤ) -
    (vfMidIntegerBlockLevel R : ℤ)

/-- Exact conservation law: next backlog equals old backlog plus integer VF
demand minus exact prime/common-wheel survivor supply. -/
theorem vfMidIntegerBlockBacklog_succ (R : ℕ) :
    vfMidIntegerBlockBacklog (R + 1) =
      vfMidIntegerBlockBacklog R +
        vfMidIntegerBlockDemand R -
          (vfMidIntegerBlockPrimeSupply R : ℤ) := by
  have hp := vfMidIntegerBlockPrimeSupply_add_primeCounting R
  have hpZ :
      (vfMidIntegerBlockPrimeSupply R : ℤ) +
          (Nat.primeCounting (R ^ 2) : ℤ) =
        (Nat.primeCounting ((R + 1) ^ 2) : ℤ) := by
    exact_mod_cast hp
  unfold vfMidIntegerBlockBacklog vfMidIntegerBlockDemand
  omega

/-- Capture is exactly backlog lying between zero and the available prime
supply in the current square block. -/
theorem vfMidIntegerBlockCaptured_iff_backlog_le_supply
    (R : ℕ) :
    VFMidIntegerBlockCaptured R ↔
      0 ≤ vfMidIntegerBlockBacklog R ∧
        vfMidIntegerBlockBacklog R ≤
          (vfMidIntegerBlockPrimeSupply R : ℤ) := by
  have hp := vfMidIntegerBlockPrimeSupply_add_primeCounting R
  have hpZ :
      (vfMidIntegerBlockPrimeSupply R : ℤ) +
          (Nat.primeCounting (R ^ 2) : ℤ) =
        (Nat.primeCounting ((R + 1) ^ 2) : ℤ) := by
    exact_mod_cast hp
  unfold VFMidIntegerBlockCaptured vfMidIntegerBlockBacklog
  omega

/-! ## Real/integer agreement up to the floor error -/

/-- Integer VF demand differs from the real midpoint band mass by less than
one count. -/
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

/-- Integer backlog is the negative real VF-mid endpoint discrepancy up to
strictly less than one count of flooring. -/
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

/-- The integer backlog increment is the negative real direct band error up to
strictly less than one count. -/
theorem abs_vfMidIntegerBlockBacklog_increment_add_bandError_lt_one
    (R : ℕ) (hR : 2 ≤ R) :
    |((((vfMidIntegerBlockBacklog (R + 1) -
          vfMidIntegerBlockBacklog R : ℤ)) : ℝ) +
        vfMidDirectBandError R)| < 1 := by
  have hrec := vfMidIntegerBlockBacklog_succ R
  have hdemand := abs_vfMidIntegerBlockDemand_sub_bandMass_lt_one R hR
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
  unfold vfMidDirectBandError vfMidDirectPrimeBandCount
    vfMidIntegerBlockPrimeSupply
  simpa only [sub_add_sub_cancel] using hdemand

/-- Immediate capture yields the deterministic one-block real discrepancy
bound, with one additional count for flooring. -/
theorem vfMidIntegerBlockCaptured_abs_directError_lt_supplyWidth
    (R : ℕ) (hcap : VFMidIntegerBlockCaptured R) :
    |vfMidDirectSquareEndpointError R| < 2 * (R : ℝ) + 2 := by
  have hcap' :=
    (vfMidIntegerBlockCaptured_iff_backlog_le_supply R).1 hcap
  have hclose := abs_vfMidIntegerBlockBacklog_add_directError_lt_one R
  have hsupply := vfMidIntegerBlockPrimeSupply_le_two_mul_add_one R
  have hB0 : (0 : ℝ) ≤ (vfMidIntegerBlockBacklog R : ℝ) := by
    exact_mod_cast hcap'.1
  have hBle :
      (vfMidIntegerBlockBacklog R : ℝ) ≤ 2 * (R : ℝ) + 1 := by
    have h1 :
        vfMidIntegerBlockBacklog R ≤ (2 * R + 1 : ℕ) := by
      have hsupplyZ :
          (vfMidIntegerBlockPrimeSupply R : ℤ) ≤
            (2 * R + 1 : ℕ) := by
        exact_mod_cast hsupply
      exact hcap'.2.trans hsupplyZ
    exact_mod_cast h1
  rw [abs_lt] at hclose ⊢
  constructor <;> linarith

/-! ## Exact Euler renewal of the common wheel -/

/-- If R+1 is composite, advancing the square clock adds no new prime
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

/-- If R+1 is prime, advancing the square clock inserts exactly that one new
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

/-- Exact renewal law: the square-block wheel is unchanged at a composite
clock tick and gains exactly the fresh prime coordinate at a prime clock tick. -/
theorem vfMidPrimesUpTo_succ (R : ℕ) :
    primesUpTo (R + 1) =
      if (R + 1).Prime then insert (R + 1) (primesUpTo R)
      else primesUpTo R := by
  by_cases hprime : (R + 1).Prime
  · rw [if_pos hprime]
    exact vfMidPrimesUpTo_succ_eq_insert_of_prime R hprime
  · rw [if_neg hprime]
    exact vfMidPrimesUpTo_succ_eq_of_not_prime R hprime

end RHLean.Analysis
