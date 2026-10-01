import Mathlib
import «research.VF_MID_INTEGER_BLOCK_CAPTURE»
import «research.VF_MID_ALIGNED_STEP_GRAPH»
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

/-- Every interior integer in the R-th square block has the same
floor-square-root index R. -/
theorem vfMidSquareWheel_squareRootIndex_eq
    {R n : ℕ} (hn : n ∈ vfMidSquareWheelSites R) :
    vfMidSquareRootIndex (n : ℝ) = R := by
  have hnI := Finset.mem_Ioo.mp hn
  unfold vfMidSquareRootIndex
  rw [Real.nat_floor_real_sqrt_eq_nat_sqrt]
  symm
  exact (Nat.eq_sqrt').2 ⟨hnI.1.le, hnI.2⟩

/-- The open square carrier has exactly 2R integer sites. -/
theorem vfMidSquareWheelSites_card (R : ℕ) :
    (vfMidSquareWheelSites R).card = 2 * R := by
  unfold vfMidSquareWheelSites
  rw [Nat.card_Ioo]
  have hsq : (R + 1) ^ 2 = R ^ 2 + (2 * R + 1) := by
    ring
  rw [hsq]
  omega


/-- Common-wheel survivors on the interior square carrier. -/
def vfMidSquareWheelSurvivors (R : ℕ) : Finset ℕ := by
  classical
  exact (vfMidSquareWheelSites R).filter (lowWheelHighSurvivor R)

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
  constructor
  · intro hsurv
    by_contra hnPrime
    have hnPos : 0 < n := by omega
    have hnOne : n ≠ 1 := by omega
    let p := n.minFac
    have hpPrime : p.Prime := by
      simpa [p] using Nat.minFac_prime hnOne
    have hpDvd : p ∣ n := by
      simpa [p] using Nat.minFac_dvd n
    have hpSqLe : p ^ 2 ≤ n := by
      simpa [p] using Nat.minFac_sq_le_self hnPos hnPrime
    have hpLt : p < R + 1 := by
      by_contra hnot
      have hRp : R + 1 ≤ p := Nat.le_of_not_gt hnot
      have hpow : (R + 1) ^ 2 ≤ p ^ 2 :=
        Nat.pow_le_pow_left hRp 2
      omega
    have hpMem : p ∈ primesUpTo R :=
      mem_primesUpTo.mpr ⟨hpPrime, by omega⟩
    exact hsurv p hpMem hpDvd
  · intro hnPrime p hpMem hpDvd
    have hpPrime : p.Prime := prime_of_mem_primesUpTo hpMem
    have hpR : p ≤ R := (mem_primesUpTo.mp hpMem).2
    have hpn : p = n :=
      (Nat.prime_dvd_prime_iff_eq hpPrime hnPrime).mp hpDvd
    omega

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
        exact Nat.Prime.not_prime_pow' (by omega : (2 : ℕ) ≠ 1)
      exact hcomp hp
    exact ⟨⟨hlow, lt_of_le_of_ne hhigh hne⟩, hp⟩
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

/-- Using the actual interior carrier, the exact prime/common-wheel supply
is bounded by the sharper 2R sites. -/
theorem vfMidIntegerBlockPrimeSupply_le_two_mul
    (R : ℕ) :
    vfMidIntegerBlockPrimeSupply R ≤ 2 * R := by
  unfold vfMidIntegerBlockPrimeSupply
  rw [vfMidDirectPrimeBand_eq_squareWheelPrimes]
  have hsub :
      vfMidSquareWheelPrimes R ⊆ vfMidSquareWheelSites R := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have hcard := Finset.card_le_card hsub
  rw [vfMidSquareWheelSites_card] at hcard
  exact hcard


/-! ## Complete prefix-wheel hierarchy

For every cutoff S <= R, form the product of every prime coordinate already
known through S.  The corresponding survivor set on the R-th square block is
a deterministic superset of the actual primes.  These survivor sets decrease
monotonically as S grows, and at the full FTA cutoff S = R they are exactly the
prime set.

This records the entire finite square-block sieve, not just the special
2-3 or 2-5 wheels.
-/

/-- Product of all prime coordinates through the prefix cutoff S. -/
def vfMidPrefixWheelModulus (S : ℕ) : ℕ :=
  ∏ p ∈ primesUpTo S, p

/-- The prefix wheel modulus is always nonzero. -/
theorem vfMidPrefixWheelModulus_ne_zero (S : ℕ) :
    vfMidPrefixWheelModulus S ≠ 0 := by
  unfold vfMidPrefixWheelModulus
  exact Finset.prod_ne_zero_iff.mpr fun p hp =>
    (prime_of_mem_primesUpTo hp).ne_zero

/-- A prime divides the prefix wheel exactly when it is already present in the
prefix prime set. -/
theorem vfMidPrime_dvd_prefixWheelModulus_iff
    {q S : ℕ} (hq : q.Prime) :
    q ∣ vfMidPrefixWheelModulus S ↔ q ≤ S := by
  constructor
  · intro hdiv
    unfold vfMidPrefixWheelModulus at hdiv
    rcases hq.prime.exists_mem_finset_dvd hdiv with
      ⟨p, hpMem, hqp⟩
    have hpPrime := prime_of_mem_primesUpTo hpMem
    have hEq : q = p :=
      (Nat.prime_dvd_prime_iff_eq hq hpPrime).mp hqp
    subst p
    exact (mem_primesUpTo.mp hpMem).2
  · intro hqS
    unfold vfMidPrefixWheelModulus
    exact Finset.dvd_prod_of_mem id
      (mem_primesUpTo_of_prime_le hq hqS)

/-- Survival under the explicit low-prime wheel is exactly coprimality to the
corresponding prefix prime product. -/
theorem lowWheelHighSurvivor_iff_coprime_prefixWheel
    (S n : ℕ) :
    lowWheelHighSurvivor S n ↔
      (vfMidPrefixWheelModulus S).Coprime n := by
  unfold lowWheelHighSurvivor vfMidPrefixWheelModulus
  constructor
  · intro hsurv
    rw [Nat.coprime_prod_left_iff]
    intro p hpMem
    have hpPrime := prime_of_mem_primesUpTo hpMem
    exact (hpPrime.coprime_iff_not_dvd).2 (hsurv p hpMem)
  · intro hcop p hpMem
    rw [Nat.coprime_prod_left_iff] at hcop
    have hpPrime := prime_of_mem_primesUpTo hpMem
    exact (hpPrime.coprime_iff_not_dvd).1 (hcop p hpMem)

/-- Survivors of only the prefix wheel through S, measured on the R-th square
block. -/
def vfMidSquarePrefixWheelSurvivors (S R : ℕ) : Finset ℕ := by
  classical
  exact (vfMidSquareWheelSites R).filter (lowWheelHighSurvivor S)

/-- Enlarging the prefix wheel can only remove survivors. -/
theorem vfMidSquarePrefixWheelSurvivors_mono
    {S T R : ℕ} (hST : S ≤ T) :
    vfMidSquarePrefixWheelSurvivors T R ⊆
      vfMidSquarePrefixWheelSurvivors S R := by
  classical
  intro n hn
  rcases Finset.mem_filter.mp hn with ⟨hnSite, hnSurv⟩
  apply Finset.mem_filter.mpr
  refine ⟨hnSite, ?_⟩
  intro p hpS hpd
  have hpData := mem_primesUpTo.mp hpS
  have hpT : p ∈ primesUpTo T :=
    mem_primesUpTo.mpr ⟨hpData.1, hpData.2.trans hST⟩
  exact hnSurv p hpT hpd

/-- Every actual prime in block R survives every prefix wheel S <= R. -/
theorem vfMidSquareWheelPrimes_subset_prefixWheelSurvivors
    {S R : ℕ} (hR : 2 ≤ R) (hSR : S ≤ R) :
    vfMidSquareWheelPrimes R ⊆
      vfMidSquarePrefixWheelSurvivors S R := by
  classical
  intro n hn
  rcases Finset.mem_filter.mp hn with ⟨hnSite, hnPrime⟩
  apply Finset.mem_filter.mpr
  refine ⟨hnSite, ?_⟩
  intro p hpMem hpDvd
  have hpPrime := prime_of_mem_primesUpTo hpMem
  have hpS := (mem_primesUpTo.mp hpMem).2
  have hpn : p = n :=
    (Nat.prime_dvd_prime_iff_eq hpPrime hnPrime).mp hpDvd
  have hnI := Finset.mem_Ioo.mp hnSite
  subst p
  have hRltSq : R < R ^ 2 := by
    nlinarith
  omega

/-- The full prefix wheel S = R is definitionally the existing common wheel. -/
theorem vfMidSquarePrefixWheelSurvivors_full
    (R : ℕ) :
    vfMidSquarePrefixWheelSurvivors R R =
      vfMidSquareWheelSurvivors R := by
  rfl

/-- At the FTA cutoff S = R the prefix survivor population is exactly the
prime population in the square block. -/
theorem vfMidIntegerBlockPrimeSupply_eq_fullPrefixWheelCard
    (R : ℕ) (hR : 2 ≤ R) :
    vfMidIntegerBlockPrimeSupply R =
      (vfMidSquarePrefixWheelSurvivors R R).card := by
  rw [vfMidSquarePrefixWheelSurvivors_full]
  exact vfMidIntegerBlockPrimeSupply_eq_commonWheelCard R hR

/-- Every partial prefix wheel gives a rigorous upper bound on exact prime
supply. -/
theorem vfMidIntegerBlockPrimeSupply_le_prefixWheelCard
    (S R : ℕ) (hR : 2 ≤ R) (hSR : S ≤ R) :
    vfMidIntegerBlockPrimeSupply R ≤
      (vfMidSquarePrefixWheelSurvivors S R).card := by
  unfold vfMidIntegerBlockPrimeSupply
  rw [vfMidDirectPrimeBand_eq_squareWheelPrimes]
  exact Finset.card_le_card
    (vfMidSquareWheelPrimes_subset_prefixWheelSurvivors hR hSR)

/-- A generic finite wheel theorem: if every prime divisor of a nonzero modulus
a is already at most R, then every prime in the R-th square block is coprime to
a, so the block prime supply is bounded by the number of coprime residue
classes in an interval of length 2R. -/
theorem vfMidIntegerBlockPrimeSupply_le_coprimeWheel
    (R a : ℕ) (hR : 2 ≤ R) (ha0 : a ≠ 0)
    (hfac : ∀ q : ℕ, q.Prime → q ∣ a → q ≤ R) :
    vfMidIntegerBlockPrimeSupply R ≤
      Nat.totient a * ((2 * R) / a + 1) := by
  have hsub :
      vfMidSquareWheelPrimes R ⊆
        (Finset.Ico (R ^ 2 + 1) ((R + 1) ^ 2)).filter
          (fun n => a.Coprime n) := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnSite, hnPrime⟩
    have hnI := Finset.mem_Ioo.mp hnSite
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_Ico.mpr ⟨by omega, hnI.2⟩
    · have hnot : ¬ n ∣ a := by
        intro hna
        have hnR := hfac n hnPrime hna
        have hRltSq : R < R ^ 2 := by
          nlinarith
        omega
      exact ((hnPrime.coprime_iff_not_dvd).2 hnot).symm
  have hcard := Finset.card_le_card hsub
  have hperiod :=
    Nat.Ico_filter_coprime_le (R ^ 2 + 1) (2 * R) ha0
  have hspan : R ^ 2 + 1 + 2 * R = (R + 1) ^ 2 := by
    ring
  rw [hspan] at hperiod
  unfold vfMidIntegerBlockPrimeSupply
  rw [vfMidDirectPrimeBand_eq_squareWheelPrimes]
  exact hcard.trans hperiod

/-- Canonical totient envelope furnished by the prefix prime product through S. -/
def vfMidPrefixWheelEnvelope (S R : ℕ) : ℕ :=
  Nat.totient (vfMidPrefixWheelModulus S) *
    ((2 * R) / vfMidPrefixWheelModulus S + 1)

/-- Every prefix cutoff S <= R gives a valid deterministic prime-supply
envelope on block R. -/
theorem vfMidIntegerBlockPrimeSupply_le_prefixWheelEnvelope
    (S R : ℕ) (hR : 2 ≤ R) (hSR : S ≤ R) :
    vfMidIntegerBlockPrimeSupply R ≤
      vfMidPrefixWheelEnvelope S R := by
  unfold vfMidPrefixWheelEnvelope
  apply vfMidIntegerBlockPrimeSupply_le_coprimeWheel R
    (vfMidPrefixWheelModulus S) hR
    (vfMidPrefixWheelModulus_ne_zero S)
  intro q hq hdiv
  exact ((vfMidPrime_dvd_prefixWheelModulus_iff hq).1 hdiv).trans hSR

/-- The exact supply lies below every member of the entire prefix-wheel family.
This is the formal "choose the strongest available prefix" API. -/
theorem vfMidIntegerBlockPrimeSupply_le_every_prefixWheelEnvelope
    (R : ℕ) (hR : 2 ≤ R) :
    ∀ S : ℕ, S ≤ R →
      vfMidIntegerBlockPrimeSupply R ≤
        vfMidPrefixWheelEnvelope S R := by
  intro S hSR
  exact vfMidIntegerBlockPrimeSupply_le_prefixWheelEnvelope S R hR hSR

/-! ## Prefix-wheel support for aligned vertical faces

The exact prime-supply conservation law turns a vertical graph crossing into a
finite square-wheel statement.  Prefix-wheel envelopes can therefore certify
the upper side of a vertical face using only arithmetic already visible below
the square-root cutoff.
-/

/-- Exact supply form of the right vertical face. -/
theorem vfMidAlignedRightVerticalCrossed_iff_primeSupply
    (c : ℝ) (R : ℕ) :
    VFMidAlignedRightVerticalCrossed c R ↔
      vfMidAlignedIntegerBlockLevel c R ≤
        Nat.primeCounting (R ^ 2) +
          vfMidIntegerBlockPrimeSupply R ∧
      Nat.primeCounting (R ^ 2) +
          vfMidIntegerBlockPrimeSupply R ≤
        vfMidAlignedIntegerBlockLevel c (R + 1) := by
  have hp := vfMidIntegerBlockPrimeSupply_add_primeCounting R
  unfold VFMidAlignedRightVerticalCrossed
  omega


/-- Exact FTA form of the right vertical face: at the full cutoff S = R the
survivor cardinality is the prime supply itself. -/
theorem vfMidAlignedRightVerticalCrossed_iff_fullPrefixWheelCard
    (c : ℝ) (R : ℕ) (hR : 2 ≤ R) :
    VFMidAlignedRightVerticalCrossed c R ↔
      vfMidAlignedIntegerBlockLevel c R ≤
        Nat.primeCounting (R ^ 2) +
          (vfMidSquarePrefixWheelSurvivors R R).card ∧
      Nat.primeCounting (R ^ 2) +
          (vfMidSquarePrefixWheelSurvivors R R).card ≤
        vfMidAlignedIntegerBlockLevel c (R + 1) := by
  rw [vfMidAlignedRightVerticalCrossed_iff_primeSupply,
    vfMidIntegerBlockPrimeSupply_eq_fullPrefixWheelCard R hR]

/-- Any partial prefix-wheel survivor count can certify a right vertical face;
this is sharper than replacing that exact finite count by its totient envelope. -/
theorem vfMidAlignedRightVerticalCrossed_of_prefixWheelCard
    (c : ℝ) (S R : ℕ) (hR : 2 ≤ R) (hSR : S ≤ R)
    (hlow :
      vfMidAlignedIntegerBlockLevel c R ≤
        Nat.primeCounting (R ^ 2))
    (hroom :
      Nat.primeCounting (R ^ 2) +
          (vfMidSquarePrefixWheelSurvivors S R).card ≤
        vfMidAlignedIntegerBlockLevel c (R + 1)) :
    VFMidAlignedRightVerticalCrossed c R := by
  rw [vfMidAlignedRightVerticalCrossed_iff_primeSupply]
  have hsupply :=
    vfMidIntegerBlockPrimeSupply_le_prefixWheelCard S R hR hSR
  constructor <;> omega

/-- If pi is already at or above the current aligned VF level and one chosen
prefix-wheel envelope fits inside the headroom to the next aligned level, then
the red staircase must intersect the right vertical VF face. -/
theorem vfMidAlignedRightVerticalCrossed_of_prefixWheelEnvelope
    (c : ℝ) (S R : ℕ) (hR : 2 ≤ R) (hSR : S ≤ R)
    (hlow :
      vfMidAlignedIntegerBlockLevel c R ≤
        Nat.primeCounting (R ^ 2))
    (hroom :
      Nat.primeCounting (R ^ 2) +
          vfMidPrefixWheelEnvelope S R ≤
        vfMidAlignedIntegerBlockLevel c (R + 1)) :
    VFMidAlignedRightVerticalCrossed c R := by
  rw [vfMidAlignedRightVerticalCrossed_iff_primeSupply]
  have hsupply :=
    vfMidIntegerBlockPrimeSupply_le_prefixWheelEnvelope S R hR hSR
  constructor <;> omega

/-- Equivalent existential API: any prefix cutoff whose deterministic envelope
fits the available VF headroom certifies a right-vertical crossing. -/
theorem vfMidAlignedRightVerticalCrossed_of_exists_prefixWheel
    (c : ℝ) (R : ℕ) (hR : 2 ≤ R)
    (hlow :
      vfMidAlignedIntegerBlockLevel c R ≤
        Nat.primeCounting (R ^ 2))
    (hex :
      ∃ S : ℕ, S ≤ R ∧
        Nat.primeCounting (R ^ 2) +
            vfMidPrefixWheelEnvelope S R ≤
          vfMidAlignedIntegerBlockLevel c (R + 1)) :
    VFMidAlignedRightVerticalCrossed c R := by
  rcases hex with ⟨S, hSR, hroom⟩
  exact vfMidAlignedRightVerticalCrossed_of_prefixWheelEnvelope
    c S R hR hSR hlow hroom

/-- Applying the same prefix-wheel certificate to the preceding block gives a
left-vertical crossing at x = R^2. -/
theorem vfMidAlignedLeftVerticalCrossed_of_prefixWheelEnvelope
    (c : ℝ) (S R : ℕ) (hR : 3 ≤ R) (hS : S ≤ R - 1)
    (hlow :
      vfMidAlignedIntegerBlockLevel c (R - 1) ≤
        Nat.primeCounting ((R - 1) ^ 2))
    (hroom :
      Nat.primeCounting ((R - 1) ^ 2) +
          vfMidPrefixWheelEnvelope S (R - 1) ≤
        vfMidAlignedIntegerBlockLevel c R) :
    VFMidAlignedLeftVerticalCrossed c R := by
  have hpred : 2 ≤ R - 1 := by omega
  have hright :=
    vfMidAlignedRightVerticalCrossed_of_prefixWheelEnvelope
      c S (R - 1) hpred hS hlow hroom
  rcases hright with ⟨hlo, hup⟩
  have hsucc : R - 1 + 1 = R := by omega
  constructor
  · simpa [hsucc] using hlo
  · simpa [hsucc] using hup

/-! ## Elementary 2-5 and 2-3 wheel bounds

Mathlib's `Nat.primeCounting_add_le` is the exact finite sieve estimate needed
here: after a fixed cutoff k >= a, primes in the next n sites inject into the
residue classes coprime to a.  Taking a = 10 leaves four residue classes out of
ten (the 2-5 wheel), while a = 6 leaves two classes out of six (the 2-3 wheel).

The +1 below is only the incomplete final residue period.  It is the finite
endpoint correction behind the informal density statements 0.4 and 1/3.
-/

/-- Prime-counting version of Mathlib 4.24's `primeCounting'_add_le`.
This is the non-strict endpoint wrapper later Mathlib versions expose directly. -/
theorem vfMid_primeCounting_totient_add_le
    {a k : ℕ} (h0 : a ≠ 0) (h1 : a ≤ k) (n : ℕ) :
    Nat.primeCounting (k + n) ≤
      Nat.primeCounting k + Nat.totient a * (n / a + 1) := by
  have h :=
    Nat.primeCounting'_add_le
      (a := a) (k := k + 1) h0 (by omega) n
  have harg : k + 1 + n = k + n + 1 := by
    omega
  rw [harg] at h
  exact h

/-- Exact finite 2-5 wheel bound for one square block.  Asymptotically this is
0.4 times the block width, with one incomplete period of length ten allowed. -/
theorem vfMidIntegerBlockPrimeSupply_le_two_five_wheel
    (R : ℕ) (hR : 4 ≤ R) :
    vfMidIntegerBlockPrimeSupply R ≤
      4 * ((2 * R + 1) / 10 + 1) := by
  have h10 : 10 ≤ R ^ 2 := by
    nlinarith
  have hpc :=
    vfMid_primeCounting_totient_add_le
      (a := 10) (k := R ^ 2) (by norm_num) h10 (2 * R + 1)
  have hsq : R ^ 2 + (2 * R + 1) = (R + 1) ^ 2 := by
    ring
  rw [hsq, show Nat.totient 10 = 4 from rfl] at hpc
  have hband := vfMidIntegerBlockPrimeSupply_add_primeCounting R
  omega

/-- Cross-multiplied 0.4-density form of the 2-5 wheel estimate.  The additive
20 is exactly four possible survivors from the incomplete final ten-period:
5 P_R <= 2(2R+1) + 20. -/
theorem vfMidIntegerBlockPrimeSupply_five_mul_le_two_width_add_twenty
    (R : ℕ) (hR : 4 ≤ R) :
    5 * vfMidIntegerBlockPrimeSupply R ≤
      2 * (2 * R + 1) + 20 := by
  have hwheel := vfMidIntegerBlockPrimeSupply_le_two_five_wheel R hR
  omega

/-- The still smaller 2-3 wheel already gives a one-third-density finite
estimate once R^2 is beyond the modulus 6. -/
theorem vfMidIntegerBlockPrimeSupply_le_two_three_wheel
    (R : ℕ) (hR : 3 ≤ R) :
    vfMidIntegerBlockPrimeSupply R ≤
      2 * ((2 * R + 1) / 6 + 1) := by
  have h6 : 6 ≤ R ^ 2 := by
    nlinarith
  have hpc :=
    vfMid_primeCounting_totient_add_le
      (a := 6) (k := R ^ 2) (by norm_num) h6 (2 * R + 1)
  have hsq : R ^ 2 + (2 * R + 1) = (R + 1) ^ 2 := by
    ring
  rw [hsq, show Nat.totient 6 = 2 from rfl] at hpc
  have hband := vfMidIntegerBlockPrimeSupply_add_primeCounting R
  omega

/-- Global elementary half-width bound.  For R >= 4 the 2-3 wheel is already
strong enough to force P_R <= R; the two initial square blocks are finite
kernel computations. -/
theorem vfMidIntegerBlockPrimeSupply_le_R
    (R : ℕ) (hR : 2 ≤ R) :
    vfMidIntegerBlockPrimeSupply R ≤ R := by
  by_cases hlarge : 4 ≤ R
  · have hwheel :=
      vfMidIntegerBlockPrimeSupply_le_two_three_wheel R (by omega)
    omega
  · interval_cases R <;> decide

/-- Therefore the exact number of primes in every nontrivial square block is
strictly less than half of the repository block width 2R+1. -/
theorem vfMidIntegerBlockPrimeSupply_two_mul_lt_width
    (R : ℕ) (hR : 2 ≤ R) :
    2 * vfMidIntegerBlockPrimeSupply R < 2 * R + 1 := by
  have h := vfMidIntegerBlockPrimeSupply_le_R R hR
  omega

/-- Real-valued form of the strict half-width theorem. -/
theorem vfMidIntegerBlockPrimeSupply_lt_half_width
    (R : ℕ) (hR : 2 ≤ R) :
    (vfMidIntegerBlockPrimeSupply R : ℝ) <
      (2 * (R : ℝ) + 1) / 2 := by
  have hnat := vfMidIntegerBlockPrimeSupply_two_mul_lt_width R hR
  have hreal :
      2 * (vfMidIntegerBlockPrimeSupply R : ℝ) <
        2 * (R : ℝ) + 1 := by
    exact_mod_cast hnat
  linarith

/-- The universal half-width estimate gives a simple sufficient condition:
R counts of headroom above the current prime endpoint are enough for the right
vertical face. -/
theorem vfMidAlignedRightVerticalCrossed_of_R_headroom
    (c : ℝ) (R : ℕ) (hR : 2 ≤ R)
    (hlow :
      vfMidAlignedIntegerBlockLevel c R ≤
        Nat.primeCounting (R ^ 2))
    (hroom :
      Nat.primeCounting (R ^ 2) + R ≤
        vfMidAlignedIntegerBlockLevel c (R + 1)) :
    VFMidAlignedRightVerticalCrossed c R := by
  rw [vfMidAlignedRightVerticalCrossed_iff_primeSupply]
  have hsupply := vfMidIntegerBlockPrimeSupply_le_R R hR
  constructor <;> omega

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

/-- Sharper capture consequence using the exact 2R interior survivor supply:
the real VF-mid endpoint discrepancy is less than one interior block width plus
the sub-unit floor error. -/
theorem vfMidIntegerBlockCaptured_abs_directError_lt_two_mul_add_one
    (R : ℕ) (hcap : VFMidIntegerBlockCaptured R) :
    |vfMidDirectSquareEndpointError R| < 2 * (R : ℝ) + 1 := by
  have hcap' :=
    (vfMidIntegerBlockCaptured_iff_backlog_le_supply R).1 hcap
  have hclose := abs_vfMidIntegerBlockBacklog_add_directError_lt_one R
  have hsupply := vfMidIntegerBlockPrimeSupply_le_two_mul R
  have hB0 : (0 : ℝ) ≤ (vfMidIntegerBlockBacklog R : ℝ) := by
    exact_mod_cast hcap'.1
  have hBle :
      (vfMidIntegerBlockBacklog R : ℝ) ≤ 2 * (R : ℝ) := by
    have hsupplyZ :
        (vfMidIntegerBlockPrimeSupply R : ℤ) ≤ (2 * R : ℕ) := by
      exact_mod_cast hsupply
    have h1 :
        vfMidIntegerBlockBacklog R ≤ (2 * R : ℕ) :=
      hcap'.2.trans hsupplyZ
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
