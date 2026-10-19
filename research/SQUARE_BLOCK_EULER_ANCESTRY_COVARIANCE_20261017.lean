import Mathlib
import RHLean.Analysis.CanonicalLowOccupancy
import RHLean.Arithmetic.SignedBuchstabRecursion
import RHLean.Arithmetic.PrimeWheelMobiusRecovery
import RHLean.Analysis.MathlibMertensHook
import RHLean.Proof.SquareBlockSmoothTransportGram
import RHLean.Proof.CanonicalGapAncestryHighRealization

/-!
# Fixed-square-wheel Möbius parity, density, and complete pair ancestry

Exact arithmetic formalization of the 2026-10-17 discussion.
The low-prime wheel is fixed on [R^2,(R+1)^2).  A squarefree
integer in this block has at most one factor outside that wheel;
any high-prime cofactor lies at most R.  Every fresh high prime
reverses the complete Möbius sign of its admitted cofactor.

We distinguish uncentered signed Möbius pair sums from statistical
covariances, keep the genuine squarefree diagonal, and group *all*
physical pairs by (factor depth of m, factor depth of n, shared
prime depth).  Factor depth zero includes n=1.

Everything proved here is a finite identity or support restriction.
No uniform all-scale signed bound and no RH are claimed.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators
open RHLean.Arithmetic
open RHLean.Analysis

namespace RHLean.Proof

/-! ## Uniform factor set on a canonical square block -/

/-- This square block has exactly one integer square-root coordinate. -/
theorem squareBlock_fixed_sqrt
    {R n : ℕ} (hn : n ∈ canonicalSquareBlock R) :
    Nat.sqrt n = R :=
  CanonicalGapAncestryHighRealization.sqrt_eq_of_mem_canonicalSquareBlock hn

/-- A number in a positive square block is prime exactly when it survives
all primes in the common low wheel, *including* numbers beyond R^2.
No appeal to a prime density estimate or a zeta zero is needed. -/
theorem squareBlock_prime_iff_lowWheel
    {R n : ℕ} (hR : 2 ≤ R) (hn : n ∈ canonicalSquareBlock R) :
    n.Prime ↔ ∀ p ∈ primesUpTo R, ¬ p ∣ n := by
  have hnI : R ^ 2 ≤ n ∧ n < (R + 1) ^ 2 := by
    simpa [canonicalSquareBlock, Finset.mem_Ico] using! hn
  have hnR : R < n := by nlinarith
  constructor
  · intro hnPrime p hpWheel hpd
    obtain ⟨hpPrime, hpR⟩ := mem_primesUpTo.mp hpWheel
    have hpn : p = n := (Nat.prime_dvd_prime_iff_eq hpPrime hnPrime).mp hpd
    omega
  · intro hWheel
    by_contra hnPrime
    have hnpos : 0 < n := by omega
    have hn1 : n ≠ 1 := by omega
    let p := n.minFac
    have hpPrime : p.Prime := by
      simpa [p] using! Nat.minFac_prime hn1
    have hpd : p ∣ n := by
      simpa [p] using! Nat.minFac_dvd n
    have hpSquare : p ^ 2 ≤ n := by
      simpa [p] using! Nat.minFac_sq_le_self hnpos hnPrime
    have hpR : p ≤ R := by
      by_contra h
      have hlarge : R + 1 ≤ p := by omega
      have hSq : (R + 1) ^ 2 ≤ p ^ 2 :=
        Nat.pow_le_pow_left hlarge 2
      omega
    have hpWheel : p ∈ primesUpTo R :=
      mem_primesUpTo.mpr ⟨hpPrime, hpR⟩
    exact hWheel p hpWheel hpd

/-- On a single square block, the set of prime factors outside the
fixed wheel has cardinality at most one.  This also applies to
squareful n, before restricting to nonzero Möbius sites. -/
theorem squareBlock_atMostOneHighPrime
    {R n : ℕ} (hR : 2 ≤ R) (hn : n ∈ canonicalSquareBlock R) :
    (n.primeFactors \ primesUpTo R).card ≤ 1 := by
  let U : ℕ := (R + 1) ^ 2 - 1
  have hblock : R ^ 2 ≤ n ∧ n < (R + 1) ^ 2 := by
    simpa [canonicalSquareBlock, Finset.mem_Ico] using! hn
  have hUlow : R ^ 2 ≤ U := by
    have hsquare : (R + 1) ^ 2 = R ^ 2 + 2 * R + 1 := by ring
    dsimp [U]
    rw [hsquare]
    omega
  have hUhigh : U < (R + 1) ^ 2 := by
    dsimp [U]
    omega
  have hroot : Nat.sqrt U = R := by
    exact ((Nat.eq_sqrt').2 ⟨hUlow, hUhigh⟩).symm
  have hcover : PrimeWheelSqrtCoverage (primesUpTo R) U := by
    intro p hp hle
    rw [hroot] at hle
    exact mem_primesUpTo.mpr ⟨hp, hle⟩
  have hnpos : 0 < n := by nlinarith
  have hnU : n ≤ U := by
    dsimp [U]
    omega
  exact large_primeFactors_card_le_one (primesUpTo R) hcover hnpos hnU

/-- If p>R divides an integer in a square block, its complete
cofactor is ≤R, regardless of how many low factors it contains. -/
theorem squareBlock_highPrimeCofactor_le
    {R n p : ℕ} (hn : n ∈ canonicalSquareBlock R)
    (hpR : R < p) (hpd : p ∣ n) :
    n / p ≤ R := by
  have hnupper : n < (R + 1) ^ 2 :=
    (Finset.mem_Ico.mp (show n ∈ Finset.Ico (R ^ 2) ((R + 1) ^ 2) from hn)).2
  by_contra h
  have hco : R + 1 ≤ n / p := by omega
  have hpp : R + 1 ≤ p := by omega
  have hprod : (R + 1) * (R + 1) ≤ p * (n / p) :=
    Nat.mul_le_mul hpp hco
  have hfactor : p * (n / p) = n := Nat.mul_div_cancel' hpd
  nlinarith

/-- Every admitted high prime reverses the entire Möbius parity
of a cofactor, even when the cofactor has many distinct prime factors. -/
theorem highPrimeCofactor_sign_reversal
    {R p c : ℕ} (hp : p.Prime) (hlarge : R < p)
    (hc : 0 < c) (hcR : c ≤ R) :
    μ (p * c) = -μ c := by
  have hnot : ¬ p ∣ c := by
    intro hdiv
    have hle : p ≤ c := Nat.le_of_dvd hc hdiv
    omega
  exact RHLean.Arithmetic.moebius_prime_mul hp hnot

/-! ## The exact signed high-prime cofactor bill on the same block -/

/-- A physical site on the high-prime side of its fixed square block has
its *complete* Mobius sign reversed from its genuine low cofactor.  This
retains arbitrarily many distinct low primes, and squareful cofactors
remain zero.  It is not an estimate. -/
theorem squareBlock_highPrimeOwnerSign
    {R n : ℕ} (hR : 2 ≤ R) (hn : n ∈ canonicalSquareBlock R)
    (hhigh : R < canonicalLargestPrimeFactor n) :
    μ n = -μ (canonicalCofactor n) := by
  have hnI : R ^ 2 ≤ n ∧ n < (R + 1) ^ 2 := by
    simpa [canonicalSquareBlock, Finset.mem_Ico] using! hn
  have hn1 : 1 < n := by nlinarith
  have hp : (canonicalLargestPrimeFactor n).Prime :=
    canonicalLargestPrimeFactor_prime hn1
  have hpDvd : canonicalLargestPrimeFactor n ∣ n :=
    canonicalLargestPrimeFactor_dvd hn1
  have hc : canonicalCofactor n ≤ R := by
    simpa only [canonicalCofactor] using!
      squareBlock_highPrimeCofactor_le hn hhigh hpDvd
  have hprod := canonicalCofactor_mul_largestPrimeFactor hn1
  have hcpos : 0 < canonicalCofactor n := by
    by_contra h
    have hc0 : canonicalCofactor n = 0 := by omega
    rw [hc0] at hprod
    simp at hprod
    omega
  have hflip := highPrimeCofactor_sign_reversal hp hhigh hcpos hc
  calc
    μ n = μ (canonicalCofactor n * canonicalLargestPrimeFactor n) := by
      rw [hprod]
    _ = μ (canonicalLargestPrimeFactor n * canonicalCofactor n) := by
      rw [Nat.mul_comm]
    _ = -μ (canonicalCofactor n) := hflip

/-- Sum each physical high-prime seat exactly ONCE, weighting it with
the complete genuine low cofactor.  The existing native owner selector
prohibits cloning or dropping the prime-only c=1 seat. -/
noncomputable def squareBlockLowCofactorBill (R : ℕ) : ℂ :=
  ∑ n ∈ canonicalSquareBlock R,
    if R < canonicalLargestPrimeFactor n then
      (((μ (canonicalCofactor n) : ℤ) : ℂ)) else 0

/-- The canonical smooth/transport architecture already has the
correct sign: its transport is exactly the signed LOW-cofactor bill
after prime-extension parity reversal. -/
theorem squareBlockTransportIncrement_eq_lowCofactorBill
    (R : ℕ) (hR : 2 ≤ R) :
    squareBlockTransportIncrement R = squareBlockLowCofactorBill R := by
  classical
  unfold squareBlockTransportIncrement squareBlockLowCofactorBill
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hhigh : R < canonicalLargestPrimeFactor n
  · simp only [hhigh, ite_true]
    have hsign := squareBlock_highPrimeOwnerSign hR hn hhigh
    simp [canonicalMoebiusWeight, hsign]
  · simp [hhigh]

/-- Physical square-block increment = genuine smooth sites minus
the complete original-coefficient, low-cofactor extension bill.
The arithmetic size of its cumulative sum is *not* estimated here. -/
theorem squareBlockIncrement_eq_smooth_sub_lowCofactorBill
    (R : ℕ) (hR : 2 ≤ R) :
    canonicalTotalIncrement R =
      squareBlockSmoothIncrement R - squareBlockLowCofactorBill R := by
  rw [canonicalTotalIncrement_eq_smooth_sub_transport,
      squareBlockTransportIncrement_eq_lowCofactorBill R hR]

/-! ## Exact density-versus-covariance accounting -/

/-- Number of positive Möbius sites, as a real-valued exact count. -/
def positiveMoebiusPopulation (x : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (x + 1), if (μ n : ℤ) = 1 then 1 else 0

/-- Number of negative Möbius sites, as a real-valued exact count. -/
def negativeMoebiusPopulation (x : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (x + 1), if (μ n : ℤ) = -1 then 1 else 0

private theorem moebiusStep_eq_positive_sub_negative (n : ℕ) :
    realMoebiusStep n =
      (if (μ n : ℤ) = 1 then (1 : ℝ) else 0) -
      (if (μ n : ℤ) = -1 then (1 : ℝ) else 0) := by
  rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;>
    simp [realMoebiusStep, h]

private theorem moebiusStep_sq_eq_positive_add_negative (n : ℕ) :
    realMoebiusStep n ^ 2 =
      (if (μ n : ℤ) = 1 then (1 : ℝ) else 0) +
      (if (μ n : ℤ) = -1 then (1 : ℝ) else 0) := by
  rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;>
    simp [realMoebiusStep, h]

theorem mertensLength_eq_populationDifference (x : ℕ) :
    realMertensLength (x + 1) =
      positiveMoebiusPopulation x - negativeMoebiusPopulation x := by
  unfold realMertensLength positiveMoebiusPopulation negativeMoebiusPopulation
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  exact moebiusStep_eq_positive_sub_negative n

theorem mertensDiagonal_eq_populationTotal (x : ℕ) :
    realMertensDiagonal (x + 1) =
      positiveMoebiusPopulation x + negativeMoebiusPopulation x := by
  unfold realMertensDiagonal positiveMoebiusPopulation negativeMoebiusPopulation
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  exact moebiusStep_sq_eq_positive_add_negative n

/-- Exact zero-target equation in density coordinates:
(A-B)^2 = (A+B) + 2 C. -/
theorem populationDifference_sq_eq_total_add_two_covariance (x : ℕ) :
    (positiveMoebiusPopulation x - negativeMoebiusPopulation x) ^ 2 =
      positiveMoebiusPopulation x + negativeMoebiusPopulation x +
        2 * realMertensPositiveLagPairSum (x + 1) := by
  calc
    (positiveMoebiusPopulation x - negativeMoebiusPopulation x) ^ 2 =
        realMertensLength (x + 1) ^ 2 := by
          rw [mertensLength_eq_populationDifference]
    _ = realMertensDiagonal (x + 1) +
        2 * realMertensPositiveLagPairSum (x + 1) :=
          realMertensLength_sq_eq_diagonal_add_two_mul_positiveLagPairSum (x + 1)
    _ = positiveMoebiusPopulation x + negativeMoebiusPopulation x +
        2 * realMertensPositiveLagPairSum (x + 1) := by
          rw [mertensDiagonal_eq_populationTotal]

/-- Positive *total* covariance is equivalent to squared sign imbalance
exceeding the number of nonzero Möbius sites.  Equal limiting densities
alone supply no such pointwise square-root estimate. -/
theorem positiveCovariance_iff_squarefreePopulationExceeded (x : ℕ) :
    0 < realMertensPositiveLagPairSum (x + 1) ↔
      positiveMoebiusPopulation x + negativeMoebiusPopulation x <
        (positiveMoebiusPopulation x - negativeMoebiusPopulation x) ^ 2 := by
  have h := populationDifference_sq_eq_total_add_two_covariance x
  constructor <;> intro hsign <;> nlinarith

/-- For an arbitrary nonnegative or negative ceiling T, the exact
signed-covariance ceiling is equivalent to the Mertens square ceiling.
This is a change of coordinates, *not* an independent arithmetic bound. -/
theorem covariance_ceiling_iff_mertens_square_ceiling (x : ℕ) (T : ℝ) :
    realMertensPositiveLagPairSum (x + 1) ≤
      (T - realMertensDiagonal (x + 1)) / 2 ↔
    ‖mertensSummatory x‖ ^ 2 ≤ T := by
  have h := norm_mertensSummatory_sq_eq_realMertensLength_sq x
  have hs := realMertensLength_sq_eq_diagonal_add_two_mul_positiveLagPairSum
    (x + 1)
  constructor <;> intro hb <;> nlinarith

/-! ## Complete factor-depth / shared-prime-ancestry partition -/

/-- The genuine physical, unordered, nonzero Möbius pair carrier.
The unit n=1 is present, with prime-factor depth zero. -/
def physicalSquarefreePairs (x : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 x).product (Finset.Icc 1 x)).filter fun mn =>
    mn.1 < mn.2 ∧ (μ mn.1 : ℤ) ≠ 0 ∧ (μ mn.2 : ℤ) ≠ 0

/-- The tensor label is (depth(m),depth(n),depth(gcd(m,n))). -/
def ancestryLabel (mn : ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (mn.1.primeFactors.card,
   mn.2.primeFactors.card,
   (Nat.gcd mn.1 mn.2).primeFactors.card)

def ancestryLabels (x : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (physicalSquarefreePairs x).image ancestryLabel

/-- Exact, nonnegative ancestry-cell population, including all depths. -/
def ancestryCellCount (x : ℕ) (v : ℕ × ℕ × ℕ) : ℕ :=
  ((physicalSquarefreePairs x).filter fun mn => ancestryLabel mn = v).card

/-- The sign of a nonzero Möbius pair in one ancestry cell depends on
the parity of the TWO complete factor depths, not solely shared depth. -/
theorem ancestryCell_signedMass (x : ℕ) (v : ℕ × ℕ × ℕ) :
    (∑ mn ∈ (physicalSquarefreePairs x).filter (fun mn => ancestryLabel mn = v),
      (μ mn.1 : ℤ) * (μ mn.2 : ℤ)) =
        (-1 : ℤ) ^ (v.1 + v.2.1) * (ancestryCellCount x v : ℤ) := by
  classical
  have hpoint : ∀ mn ∈ (physicalSquarefreePairs x).filter
      (fun mn => ancestryLabel mn = v),
      (μ mn.1 : ℤ) * (μ mn.2 : ℤ) =
        (-1 : ℤ) ^ (v.1 + v.2.1) := by
    intro mn hmn
    obtain ⟨hpair, hlabel⟩ := Finset.mem_filter.mp hmn
    obtain ⟨_hlt, hmuA, hmuB⟩ :=
      (Finset.mem_filter.mp hpair).2
    have ha : Squarefree mn.1 :=
      ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmuA
    have hb : Squarefree mn.2 :=
      ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmuB
    have hka : mn.1.primeFactors.card = v.1 := by
      simpa [ancestryLabel] using!
        congrArg (fun t : ℕ × ℕ × ℕ => t.1) hlabel
    have hkb : mn.2.primeFactors.card = v.2.1 := by
      simpa [ancestryLabel] using!
        congrArg (fun t : ℕ × ℕ × ℕ => t.2.1) hlabel
    rw [moebius_eq_negOnePow_primeFactors_card ha,
        moebius_eq_negOnePow_primeFactors_card hb,
        ← pow_add, hka, hkb]
  calc
    (∑ mn ∈ (physicalSquarefreePairs x).filter (fun mn => ancestryLabel mn = v),
       (μ mn.1 : ℤ) * (μ mn.2 : ℤ)) =
      ∑ mn ∈ (physicalSquarefreePairs x).filter (fun mn => ancestryLabel mn = v),
        (-1 : ℤ) ^ (v.1 + v.2.1) := by
          apply Finset.sum_congr rfl
          exact hpoint
    _ = (-1 : ℤ) ^ (v.1 + v.2.1) * (ancestryCellCount x v : ℤ) := by
          simp [ancestryCellCount, Finset.sum_const, mul_comm]

/-- Complete A_(k,l,j) tensor reassembles the *original signed pair sum*.
All finite factor depths and all shared-prime depths are retained.
This identity does not furnish an all-scale cancellation estimate. -/
theorem physicalPairSum_eq_completeAncestryTensor (x : ℕ) :
    (∑ mn ∈ physicalSquarefreePairs x,
        (μ mn.1 : ℤ) * (μ mn.2 : ℤ)) =
      ∑ v ∈ ancestryLabels x,
        (-1 : ℤ) ^ (v.1 + v.2.1) * (ancestryCellCount x v : ℤ) := by
  classical
  have hmaps : ∀ mn ∈ physicalSquarefreePairs x,
      ancestryLabel mn ∈ ancestryLabels x := by
    intro mn hmn
    exact Finset.mem_image_of_mem ancestryLabel hmn
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := physicalSquarefreePairs x) (t := ancestryLabels x)
    (g := ancestryLabel) hmaps
    (fun mn : ℕ × ℕ => (μ mn.1 : ℤ) * (μ mn.2 : ℤ))
  calc
    (∑ mn ∈ physicalSquarefreePairs x,
        (μ mn.1 : ℤ) * (μ mn.2 : ℤ)) =
      ∑ v ∈ ancestryLabels x,
        ∑ mn ∈ physicalSquarefreePairs x with ancestryLabel mn = v,
          (μ mn.1 : ℤ) * (μ mn.2 : ℤ) := hfiber.symm
    _ = ∑ v ∈ ancestryLabels x,
        (-1 : ℤ) ^ (v.1 + v.2.1) * (ancestryCellCount x v : ℤ) := by
          apply Finset.sum_congr rfl
          intro v _
          exact ancestryCell_signedMass x v

/-! ## Explicit connection to the already-compiled square-block splitting -/

theorem fixedWheelBlock_increment_eq_smooth_sub_transport (R : ℕ) :
    canonicalTotalIncrement R =
      squareBlockSmoothIncrement R - squareBlockTransportIncrement R :=
  canonicalTotalIncrement_eq_smooth_sub_transport R

theorem fixedWheelBlock_cumulative_eq_mertens (R : ℕ) :
    squareBlockSmoothPrefix R - squareBlockTransportPrefix R =
      RHLean.Analysis.squarePrefixMertens R :=
  squareBlockSmoothTransportResidual_eq_squarePrefixMertens R

end RHLean.Proof

#print axioms RHLean.Proof.squareBlock_prime_iff_lowWheel
#print axioms RHLean.Proof.squareBlock_atMostOneHighPrime
#print axioms RHLean.Proof.squareBlock_highPrimeCofactor_le
#print axioms RHLean.Proof.highPrimeCofactor_sign_reversal
#print axioms RHLean.Proof.squareBlock_highPrimeOwnerSign
#print axioms RHLean.Proof.squareBlockTransportIncrement_eq_lowCofactorBill
#print axioms RHLean.Proof.squareBlockIncrement_eq_smooth_sub_lowCofactorBill
#print axioms RHLean.Proof.populationDifference_sq_eq_total_add_two_covariance
#print axioms RHLean.Proof.positiveCovariance_iff_squarefreePopulationExceeded
#print axioms RHLean.Proof.covariance_ceiling_iff_mertens_square_ceiling
#print axioms RHLean.Proof.ancestryCell_signedMass
#print axioms RHLean.Proof.physicalPairSum_eq_completeAncestryTensor
