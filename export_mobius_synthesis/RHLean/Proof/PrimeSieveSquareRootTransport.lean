import Mathlib
import RHLean.Arithmetic.PrimeWheelMobiusRecovery
import RHLean.Arithmetic.PrimesUpToFrontier
import RHLean.Analysis.SquareRootTransportRealization

/-!
# Elementary prime-sieve realization of square-root transport

This module reconnects the square-root smooth/transport decomposition to the
prime-by-prime sign-flip mechanism from which the Mobius parity originates.

The existing prime-wheel field `seededPrimeComb S n` starts from the provisional
seed `-1`.  Negating it gives the all-plus process: start every positive site at
`+1`, then for each processed prime flip first-power multiples and kill square
multiples.  Once the processed prime set covers the square root of the ambient
cutoff, every unresolved squarefree source has exactly one unprocessed prime
factor.  Its current all-plus sign is therefore the negative of its final Mobius
sign.

At the complete square endpoint `R^2 - 1`, this elementary unresolved mass is
exactly the repository's original square-root transport term.  Thus the two
states are

```text
before the remaining large-prime flips:  A_R + T_R
after all prime flips:                  A_R - T_R = M(R^2-1).
```

No analytic estimate is used or claimed.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

/-- All-plus prime-comb state.  The special value at zero is set to zero so
prefix sums agree literally with the usual Mertens convention `mu(0)=0`. -/
def allPlusPrimeCombSite (S : Finset ℕ) (n : ℕ) : ℤ :=
  if n = 0 then 0 else -seededPrimeComb S n

/-- Sum of the all-plus prime-comb state over a complete square prefix after all
primes at most `R` have acted. -/
def allPlusSquareRootPrimeCombMass (R : ℕ) : ℂ :=
  ∑ m ∈ cumulativeSquarePrefixSet (R - 1),
    (((allPlusPrimeCombSite (primesUpTo R) m : ℤ) : ℂ))

/-- `primesUpTo y` covers every prime coordinate through `sqrt upper` whenever
that square-root cutoff is at most `y`. -/
theorem primesUpTo_sqrtCoverage
    {y upper : ℕ} (hsqrt : Nat.sqrt upper ≤ y) :
    PrimeWheelSqrtCoverage (primesUpTo y) upper := by
  intro p hp hple
  exact mem_primesUpTo.mpr ⟨hp, hple.trans hsqrt⟩

/-- Pointwise meaning of the all-plus process after square-root coverage: smooth
squarefree sources already have their final Mobius sign, while a squarefree
source with one unresolved large prime has the opposite sign.  Nonsquarefree
sources are zero on both sides. -/
theorem allPlusPrimeCombSite_eq_moebius_or_neg
    (S : Finset ℕ) {upper n : ℕ}
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hcover : PrimeWheelSqrtCoverage S upper)
    (hnpos : 0 < n) (hnupper : n ≤ upper) :
    allPlusPrimeCombSite S n =
      if IsPrimeWheelSmooth S n then μ n else -μ n := by
  classical
  by_cases hsq : Squarefree n
  · by_cases hsmooth : IsPrimeWheelSmooth S n
    · have hseed := seededPrimeComb_eq_neg_moebius_of_smooth S hprime hsmooth
      simp [allPlusPrimeCombSite, Nat.ne_of_gt hnpos, hsmooth, hseed]
    · have hseed := seededPrimeComb_eq_moebius_of_not_smooth
        S hprime hcover hsq hnupper hsmooth
      simp [allPlusPrimeCombSite, Nat.ne_of_gt hnpos, hsmooth, hseed]
  · have hseed := seededPrimeComb_eq_zero_of_not_squarefree
      S hcover hnpos hnupper hsq
    have hmu := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
    have hsmooth : ¬ IsPrimeWheelSmooth S n := by
      intro h
      exact hsq h.1
    simp [allPlusPrimeCombSite, Nat.ne_of_gt hnpos, hsmooth, hseed, hmu]

private theorem primeFactor_le_canonicalLargestPrimeFactor
    {n p : ℕ} (hn : 1 < n) (hp : p ∈ n.primeFactors) :
    p ≤ canonicalLargestPrimeFactor n := by
  unfold canonicalLargestPrimeFactor
  rw [dif_pos hn]
  exact Finset.le_max' n.primeFactors p hp

private theorem canonicalLargestPrimeFactor_mem_primeFactors
    {n : ℕ} (hn : 1 < n) :
    canonicalLargestPrimeFactor n ∈ n.primeFactors := by
  unfold canonicalLargestPrimeFactor
  rw [dif_pos hn]
  exact Finset.max'_mem n.primeFactors (Nat.nonempty_primeFactors.mpr hn)

/-- For a positive squarefree source and a nontrivial cutoff, smoothness with
respect to every prime at most `R` is exactly the condition that its canonical
largest prime factor is at most `R`. -/
theorem isPrimeWheelSmooth_primesUpTo_iff_largestPrime_le
    {R n : ℕ} (hR : 1 ≤ R) (hnpos : 0 < n) (hsq : Squarefree n) :
    IsPrimeWheelSmooth (primesUpTo R) n ↔
      canonicalLargestPrimeFactor n ≤ R := by
  by_cases hn1 : n = 1
  · subst n
    simp [IsPrimeWheelSmooth, canonicalLargestPrimeFactor, hR]
  · have hn : 1 < n := by omega
    constructor
    · intro hsmooth
      have hqmem := canonicalLargestPrimeFactor_mem_primeFactors hn
      exact (mem_primesUpTo.mp (hsmooth.2 _ hqmem)).2
    · intro hq
      refine ⟨hsq, ?_⟩
      intro p hp
      have hpPrime := (Nat.mem_primeFactors.mp hp).1
      have hpq := primeFactor_le_canonicalLargestPrimeFactor hn hp
      exact mem_primesUpTo.mpr ⟨hpPrime, hpq.trans hq⟩

private theorem squareRootEndpoint_sqrt_lt
    {R : ℕ} (hR : 1 ≤ R) :
    Nat.sqrt (squareRootEndpoint R) < R := by
  apply (Nat.sqrt_lt').2
  unfold squareRootEndpoint
  have hpos : 0 < R ^ 2 := by positivity
  omega

/-- Before the primes above `R` have acted, the complete square-prefix all-plus
state is exactly `smooth + transport`.  This is the elementary counterpart of
the already-proved final identity `M = smooth - transport`. -/
theorem allPlusSquareRootPrimeCombMass_eq_smooth_add_transport
    (R : ℕ) (hR : 2 ≤ R) :
    allPlusSquareRootPrimeCombMass R =
      squareRootSmoothMass (R - 1) + squareRootTransportMass (R - 1) := by
  classical
  have hR1 : 1 ≤ R := by omega
  have hpred : R - 1 + 1 = R := Nat.sub_add_cancel hR1
  have hsqrt : Nat.sqrt (squareRootEndpoint R) ≤ R :=
    (squareRootEndpoint_sqrt_lt hR1).le
  have hcover : PrimeWheelSqrtCoverage (primesUpTo R) (squareRootEndpoint R) :=
    primesUpTo_sqrtCoverage hsqrt
  have hprime : ∀ p ∈ primesUpTo R, Nat.Prime p := by
    intro p hp
    exact prime_of_mem_primesUpTo hp
  unfold allPlusSquareRootPrimeCombMass squareRootSmoothMass squareRootTransportMass
  rw [hpred, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hm0 : m = 0
  · subst m
    simp [allPlusPrimeCombSite, canonicalMoebiusWeight]
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
    have hmLt : m < R ^ 2 := by
      simpa [cumulativeSquarePrefixSet, hpred] using hm
    have hmUpper : m ≤ squareRootEndpoint R := by
      unfold squareRootEndpoint
      omega
    have hsite := allPlusPrimeCombSite_eq_moebius_or_neg
      (primesUpTo R) hprime hcover hmpos hmUpper
    by_cases hsq : Squarefree m
    · have hsmoothIff :=
        isPrimeWheelSmooth_primesUpTo_iff_largestPrime_le hR1 hmpos hsq
      by_cases hq : canonicalLargestPrimeFactor m ≤ R
      · have hsmooth : IsPrimeWheelSmooth (primesUpTo R) m := hsmoothIff.mpr hq
        rw [hsite]
        simp [hsmooth, hq, canonicalMoebiusWeight]
      · have hsmooth : ¬ IsPrimeWheelSmooth (primesUpTo R) m := by
          intro hs
          exact hq (hsmoothIff.mp hs)
        have hqgt : R < canonicalLargestPrimeFactor m := Nat.lt_of_not_ge hq
        rw [hsite]
        simp [hsmooth, hq, hqgt, canonicalMoebiusWeight]
    · have hmu := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
      have hsmooth : ¬ IsPrimeWheelSmooth (primesUpTo R) m := by
        intro hs
        exact hsq hs.1
      rw [hsite]
      simp [hsmooth, hmu, canonicalMoebiusWeight]

/-- Exact elementary gap identity at a complete square endpoint: the difference
between the state before and after the remaining large-prime flips is twice the
original square-root transport mass. -/
theorem allPlusSquareRootPrimeCombMass_sub_mertens_eq_two_transport
    (R : ℕ) (hR : 2 ≤ R) :
    allPlusSquareRootPrimeCombMass R -
        RHLean.Analysis.squarePrefixMertens (R - 1) =
      2 * squareRootTransportMass (R - 1) := by
  rw [allPlusSquareRootPrimeCombMass_eq_smooth_add_transport R hR]
  rw [squarePrefixMertens_eq_squareRootSmooth_sub_transport]
  ring

/-- The complementary half-sum is exactly the original smooth contribution.
This names the identification `A_R = (before + after)/2` without introducing
any division into the formal statement. -/
theorem allPlusSquareRootPrimeCombMass_add_mertens_eq_two_smooth
    (R : ℕ) (hR : 2 ≤ R) :
    allPlusSquareRootPrimeCombMass R +
        RHLean.Analysis.squarePrefixMertens (R - 1) =
      2 * squareRootSmoothMass (R - 1) := by
  rw [allPlusSquareRootPrimeCombMass_eq_smooth_add_transport R hR]
  rw [squarePrefixMertens_eq_squareRootSmooth_sub_transport]
  ring

/-- Prime-first form of the same gap.  The transport is literally the batch sum
of lower-scale Mertens values carried by the as-yet unprocessed primes `q > R`.
-/
theorem allPlusSquareRootPrimeCombMass_sub_mertens_eq_mertensPrimeTail
    (R : ℕ) (hR : 2 ≤ R) :
    allPlusSquareRootPrimeCombMass R -
        RHLean.Analysis.squarePrefixMertens (R - 1) =
      2 *
        (∑ q ∈ Finset.Ioc R (squareRootEndpoint R),
          if q.Prime then
            RHLean.Analysis.mertensSummatory (squareRootEndpoint R / q)
          else
            0) := by
  rw [allPlusSquareRootPrimeCombMass_sub_mertens_eq_two_transport R hR]
  rw [squareRootTransportMass_pred_eq_cofactorFirst R (by omega)]
  rw [squareRootTransportCofactorFirst_eq_primeFirst]
  rw [squareRootTransportPrimeFirst_eq_mertensTransform R (by omega)]

end RHLean.Proof
