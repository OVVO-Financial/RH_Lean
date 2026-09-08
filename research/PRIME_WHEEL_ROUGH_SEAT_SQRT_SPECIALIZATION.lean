import RHLean.Proof.PrimeWheelRoughSeatCorrelation
import RHLean.Proof.LowWheelHighPrimeSurvivor
import RHLean.Arithmetic.MobiusFiniteDifferenceIdentification

/-!
# Square-root specialization of the signed rough-seat correlation

When the wheel contains every prime through `R` and the physical endpoint is
`X_R = R^2 - 1`, every rough seat above `R` is a prime.  Moreover every
reciprocal cutoff `X_R / q` attached to such a prime is below `R`, so the
truncated divisor kernel is exactly the ordinary lower Mertens prefix there.

This turns the generic rough-seat identity into the exact high-prime transport
formula

`M(X_R) = K_R(X_R) - sum_{R < q <= X_R, q prime} M(floor(X_R/q))`.

No norm or estimate is used.  This is the literal bridge from the finite-wheel
kernel coordinate to the repository's low/high square-root transport.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

/-- Coprimality to a prime-set primorial is exactly avoidance of every selected
prime coordinate. -/
theorem coprime_primorial_iff_avoid_selected_primes
    (S : Finset ℕ) (n : ℕ) (hprime : ∀ p ∈ S, Nat.Prime p) :
    Nat.Coprime n (RHLean.Arithmetic.primorial S) ↔
      ∀ p ∈ S, ¬ p ∣ n := by
  classical
  revert hprime
  induction S using Finset.induction_on with
  | empty =>
      intro _hprime
      simp [RHLean.Arithmetic.primorial]
  | @insert p S hpS ih =>
      intro hprime
      have hp : p.Prime := hprime p (Finset.mem_insert_self p S)
      have hS : ∀ q ∈ S, q.Prime := fun q hq =>
        hprime q (Finset.mem_insert_of_mem hq)
      rw [primorial_insert S p hpS, Nat.coprime_mul_iff_right, ih hS]
      have hcop : Nat.Coprime n p ↔ ¬ p ∣ n := by
        rw [Nat.coprime_comm]
        exact hp.coprime_iff_not_dvd
      rw [hcop]
      simp [hpS]

/-- The coprimality predicate used by `roughWheelInterval` is exactly the
low-wheel survivor predicate when the selected set is `primesUpTo R`. -/
theorem coprime_primorial_primesUpTo_iff_lowWheelHighSurvivor
    (R n : ℕ) :
    Nat.Coprime n (RHLean.Arithmetic.primorial (primesUpTo R)) ↔
      lowWheelHighSurvivor R n := by
  unfold lowWheelHighSurvivor
  exact coprime_primorial_iff_avoid_selected_primes
    (primesUpTo R) n (fun p hp => prime_of_mem_primesUpTo hp)

/-- Positive-support indicator used to read the truncated kernel as the
canonical divisor finite-difference operator. -/
def primeWheelPositiveIndicator (y : ℕ) : ℤ :=
  if y = 0 then 0 else 1

/-- The truncated divisor kernel is the canonical finite-difference operator
applied to the positive-support indicator. -/
theorem primeWheelTruncatedMoebiusKernel_eq_finiteDifferenceOperator_indicator
    (S : Finset ℕ) (X : ℕ) :
    primeWheelTruncatedMoebiusKernel S X =
      finiteDifferenceOperator S primeWheelPositiveIndicator X := by
  classical
  unfold primeWheelTruncatedMoebiusKernel finiteDifferenceOperator
  apply Finset.sum_congr rfl
  intro d hd
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  by_cases hdX : d ≤ X
  · have hq1 : 1 ≤ X / d := (Nat.one_le_div_iff hdpos).2 hdX
    have hq0 : X / d ≠ 0 := by omega
    simp [shift, primeWheelPositiveIndicator, hdX, hq0]
  · have hXd : X < d := Nat.lt_of_not_ge hdX
    have hq0 : X / d = 0 := Nat.div_eq_of_lt hXd
    simp [shift, primeWheelPositiveIndicator, hdX, hq0]

/-- Once the selected prime set contains every prime through `X`, the truncated
wheel kernel is exactly the ordinary positive Möbius prefix through `X`. -/
theorem primeWheelTruncatedMoebiusKernel_eq_moebius_Icc_of_cover
    (S : Finset ℕ) (X : ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hcover : primesUpTo X ⊆ S) :
    primeWheelTruncatedMoebiusKernel S X =
      ∑ n ∈ Finset.Icc 1 X, (μ n : ℤ) := by
  rw [primeWheelTruncatedMoebiusKernel_eq_finiteDifferenceOperator_indicator]
  have hident :=
    sum_Icc_moebius_mul_eq_finiteDifferenceOperator_of_primesUpTo_subset
      S primeWheelPositiveIndicator X hprime hcover (by
        simp [primeWheelPositiveIndicator])
  rw [← hident]
  apply Finset.sum_congr rfl
  intro n hn
  rcases Finset.mem_Icc.mp hn with ⟨hn1, hnX⟩
  have hnpos : 0 < n := by omega
  have hq1 : 1 ≤ X / n := (Nat.one_le_div_iff hnpos).2 hnX
  have hq0 : X / n ≠ 0 := by omega
  simp [primeWheelPositiveIndicator, hq0]

/-- The standard rough-Mertens prefix agrees with the positive Möbius `Icc`
prefix because the zero term vanishes. -/
theorem roughMertens_one_eq_moebius_Icc (X : ℕ) :
    roughMertens 1 X = ∑ n ∈ Finset.Icc 1 X, (μ n : ℤ) := by
  unfold roughMertens
  have hset : Finset.range (X + 1) = insert 0 (Finset.Icc 1 X) := by
    ext n
    simp
    omega
  rw [hset]
  simp [roughMoebius]

/-- Below a larger saturated wheel cutoff, the kernel is literally the lower
Mertens prefix. -/
theorem primeWheelTruncatedMoebiusKernel_primesUpTo_eq_roughMertens
    (R X : ℕ) (hXR : X ≤ R) :
    primeWheelTruncatedMoebiusKernel (primesUpTo R) X = roughMertens 1 X := by
  rw [primeWheelTruncatedMoebiusKernel_eq_moebius_Icc_of_cover]
  · exact (roughMertens_one_eq_moebius_Icc X).symm
  · intro p hp
    exact prime_of_mem_primesUpTo hp
  · intro p hp
    rcases mem_primesUpTo.mp hp with ⟨hpPrime, hpX⟩
    exact mem_primesUpTo.mpr ⟨hpPrime, hpX.trans hXR⟩

/-- At the complete square endpoint, the rough carrier for the full low wheel
consists of `1` together with exactly the primes strictly above the root. -/
theorem roughWheelInterval_primesUpTo_squareRootEndpoint_eq_one_union_highPrimes
    (R : ℕ) (hR : 2 ≤ R) :
    roughWheelInterval (RHLean.Arithmetic.primorial (primesUpTo R))
        0 (squareRootEndpoint R) =
      ({1} : Finset ℕ) ∪
        (Finset.Ioc R (squareRootEndpoint R)).filter Nat.Prime := by
  classical
  ext n
  simp only [roughWheelInterval, Finset.mem_filter, Finset.mem_Ioc,
    Finset.mem_union, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hn0, hnX⟩, hcop⟩
    have hsurv : lowWheelHighSurvivor R n :=
      (coprime_primorial_primesUpTo_iff_lowWheelHighSurvivor R n).mp hcop
    by_cases hnR : n ≤ R
    · by_cases hn1 : n = 1
      · exact Or.inl hn1
      · have hnpos : 0 < n := by omega
        have hnOne : n ≠ 1 := hn1
        let p := n.minFac
        have hpPrime : p.Prime := by
          simpa [p] using Nat.minFac_prime hnOne
        have hpDvd : p ∣ n := by
          simpa [p] using Nat.minFac_dvd n
        have hpLeN : p ≤ n := Nat.le_of_dvd hnpos hpDvd
        have hpMem : p ∈ primesUpTo R :=
          mem_primesUpTo.mpr ⟨hpPrime, hpLeN.trans hnR⟩
        exact (hsurv p hpMem hpDvd).elim
    · have hRn : R < n := Nat.lt_of_not_ge hnR
      have hnPrime : n.Prime :=
        (lowWheelHighSurvivor_iff_prime hR hRn hnX).mp hsurv
      exact Or.inr ⟨⟨hRn, hnX⟩, hnPrime⟩
  · intro h
    rcases h with rfl | hn
    · simp [coprime_primorial_primesUpTo_iff_lowWheelHighSurvivor,
        lowWheelHighSurvivor]
    · rcases hn with ⟨hnI, hnPrime⟩
      rcases Finset.mem_Ioc.mp hnI with ⟨hRn, hnX⟩
      have hsurv : lowWheelHighSurvivor R n :=
        (lowWheelHighSurvivor_iff_prime hR hRn hnX).mpr hnPrime
      exact ⟨⟨by omega, hnX⟩,
        (coprime_primorial_primesUpTo_iff_lowWheelHighSurvivor R n).mpr hsurv⟩

/-- A high prime at the square endpoint sees a reciprocal cutoff strictly below
the root. -/
theorem squareRootEndpoint_div_lt_root_of_root_lt
    {R q : ℕ} (hR : 2 ≤ R) (hRq : R < q) :
    squareRootEndpoint R / q < R := by
  have hqpos : 0 < q := by omega
  apply (Nat.div_lt_iff_lt_mul hqpos).2
  unfold squareRootEndpoint
  nlinarith

/-- **Square-root rough-seat transport identity.**  The entire high-prime
family is a signed sum of *lower Mertens states*, while the remaining low-wheel
term stays as one intact truncated kernel.  Every high prime contributes with
the exact Möbius flip `-M(floor(X_R/q))`. -/
theorem roughMertens_squareRootEndpoint_eq_lowKernel_add_neg_highPrimeLowerMertens
    (R : ℕ) (hR : 2 ≤ R) :
    roughMertens 1 (squareRootEndpoint R) =
      primeWheelTruncatedMoebiusKernel (primesUpTo R) (squareRootEndpoint R) +
        ∑ q ∈ (Finset.Ioc R (squareRootEndpoint R)).filter Nat.Prime,
          -roughMertens 1 (squareRootEndpoint R / q) := by
  let S := primesUpTo R
  have hprime : ∀ p ∈ S, p.Prime := by
    intro p hp
    exact prime_of_mem_primesUpTo hp
  have hfull :=
    roughMertens_one_eq_primeWheel_fullRoughSeatCorrelation
      S hprime (squareRootEndpoint R)
  rw [roughWheelInterval_primesUpTo_squareRootEndpoint_eq_one_union_highPrimes
      R hR] at hfull
  have hdisj :
      Disjoint ({1} : Finset ℕ)
        ((Finset.Ioc R (squareRootEndpoint R)).filter Nat.Prime) := by
    rw [Finset.disjoint_left]
    intro n hn1 hnHigh
    have hnEq : n = 1 := by simpa using hn1
    subst n
    have hI := (Finset.mem_filter.mp hnHigh).1
    have hR1 := (Finset.mem_Ioc.mp hI).1
    omega
  rw [Finset.sum_union hdisj, Finset.sum_singleton] at hfull
  simp only [Nat.div_one, ArithmeticFunction.moebius_apply_one, Int.ofNat_one,
    one_mul] at hfull
  rw [hfull]
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  rcases Finset.mem_filter.mp hq with ⟨hqI, hqPrime⟩
  have hRq : R < q := (Finset.mem_Ioc.mp hqI).1
  have hcut : squareRootEndpoint R / q ≤ R :=
    Nat.le_of_lt (squareRootEndpoint_div_lt_root_of_root_lt hR hRq)
  have hk :=
    primeWheelTruncatedMoebiusKernel_primesUpTo_eq_roughMertens
      R (squareRootEndpoint R / q) hcut
  unfold roughMoebius
  have hcop : Nat.Coprime q (RHLean.Arithmetic.primorial (primesUpTo R)) :=
    (coprime_primorial_primesUpTo_iff_lowWheelHighSurvivor R q).mpr
      ((lowWheelHighSurvivor_iff_prime hR hRq (Finset.mem_Ioc.mp hqI).2).mpr hqPrime)
  rw [if_pos hcop, ArithmeticFunction.moebius_apply_prime hqPrime, hk]
  ring

/-- Subtraction form of the same identity. -/
theorem roughMertens_squareRootEndpoint_eq_lowKernel_sub_highPrimeLowerMertens
    (R : ℕ) (hR : 2 ≤ R) :
    roughMertens 1 (squareRootEndpoint R) =
      primeWheelTruncatedMoebiusKernel (primesUpTo R) (squareRootEndpoint R) -
        ∑ q ∈ (Finset.Ioc R (squareRootEndpoint R)).filter Nat.Prime,
          roughMertens 1 (squareRootEndpoint R / q) := by
  rw [roughMertens_squareRootEndpoint_eq_lowKernel_add_neg_highPrimeLowerMertens R hR]
  rw [← Finset.sum_neg_distrib]
  ring

end RHLean.Proof
