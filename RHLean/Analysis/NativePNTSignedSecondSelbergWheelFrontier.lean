import Mathlib
import RHLean.Analysis.NativePNTSignedSecondSelberg
import RHLean.Arithmetic.PrimeWheelPartialErrorThreshold

/-!
# Signed second Selberg kernel on the square-root wheel frontier

The exact signed second-Selberg recurrence from `NativePNTSignedSecondSelberg`
uses the coefficient

`K₂(n) = (Lambda * Lambda)(n) - Lambda(n) log n`.

This file evaluates that exact coefficient on the arithmetic frontier already
classified by `PrimeWheelPartialErrorThreshold`: below `upper < 2*y^2`, every
nonzero partial-wheel error is either a square of one prime above the cutoff or
a product of two distinct primes above the cutoff.

The square face is the negative diagonal `-log(p)^2`; the distinct two-prime
face is the positive mixed term `2 log(p) log(q)`.  Thus the true signed second
kernel is a second-order prime-wheel face operator on the exact unresolved
frontier, rather than a positive scalar `Lambda_2` mass.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

/-- Exact value of `Lambda_2` on a prime square. -/
theorem nativeLambdaTwo_prime_sq
    (p : ℕ) (hp : p.Prime) :
    nativeLambdaTwo (p ^ 2) = 3 * (Real.log (p : ℝ)) ^ 2 := by
  rw [← nativeMobiusLogSquareDivisorFiber_eq_lambdaTwo]
  unfold nativeMobiusLogSquareDivisorFiber
  rw [Nat.divisors_prime_pow hp 2]
  simp [ArithmeticFunction.moebius_apply_prime hp, Real.log_pow, hp.ne_zero]
  ring

/-- The signed second-Selberg kernel is negative on the one-prime square face. -/
theorem nativePNTSignedSecondSelbergKernel_prime_sq
    (p : ℕ) (hp : p.Prime) :
    nativePNTSignedSecondSelbergKernel (p ^ 2) =
      -(Real.log (p : ℝ)) ^ 2 := by
  rw [nativePNTSignedSecondSelbergKernel_eq_lambdaTwo_sub_two_log,
    nativeLambdaTwo_prime_sq p hp]
  have hlam : Λ (p ^ 2) = Real.log (p : ℝ) := by
    simpa using ArithmeticFunction.vonMangoldt_apply_pow hp (by norm_num : (2 : ℕ) ≠ 0)
  rw [hlam, Nat.cast_pow, Real.log_pow]
  norm_num
  ring

/-- Exact value of `Lambda_2` on a product of two distinct primes. -/
theorem nativeLambdaTwo_mul_distinct_primes
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    nativeLambdaTwo (p * q) =
      2 * Real.log (p : ℝ) * Real.log (q : ℝ) := by
  have hcop : Nat.Coprime p q := by
    rw [hp.coprime_iff_not_dvd]
    intro hpqDvd
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp hpqDvd)
  rw [← nativeMobiusLogSquareDivisorFiber_eq_lambdaTwo]
  unfold nativeMobiusLogSquareDivisorFiber
  rw [Nat.Coprime.divisors_mul hcop]
  simp [hp.divisors, hq.divisors, ArithmeticFunction.moebius_apply_prime,
    hp, hq, Real.log_mul, hp.ne_zero, hq.ne_zero]
  ring

/-- The signed kernel is the positive mixed face on two distinct primes. -/
theorem nativePNTSignedSecondSelbergKernel_mul_distinct_primes
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    nativePNTSignedSecondSelbergKernel (p * q) =
      2 * Real.log (p : ℝ) * Real.log (q : ℝ) := by
  rw [nativePNTSignedSecondSelbergKernel_eq_lambdaTwo_sub_two_log,
    nativeLambdaTwo_mul_distinct_primes p q hp hq hpq]
  have hnotPow : ¬ IsPrimePow (p * q) := by
    intro hpow
    rcases hpow with ⟨r, hr, k, hk, hEq⟩
    have hpDvd : p ∣ r ^ k := by
      rw [← hEq]
      exact dvd_mul_right p q
    have hqDvd : q ∣ r ^ k := by
      rw [← hEq]
      exact dvd_mul_left q p
    have hpr : p = r := by
      have hprDvd : p ∣ r := (hp.dvd_pow).mp hpDvd
      exact (Nat.prime_dvd_prime_iff_eq hp hr).mp hprDvd
    have hqr : q = r := by
      have hqrDvd : q ∣ r := (hq.dvd_pow).mp hqDvd
      exact (Nat.prime_dvd_prime_iff_eq hq hr).mp hqrDvd
    exact hpq (hpr.trans hqr.symm)
  have hlam : Λ (p * q) = 0 := by
    rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]
    exact Or.inr hnotPow
  rw [hlam]
  ring

/-- **Exact square-root wheel-frontier classification of the true signed second
Selberg kernel.**  The only nonzero partial-wheel errors are the negative
one-prime diagonal or the positive two-prime mixed face. -/
theorem nativePNTSignedSecondSelbergKernel_wheelFrontier_classification
    (y upper : ℕ) {n : ℕ}
    (hscale : upper < 2 * y ^ 2)
    (hnpos : 0 < n) (hnupper : n ≤ upper)
    (herr : μ n - partialPrimeWheelSite y upper n ≠ 0) :
    (∃ q : ℕ,
      q.Prime ∧ y < q ∧ n = q ^ 2 ∧
        μ n - partialPrimeWheelSite y upper n = 1 ∧
        nativePNTSignedSecondSelbergKernel n =
          -(Real.log (q : ℝ)) ^ 2) ∨
    (∃ q r : ℕ,
      q.Prime ∧ r.Prime ∧ q ≠ r ∧ y < q ∧ y < r ∧ n = q * r ∧
        μ n - partialPrimeWheelSite y upper n = 2 ∧
        nativePNTSignedSecondSelbergKernel n =
          2 * Real.log (q : ℝ) * Real.log (r : ℝ)) := by
  rcases partialPrimeWheel_nonzero_error_classification_of_two_mul_sq
      y upper hscale hnpos hnupper herr with hsquare | hpair
  · rcases hsquare with ⟨q, hq, hyq, hn, herrval⟩
    left
    refine ⟨q, hq, hyq, hn, herrval, ?_⟩
    rw [hn]
    exact nativePNTSignedSecondSelbergKernel_prime_sq q hq
  · rcases hpair with ⟨q, r, hq, hr, hqr, hyq, hyr, hn, herrval⟩
    right
    refine ⟨q, r, hq, hr, hqr, hyq, hyr, hn, herrval, ?_⟩
    rw [hn]
    exact nativePNTSignedSecondSelbergKernel_mul_distinct_primes q r hq hr hqr

end RHLean.Analysis
