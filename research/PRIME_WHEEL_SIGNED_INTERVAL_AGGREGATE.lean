import RHLean.Proof.PostRootCovarianceUnconditionalDecayScratch
import RHLean.Analysis.RamanujanDivisorBoundary

/-!
# Exact signed prime-wheel interval aggregate

Wheel depth is not used here as a counting parameter.  The full divisor cube is
kept signed on the exact rough-interval carrier.  Since the Mobius coefficients
of a nontrivial wheel sum to zero, the divisor-difference formula may be
recentered at the common physical anchor `B / W` without changing its value.
This is the quantity on which any further gain must come from cancellation
between signed bands rather than from counting them separately.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

/-- The signed divisor-cube interval aggregate at wheel `prod S`, recentered at
the common bottom anchor `B / prod S`.  No absolute values occur inside it. -/
def primeWheelSignedIntervalAggregate (S : Finset ℕ) (B : ℕ) : ℤ :=
  ∑ d ∈ (RHLean.Arithmetic.primorial S).divisors,
    (μ d : ℤ) *
      roughInterval (RHLean.Arithmetic.primorial S)
        (B / RHLean.Arithmetic.primorial S) (B / d)

/-- **Exact signed-band recovery of physical Mertens.**  For every nontrivial
finite prime wheel, the ordinary Mertens prefix is exactly the signed sum of
rough intervals from the common anchor `B / W` to the divisor-scaled endpoint
`B / d`.

This is just the already-compiled divisor finite-difference identity plus the
zero sum of Mobius coefficients over divisors of `W`; therefore no cancellation
has been discarded before this representation. -/
theorem roughMertens_one_eq_primeWheel_signedIntervalAggregate
    (S : Finset ℕ) (hprime : ∀ p ∈ S, Nat.Prime p)
    (hWne : RHLean.Arithmetic.primorial S ≠ 1) (B : ℕ) :
    roughMertens 1 B = primeWheelSignedIntervalAggregate S B := by
  have hmu :
      (∑ d ∈ (RHLean.Arithmetic.primorial S).divisors, (μ d : ℤ)) = 0 := by
    rw [RHLean.Analysis.sum_moebius_divisors_eq_one_or_zero]
    simp [hWne]
  rw [roughMertens_one_eq_primeWheel_divisorDifference S hprime B]
  unfold primeWheelSignedIntervalAggregate
  simp_rw [roughInterval, mul_sub]
  rw [Finset.sum_sub_distrib]
  have hanchor :
      (∑ d ∈ (RHLean.Arithmetic.primorial S).divisors,
        (μ d : ℤ) *
          roughMertens (RHLean.Arithmetic.primorial S)
            (B / RHLean.Arithmetic.primorial S)) = 0 := by
    rw [← Finset.sum_mul, hmu, zero_mul]
  rw [hanchor, sub_zero]

/-- The signed interval aggregate is invariant under adjoining a fresh prime:
the new wheel refines the same physical Mertens prefix rather than restarting
the estimate.  This is the interval-carrier form of
`primeWheelMertensTransport_invariant_insert`. -/
theorem primeWheelSignedIntervalAggregate_invariant_insert
    (S : Finset ℕ) (p : ℕ)
    (hp : Nat.Prime p) (hpS : p ∉ S)
    (hprime : ∀ q ∈ S, Nat.Prime q)
    (hWne : RHLean.Arithmetic.primorial S ≠ 1)
    (hWins : RHLean.Arithmetic.primorial (insert p S) ≠ 1)
    (B : ℕ) :
    primeWheelSignedIntervalAggregate (insert p S) B =
      primeWheelSignedIntervalAggregate S B := by
  have hprimeInsert : ∀ q ∈ insert p S, Nat.Prime q := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hqS
    · exact hp
    · exact hprime q hqS
  rw [← roughMertens_one_eq_primeWheel_signedIntervalAggregate
        (insert p S) hprimeInsert hWins B,
      ← roughMertens_one_eq_primeWheel_signedIntervalAggregate
        S hprime hWne B]

end RHLean.Proof
