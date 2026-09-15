import Mathlib
import RHLean.Arithmetic.PrimeWheelMobiusRecovery

/-!
# Finite-prime alignment residual

The stacked prime/Perron visualization has an exact arithmetic interpretation.
On squarefree support every processed prime divisor contributes one sign flip.
Thus the sign at a site is determined by the parity of the processed aligned
prime coordinates, while the difference from the true Moebius sign is entirely
determined by the parity of the as-yet unseen prime factors.

At square-root coverage there is at most one unseen prime factor, so this
residual has only two states: zero, or exactly twice the processed alignment
sign with the opposite orientation.  This is a carrier identity, not an
estimate and not an appeal to prime density.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Number of processed prime coordinates aligned at `n`. -/
def primeAlignmentCount (S : Finset ℕ) (n : ℕ) : ℕ :=
  (S.filter fun p => p ∣ n).card

/-- Sign displayed by the all-plus stacked prime alignment state. -/
def primeAlignmentSign (S : Finset ℕ) (n : ℕ) : ℤ :=
  (-1 : ℤ) ^ primeAlignmentCount S n

/-- Number of prime factors of `n` not yet represented in the processed set. -/
def unseenPrimeAlignmentCount (S : Finset ℕ) (n : ℕ) : ℕ :=
  (n.primeFactors \ S).card

/-- Difference between the true Moebius sign and the processed alignment sign. -/
def primeAlignmentResidual (S : Finset ℕ) (n : ℕ) : ℤ :=
  μ n - primeAlignmentSign S n

/-- The visual parity sign is exactly the product of the processed local Euler
coordinates. -/
theorem primeAlignmentSign_eq_localPrimeCombProduct
    (S : Finset ℕ) (n : ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hsq : Squarefree n) :
    primeAlignmentSign S n = ∏ p ∈ S, localPrimeComb p n := by
  symm
  exact prod_localPrimeComb_eq_negOnePow_filter_card S n hprime hsq

/-- **Exact processed/unseen factorization.**  The true Moebius sign is the
processed alignment parity times the parity of the unseen prime factors. -/
theorem moebius_eq_alignmentSign_mul_unseenParity
    (S : Finset ℕ) {n : ℕ}
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hsq : Squarefree n) :
    μ n = primeAlignmentSign S n *
      ((-1 : ℤ) ^ unseenPrimeAlignmentCount S n) := by
  have hn0 : n ≠ 0 := hsq.ne_zero
  have hinter := filter_dvd_eq_primeFactors_inter S hn0 hprime
  have hcard := Finset.card_sdiff_add_card_inter n.primeFactors S
  have htotal :
      n.primeFactors.card =
        (n.primeFactors ∩ S).card + (n.primeFactors \ S).card := by
    omega
  rw [moebius_eq_negOnePow_primeFactors_card hsq, htotal, pow_add]
  unfold primeAlignmentSign primeAlignmentCount unseenPrimeAlignmentCount
  rw [hinter]

/-- **General residual formula.**  No small-prime case split remains: the
residual is controlled exactly by unseen-factor parity. -/
theorem primeAlignmentResidual_eq_alignmentSign_mul_unseenParity_sub_one
    (S : Finset ℕ) {n : ℕ}
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hsq : Squarefree n) :
    primeAlignmentResidual S n =
      primeAlignmentSign S n *
        (((-1 : ℤ) ^ unseenPrimeAlignmentCount S n) - 1) := by
  unfold primeAlignmentResidual
  rw [moebius_eq_alignmentSign_mul_unseenParity S hprime hsq]
  ring

/-- Under square-root coverage there is at most one unseen aligned prime. -/
theorem unseenPrimeAlignmentCount_le_one_of_sqrtCoverage
    (S : Finset ℕ) {upper n : ℕ}
    (hcover : PrimeWheelSqrtCoverage S upper)
    (hnpos : 0 < n) (hnupper : n ≤ upper) :
    unseenPrimeAlignmentCount S n ≤ 1 := by
  unfold unseenPrimeAlignmentCount
  exact large_primeFactors_card_le_one S hcover hnpos hnupper

/-- **Two-state square-root residual.**  Once all primes through `sqrt upper`
have been processed, a squarefree site has either no residual or exactly the
opposite twice-alignment residual.  This is the formal version of the stacked
picture: even unseen parity gives `+1`, odd unseen parity gives `-1`. -/
theorem primeAlignmentResidual_eq_zero_or_neg_two_mul_alignmentSign
    (S : Finset ℕ) {upper n : ℕ}
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hcover : PrimeWheelSqrtCoverage S upper)
    (hsq : Squarefree n) (hnupper : n ≤ upper) :
    primeAlignmentResidual S n = 0 ∨
      primeAlignmentResidual S n = -2 * primeAlignmentSign S n := by
  have hnpos : 0 < n := Nat.pos_of_ne_zero hsq.ne_zero
  have hle := unseenPrimeAlignmentCount_le_one_of_sqrtCoverage
    S hcover hnpos hnupper
  have hres :=
    primeAlignmentResidual_eq_alignmentSign_mul_unseenParity_sub_one
      S hprime hsq
  by_cases hz : unseenPrimeAlignmentCount S n = 0
  · left
    rw [hres, hz]
    simp
  · have hone : unseenPrimeAlignmentCount S n = 1 := by omega
    right
    rw [hres, hone]
    ring

end RHLean.Proof
