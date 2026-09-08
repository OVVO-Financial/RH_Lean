import RHLean.Arithmetic.PrimeCombFiniteDifferenceFreshPrime

/-!
# Signed truncated Mobius kernel of a finite prime wheel

This is the coefficient that appears after the exact signed wheel interval
aggregate is reindexed by physical rough seats.  Unlike separate-band counting,
it keeps every divisor sign until the last step.

For a finite prime set `S`, write

`K_S(X) = sum_{d | prod S, d <= X} mu(d)`.

Adjoining a fresh prime is exactly one multiplicative finite difference:

`K_{S union {p}}(X) = K_S(X) - K_S(floor(X/p))`.

No absolute value, density estimate, or wheel-depth loss occurs.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

/-- Signed Mobius mass of wheel divisors admitted by cutoff `X`.  The `if`
form keeps the complete divisor carrier fixed, which makes fresh-prime
refinement an exact fiber split. -/
def primeWheelTruncatedMoebiusKernel (S : Finset ℕ) (X : ℕ) : ℤ :=
  ∑ d ∈ (primorial S).divisors,
    if d ≤ X then (μ d : ℤ) else 0

/-- **Exact fresh-prime recurrence for the signed cutoff kernel.**  The old
divisors and their fresh-`p` children have opposite Mobius signs, so adjoining
`p` differences the old kernel at the reciprocal cutoff. -/
theorem primeWheelTruncatedMoebiusKernel_insert
    (S : Finset ℕ) (p X : ℕ)
    (hp : Nat.Prime p) (hpS : p ∉ S)
    (hprime : ∀ q ∈ S, Nat.Prime q) :
    primeWheelTruncatedMoebiusKernel (insert p S) X =
      primeWheelTruncatedMoebiusKernel S X -
        primeWheelTruncatedMoebiusKernel S (X / p) := by
  classical
  have hcop : Nat.Coprime p (primorial S) :=
    prime_coprime_primorial S p hp hpS hprime
  have hdisj :=
    disjoint_divisors_primorial_mul_image S p hp hpS hprime
  unfold primeWheelTruncatedMoebiusKernel
  rw [divisors_primorial_insert S p hp hpS]
  rw [Finset.sum_union hdisj]
  have hinj : Set.InjOn (fun d : ℕ => p * d) (primorial S).divisors := by
    intro a _ha b _hb hab
    exact Nat.mul_left_cancel hp.pos hab
  have hsecond :
      (∑ d ∈ (primorial S).divisors.image (fun d => p * d),
          if d ≤ X then (μ d : ℤ) else 0) =
        -(∑ d ∈ (primorial S).divisors,
          if d ≤ X / p then (μ d : ℤ) else 0) := by
    rw [Finset.sum_image hinj]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    have hdP : d ∣ primorial S := Nat.dvd_of_mem_divisors hd
    have hcopd : Nat.Coprime p d := hcop.of_dvd_right hdP
    have hmu : μ (p * d) = -μ d := by
      rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcopd]
      rw [ArithmeticFunction.moebius_apply_prime hp]
      ring
    have hcut : p * d ≤ X ↔ d ≤ X / p := by
      constructor
      · intro h
        apply (Nat.le_div_iff_mul_le hp.pos).2
        simpa [Nat.mul_comm] using h
      · intro h
        have hm := (Nat.le_div_iff_mul_le hp.pos).1 h
        simpa [Nat.mul_comm] using hm
    by_cases hdX : d ≤ X / p
    · have hpdX : p * d ≤ X := hcut.mpr hdX
      simp [hdX, hpdX, hmu]
    · have hpdX : ¬ p * d ≤ X := by
        intro h
        exact hdX (hcut.mp h)
      simp [hdX, hpdX]
  rw [hsecond]
  ring

/-- The recurrence can be read literally as the old cutoff kernel minus its
fresh-prime-scaled child. -/
theorem primeWheelTruncatedMoebiusKernel_insert_sub
    (S : Finset ℕ) (p X : ℕ)
    (hp : Nat.Prime p) (hpS : p ∉ S)
    (hprime : ∀ q ∈ S, Nat.Prime q) :
    primeWheelTruncatedMoebiusKernel (insert p S) X -
        primeWheelTruncatedMoebiusKernel S X =
      -primeWheelTruncatedMoebiusKernel S (X / p) := by
  rw [primeWheelTruncatedMoebiusKernel_insert S p X hp hpS hprime]
  ring

end RHLean.Proof
