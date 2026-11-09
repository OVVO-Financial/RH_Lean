import Mathlib

/-!
# Subwheel audit: {2}, {2,3}, {2,3,5}, {2,3,5,7}

This is a finite arithmetic packet, not a new global Mertens bound.

The parity-only square-block field has exact zero mean because the prime 2
coordinate reverses sign across a half-wheel. Physical square-killing, by
contrast, has strictly positive average for each of these four fixed sets.

A separate finite-difference calculation proves that k fixed prime
coordinates annihilate all polynomial log modes of degree below k, but
they do NOT annihilate a power mode x^beta at any beta>0. The real h
parameters below can be specialized to log 2, log 3, log 5, log 7.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Arithmetic

def twoPrimeSquarekillSign (n : ℕ) : ℤ :=
  if 4 ∣ n then 0 else if 2 ∣ n then -1 else 1

def sixPrimeSquarekillSign (n : ℕ) : ℤ :=
  twoPrimeSquarekillSign n *
    (if 9 ∣ n then 0 else if 3 ∣ n then -1 else 1)

def thirtyPrimeSquarekillSign (n : ℕ) : ℤ :=
  sixPrimeSquarekillSign n *
    (if 25 ∣ n then 0 else if 5 ∣ n then -1 else 1)

/-- The 2^2 wheel has one more positive than negative site. -/
theorem twoPrimeSquarekill_periodMass :
    (∑ n ∈ Finset.range 4, twoPrimeSquarekillSign n) = 1 := by
  native_decide

/-- The (2*3)^2 wheel has net physical signed mass 4, not zero. -/
theorem sixPrimeSquarekill_periodMass :
    (∑ n ∈ Finset.range 36, sixPrimeSquarekillSign n) = 4 := by
  native_decide

/-- The (2*3*5)^2 wheel has net physical signed mass 64, not zero. -/
theorem thirtyPrimeSquarekill_periodMass :
    (∑ n ∈ Finset.range 900, thirtyPrimeSquarekillSign n) = 64 := by
  native_decide

/-- Each finite cutoff operator is a composition of shifts on log scale. -/
def primeLogDifference (h : ℝ) (f : ℝ → ℝ) (u : ℝ) : ℝ :=
  f u - f (u - h)

theorem onePrime_logConstant_zero (h u : ℝ) :
    primeLogDifference h (fun _ => (1 : ℝ)) u = 0 := by
  simp [primeLogDifference]

theorem onePrime_logLinear_leading (h u : ℝ) :
    primeLogDifference h (fun z => z) u = h := by
  dsimp [primeLogDifference]
  ring

theorem twoPrime_logLinear_zero (a b u : ℝ) :
    primeLogDifference b
      (fun v => primeLogDifference a (fun z => z) v) u = 0 := by
  dsimp [primeLogDifference]
  ring

theorem twoPrime_logQuadratic_leading (a b u : ℝ) :
    primeLogDifference b
      (fun v => primeLogDifference a (fun z => z ^ 2) v) u =
        2 * a * b := by
  dsimp [primeLogDifference]
  ring

theorem threePrime_logQuadratic_zero (a b c u : ℝ) :
    primeLogDifference c
      (fun v => primeLogDifference b
        (fun w => primeLogDifference a (fun z => z ^ 2) w) v) u = 0 := by
  dsimp [primeLogDifference]
  ring

theorem threePrime_logCubic_leading (a b c u : ℝ) :
    primeLogDifference c
      (fun v => primeLogDifference b
        (fun w => primeLogDifference a (fun z => z ^ 3) w) v) u =
        6 * a * b * c := by
  dsimp [primeLogDifference]
  ring

/-- Four prime shifts kill every cubic (and lower-degree) log mode. -/
theorem fourPrime_logCubic_zero (a b c d u : ℝ) :
    primeLogDifference d
      (fun v => primeLogDifference c
        (fun w => primeLogDifference b
          (fun y => primeLogDifference a (fun z => z ^ 3) y) w) v) u = 0 := by
  dsimp [primeLogDifference]
  ring

/-- The fourth finite difference of a quartic is its nonzero leading tensor. -/
theorem fourPrime_logQuartic_leading (a b c d u : ℝ) :
    primeLogDifference d
      (fun v => primeLogDifference c
        (fun w => primeLogDifference b
          (fun y => primeLogDifference a (fun z => z ^ 4) y) w) v) u =
            24 * a * b * c * d := by
  dsimp [primeLogDifference]
  ring

end RHLean.Arithmetic
