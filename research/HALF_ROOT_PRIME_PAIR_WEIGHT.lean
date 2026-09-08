import «research.PROPER_SUBWHEEL_OUTER_PARITY_REASSEMBLY»

/-!
# Half-root prime-pair shell

At the explicit proper subwheel `Y = R/2`, every two-high-prime reciprocal
argument is strictly below four.  This file evaluates those four ordinary
Mertens states and removes the remaining Mertens symbol from the semiprime
layer entirely.

The resulting weight is

* `+1` on `X_R / 2 < p*q <= X_R` (reciprocal depth 1),
* `0` on reciprocal depths 0 and 2,
* `-1` on `X_R / 4 < p*q <= X_R / 3` (reciprocal depth 3).

Thus the depth-two correction is a literal signed hyperbolic prime-pair shell.
No estimate or norm is used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

private theorem mertensSummatoryInt_zero : mertensSummatoryInt 0 = 0 := by
  simp [mertensSummatoryInt]

private theorem mertensSummatoryInt_one : mertensSummatoryInt 1 = 1 := by
  unfold mertensSummatoryInt
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  norm_num

private theorem mertensSummatoryInt_two : mertensSummatoryInt 2 = 0 := by
  have hmu2 : μ 2 = -1 :=
    ArithmeticFunction.moebius_apply_prime Nat.prime_two
  unfold mertensSummatoryInt
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
  norm_num [hmu2]

private theorem mertensSummatoryInt_three : mertensSummatoryInt 3 = -1 := by
  have hmu2 : μ 2 = -1 :=
    ArithmeticFunction.moebius_apply_prime Nat.prime_two
  have hmu3 : μ 3 = -1 :=
    ArithmeticFunction.moebius_apply_prime (by norm_num)
  unfold mertensSummatoryInt
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ]
  norm_num [hmu2, hmu3]

/-- Pure finite weight left by a pair of primes above the half-root. -/
def halfRootPrimePairWeight (R p q : ℕ) : ℤ :=
  if squareRootEndpoint R / (p * q) = 1 then 1
  else if squareRootEndpoint R / (p * q) = 3 then -1
  else 0

/-- The four-state Mertens response is exactly the signed prime-pair shell
weight. -/
theorem mertensSummatoryInt_squareRootEndpoint_div_pair_eq_halfRootPrimePairWeight
    {R p q : ℕ} (hR : 6 ≤ R)
    (hp : p ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (squareRootEndpoint R))
    (hq : q ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (p - 1)) :
    mertensSummatoryInt (squareRootEndpoint R / (p * q)) =
      halfRootPrimePairWeight R p q := by
  have hlt := squareRootEndpoint_div_two_halfRootHighPrimes_lt_four hR hp hq
  let z := squareRootEndpoint R / (p * q)
  have hzlt : z < 4 := by simpa [z] using hlt
  by_cases hz0 : z = 0
  · simp [halfRootPrimePairWeight, z, hz0, mertensSummatoryInt_zero]
  by_cases hz1 : z = 1
  · simp [halfRootPrimePairWeight, z, hz1, mertensSummatoryInt_one]
  by_cases hz2 : z = 2
  · simp [halfRootPrimePairWeight, z, hz2, mertensSummatoryInt_two]
  have hz3 : z = 3 := by
    clear_value z
    omega
  simp [halfRootPrimePairWeight, z, hz3, mertensSummatoryInt_three]

/-- The entire two-high-prime correction is now a finite prime-pair weight sum,
with no recursive Mertens value left. -/
theorem halfRoot_semiprimeLayer_eq_primePairWeight
    (R : ℕ) (hR : 6 ≤ R) :
    (∑ p ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (squareRootEndpoint R),
        ∑ q ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (p - 1),
          mertensSummatoryInt (squareRootEndpoint R / (p * q))) =
      ∑ p ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (squareRootEndpoint R),
        ∑ q ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (p - 1),
          halfRootPrimePairWeight R p q := by
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  exact mertensSummatoryInt_squareRootEndpoint_div_pair_eq_halfRootPrimePairWeight
    hR hp hq

/-- **Explicit half-root prime-pair normal form.**  The proper-subwheel Mertens
identity has only three pieces: one common frozen base, its one-prime common
kernel column, and a finite signed hyperbolic prime-pair shell. -/
theorem squareRootProperSubwheelFrozenCorrelation_eq_halfRootPrimePairShell
    (R : ℕ) (hR : 6 ≤ R) :
    squareRootProperSubwheelFrozenCorrelation R (R / 2) =
      frozenPrimeUniverseMass (primesUpTo (R / 2)) (squareRootEndpoint R) -
        (∑ p ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (squareRootEndpoint R),
          frozenPrimeUniverseMass (primesUpTo (R / 2))
            (squareRootEndpoint R / p)) +
        ∑ p ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (squareRootEndpoint R),
          ∑ q ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (p - 1),
            halfRootPrimePairWeight R p q := by
  rw [squareRootProperSubwheelFrozenCorrelation_eq_halfRootDepthTwo R hR,
    halfRoot_semiprimeLayer_eq_primePairWeight R hR]

end RHLean.Proof
