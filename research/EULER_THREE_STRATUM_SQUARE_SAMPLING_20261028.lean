import Mathlib
import «research.EULER_ADMISSIBLE_SIGNED_RETURN_TELESCOPE_20261028»

/-!
# Three genuinely admitted prime strata sampled across moving square blocks

For X_R = R^2-1 and y=R-1, split the ORIGINAL prime-factor-admissible
Euler population at y, X_R/2 and X_R:

  low:     largest prime factor < R, including 1;
  middle:  prime p in [R, X_R/2], with cofactor >= 2;
  upper:   prime p in (X_R/2, X_R], with cofactor exactly 1.

The last class consists of prime singletons. Its contribution is negative,
and is NOT independently centered. We prove exact floor-faithful band
reassembly and a full six-term, signed dynamic square-shell Gram when the
sampled index R ranges across a deterministic dyadic window.

None of these finite identities asserts random signs, martingale
increments, zero pair covariance, a stochastic law, or power saving.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof
open RHLean.Analysis

/-- The complete low-prime product-admissible population. This is NOT the
sum of Mobius over integers n <= sqrt X; it includes all admissible products
up to X formed exclusively from lower primes. -/
def eulerThreeLow (R : ℕ) : ℂ :=
  eulerAdmissibleLowPopulation R

/-- Reciprocal bands k>=2 are exactly prime families with a cofactor >=2. -/
def eulerThreeMiddleDebt (R : ℕ) : ℂ :=
  ∑ k ∈ Finset.Icc 2 (R - 1),
    (eulerAdmissibleBandPopulation R k : ℂ) * mertensSummatory k

/-- Band k=1 consists only of singleton primes in the top half. -/
def eulerThreeTopDebt (R : ℕ) : ℂ :=
  (eulerAdmissibleBandPopulation R 1 : ℂ)

/-- Actual signed middle population: opposite of prime-family debt. -/
def eulerThreeMiddle (R : ℕ) : ℂ :=
  -eulerThreeMiddleDebt R

/-- Actual signed top population: minus the count of prime singletons. -/
def eulerThreeTop (R : ℕ) : ℂ :=
  -eulerThreeTopDebt R

/-- At X=R^2-1 the top-half split lies above the strict low-prime gate
R-1. This is a geometric fact, not a prime-distribution estimate. -/
theorem eulerThree_root_le_half (R : ℕ) (hR : 2 ≤ R) :
    R - 1 ≤ squareRootEndpoint R / 2 := by
  have hpred : R - 1 + 1 = R := by omega
  have hsq : 1 ≤ R ^ 2 := by nlinarith
  have hX : squareRootEndpoint R + 1 = R ^ 2 := by
    unfold squareRootEndpoint
    omega
  apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2
  nlinarith [sq_nonneg (R - 1)]

/-- The top reciprocal band really IS (X/2, X], with prime-count
multiplicity rather than a surrogate density. -/
theorem eulerThreeTopDebt_eq_prime_singletons
    (R : ℕ) (hR : 2 ≤ R) :
    eulerThreeTopDebt R =
      ((((Finset.Ioc (squareRootEndpoint R / 2)
          (squareRootEndpoint R)).filter Nat.Prime).card : ℕ) : ℂ) := by
  have hgeom := eulerThree_root_le_half R hR
  unfold eulerThreeTopDebt eulerAdmissibleBandPopulation
    primeSieveReciprocalInterval primeSieveReciprocalLower
    primeSieveReciprocalUpper
  simp [max_eq_right hgeom]

/-- Top-half debt is exactly pi(X)-pi(floor X/2). -/
theorem eulerThreeTopDebt_eq_primeCounting_gap
    (R : ℕ) (hR : 2 ≤ R) :
    eulerThreeTopDebt R =
      (((Nat.primeCounting (squareRootEndpoint R) -
        Nat.primeCounting (squareRootEndpoint R / 2) : ℕ) : ℂ)) := by
  rw [eulerThreeTopDebt_eq_prime_singletons R hR]
  have hcount := primeCard_Ioc_add_primeCounting_eq
    (a := squareRootEndpoint R / 2)
    (b := squareRootEndpoint R)
    (Nat.div_le_self _ _)
  have hres :
      ((Finset.Ioc (squareRootEndpoint R / 2)
          (squareRootEndpoint R)).filter Nat.Prime).card =
        Nat.primeCounting (squareRootEndpoint R) -
          Nat.primeCounting (squareRootEndpoint R / 2) := by omega
  exact_mod_cast hres

/-- Singletons have actual Mobius value -1 and therefore are an
uncentered, explicitly negative component of the signed Euler population. -/
theorem eulerThreeTop_eq_negative_prime_gap
    (R : ℕ) (hR : 2 ≤ R) :
    eulerThreeTop R =
      -(((Nat.primeCounting (squareRootEndpoint R) -
        Nat.primeCounting (squareRootEndpoint R / 2) : ℕ) : ℂ)) := by
  rw [eulerThreeTop, eulerThreeTopDebt_eq_primeCounting_gap R hR]

/-- Exact separation of the two high-prime strata, retaining every
actual reciprocal prime-count multiplicity. -/
theorem eulerAdmissiblePrimeDebt_eq_middle_add_top
    (R : ℕ) (hR : 2 ≤ R) :
    eulerAdmissiblePrimeDebt R =
      eulerThreeMiddleDebt R + eulerThreeTopDebt R := by
  rw [eulerAdmissiblePrimeDebt_eq_exact_bands R hR]
  have hset : Finset.Icc 1 (R - 1) =
      insert 1 (Finset.Icc 2 (R - 1)) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hset, Finset.sum_insert (by simp [Finset.mem_Icc])]
  have hMone : mertensSummatory 1 = 1 := by
    simp
  unfold eulerThreeMiddleDebt eulerThreeTopDebt
  rw [hMone]
  ring

/-- Exact three-way admitted Euler product decomposition at EVERY root.
No random-sign or stochastic independence assumption appears. -/
theorem eulerThree_endpoint_eq_three_strata
    (R : ℕ) (hR : 2 ≤ R) :
    mertensSummatory (squareRootEndpoint R) =
      eulerThreeLow R + eulerThreeMiddle R + eulerThreeTop R := by
  rw [eulerAdmissible_endpoint_eq_low_add_innovation R hR]
  have hsplit := eulerAdmissiblePrimeDebt_eq_middle_add_top R hR
  unfold eulerAdmissibleHighInnovation eulerThreeLow
    eulerThreeMiddle eulerThreeTop
  rw [hsplit]
  ring

/-- Exact three-stratum original self-dual Euler Gram. -/
theorem eulerThree_selfDual_eq_three_strata
    (R : ℕ) (hR : 2 ≤ R) :
    eulerHybridDiagonal R +
        2 * (eulerAdmissibleWeightedCo R - eulerAdmissibleWeightedDiv R) =
      2 * mertensSummatory (R - 1) -
        (eulerThreeLow R + eulerThreeMiddle R + eulerThreeTop R) := by
  have hQ := eulerAdmissible_weighted_CoDiv_eq_primePopulation R hR
  rw [hQ, eulerAdmissiblePrimeDebt_eq_middle_add_top R hR]
  unfold eulerThreeLow eulerThreeMiddle eulerThreeTop
  ring

/-! ## Sampling *the index R* across square shells, not randomizing Mobius -/

/-- True signed dyadic shell change of the low, resolved population. -/
def eulerThreeShellLow (R : ℕ) : ℝ :=
  (eulerThreeLow (R + 1) - eulerThreeLow R).re

/-- True signed dyadic shell change of the middle, cofactor-bearing population. -/
def eulerThreeShellMiddle (R : ℕ) : ℝ :=
  (eulerThreeMiddle (R + 1) - eulerThreeMiddle R).re

/-- True signed dyadic shell change of prime singletons in the moving top half. -/
def eulerThreeShellTop (R : ℕ) : ℝ :=
  (eulerThreeTop (R + 1) - eulerThreeTop R).re

/-- The actual square-shell Mobius increment (no sampling surrogate). -/
def eulerThreeShellMobius (R : ℕ) : ℝ :=
  (mertensSummatory (squareRootEndpoint (R + 1)) -
    mertensSummatory (squareRootEndpoint R)).re

/-- The gate switches between strata when R advances, but all charges
are retained and cancel in the total actual Mobius shell increment. -/
theorem eulerThree_shellFlow_eq_three
    (R : ℕ) (hR : 2 ≤ R) :
    eulerThreeShellMobius R =
      eulerThreeShellLow R +
        eulerThreeShellMiddle R + eulerThreeShellTop R := by
  unfold eulerThreeShellMobius eulerThreeShellLow
    eulerThreeShellMiddle eulerThreeShellTop
  rw [eulerThree_endpoint_eq_three_strata (R + 1) (by omega),
    eulerThree_endpoint_eq_three_strata R hR]
  simp only [Complex.sub_re, Complex.add_re]
  ring

/-- Sum of the true dyadic squared signed block samples. -/
def eulerThreeSampledShellEnergy (H : ℕ) : ℝ :=
  ∑ R ∈ Finset.Ico H (2 * H), (eulerThreeShellMobius R) ^ 2

/-- The six-term signed Gram of the *three evolving strata*, with all
three diagonal energies and every off-diagonal cross term preserved. -/
theorem eulerThree_sampledSixTermGram
    (H : ℕ) (hH : 2 ≤ H) :
    eulerThreeSampledShellEnergy H =
      (∑ R ∈ Finset.Ico H (2 * H), (eulerThreeShellLow R) ^ 2) +
      (∑ R ∈ Finset.Ico H (2 * H), (eulerThreeShellMiddle R) ^ 2) +
      (∑ R ∈ Finset.Ico H (2 * H), (eulerThreeShellTop R) ^ 2) +
      (∑ R ∈ Finset.Ico H (2 * H),
        2 * eulerThreeShellLow R * eulerThreeShellMiddle R) +
      (∑ R ∈ Finset.Ico H (2 * H),
        2 * eulerThreeShellLow R * eulerThreeShellTop R) +
      (∑ R ∈ Finset.Ico H (2 * H),
        2 * eulerThreeShellMiddle R * eulerThreeShellTop R) := by
  unfold eulerThreeSampledShellEnergy
  calc
    _ = ∑ R ∈ Finset.Ico H (2 * H),
          (eulerThreeShellLow R + eulerThreeShellMiddle R +
            eulerThreeShellTop R) ^ 2 := by
      apply Finset.sum_congr rfl
      intro R hR
      rw [eulerThree_shellFlow_eq_three R (by
        have hp := (Finset.mem_Ico.mp hR).1
        omega)]
    _ = ∑ R ∈ Finset.Ico H (2 * H),
          ((eulerThreeShellLow R) ^ 2 +
           (eulerThreeShellMiddle R) ^ 2 +
           (eulerThreeShellTop R) ^ 2 +
           2 * eulerThreeShellLow R * eulerThreeShellMiddle R +
           2 * eulerThreeShellLow R * eulerThreeShellTop R +
           2 * eulerThreeShellMiddle R * eulerThreeShellTop R) := by
      apply Finset.sum_congr rfl
      intro R _hR
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib]

#print axioms eulerThree_root_le_half
#print axioms eulerThreeTopDebt_eq_prime_singletons
#print axioms eulerThreeTopDebt_eq_primeCounting_gap
#print axioms eulerAdmissiblePrimeDebt_eq_middle_add_top
#print axioms eulerThree_endpoint_eq_three_strata
#print axioms eulerThree_selfDual_eq_three_strata
#print axioms eulerThree_shellFlow_eq_three
#print axioms eulerThree_sampledSixTermGram

end RHLean.Proof
