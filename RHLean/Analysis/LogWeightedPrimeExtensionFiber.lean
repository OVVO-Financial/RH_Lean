import Mathlib
import RHLean.Analysis.LogWeightedPrimeExtension

/-!
# Log-weighted squarefree child fibers

This module proves the local logarithmic child-fiber identity and then extends
it to every child in the finite doubling block.  Nonsquarefree children vanish
fiberwise because every genuinely fresh prime leaves a nonsquarefree cofactor.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

/-- A squarefree positive natural is the product of its distinct prime
factors. -/
theorem prod_primeFactors_eq_self_of_squarefree
    {n : ℕ} (hs : Squarefree n) :
    ∏ p ∈ n.primeFactors, p = n := by
  calc
    (∏ p ∈ n.primeFactors, p) =
        ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
          apply Finset.prod_congr rfl
          intro p hp
          have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
          have hpDvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
          rw [Nat.factorization_eq_one_of_squarefree hs hpPrime hpDvd, pow_one]
    _ = n.factorization.prod (fun p k => p ^ k) := by
          rw [Nat.prod_factorization_eq_prod_primeFactors]
    _ = n := Nat.factorization_prod_pow_eq_self hs.ne_zero

/-- The logarithm of a finite product of positive naturals is the sum of their
logarithms. -/
theorem log_nat_finset_prod
    (s : Finset ℕ) (hpos : ∀ x ∈ s, 0 < x) :
    Real.log (((∏ x ∈ s, x : ℕ) : ℝ)) =
      ∑ x ∈ s, Real.log x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have haPos : 0 < a := hpos a (Finset.mem_insert_self a s)
      have hsPos : ∀ x ∈ s, 0 < x := by
        intro x hx
        exact hpos x (Finset.mem_insert_of_mem hx)
      have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt haPos)
      have hs0 : (((∏ x ∈ s, x : ℕ) : ℝ)) ≠ 0 := by
        exact_mod_cast (Finset.prod_ne_zero_iff.mpr fun x hx => Nat.ne_of_gt (hsPos x hx))
      rw [Finset.prod_insert ha, Finset.sum_insert ha, Nat.cast_mul,
        Real.log_mul ha0 hs0, ih hsPos]

/-- On squarefree support, the logarithms of the distinct prime factors sum to
`log n`. -/
theorem sum_log_primeFactors_eq_log
    {n : ℕ} (hs : Squarefree n) :
    ∑ p ∈ n.primeFactors, Real.log p = Real.log n := by
  have hpos : ∀ p ∈ n.primeFactors, 0 < p := by
    intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).pos
  rw [← log_nat_finset_prod n.primeFactors hpos]
  rw [prod_primeFactors_eq_self_of_squarefree hs]

/-- A prime factor of a squarefree integer does not divide the complementary
cofactor. -/
theorem prime_not_dvd_div_of_squarefree
    {n p : ℕ} (hs : Squarefree n) (hp : p ∈ n.primeFactors) :
    ¬ p ∣ n / p := by
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpDvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
  have hmul : p * (n / p) = n := Nat.mul_div_cancel' hpDvd
  intro hpd
  have hsq : p * p ∣ n := by
    rw [← hmul]
    exact Nat.mul_dvd_mul_left p hpd
  exact hpPrime.not_isUnit (hs p hsq)

/-- Removing a prime factor from a squarefree number reverses its Möbius sign. -/
theorem moebiusReal_div_prime_eq_neg
    {n p : ℕ} (hs : Squarefree n) (hp : p ∈ n.primeFactors) :
    moebiusReal (n / p) = -moebiusReal n := by
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hnot := prime_not_dvd_div_of_squarefree hs hp
  have hpDvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
  have hmul : p * (n / p) = n := Nat.mul_div_cancel' hpDvd
  have hflip := moebiusReal_prime_mul hpPrime hnot
  rw [hmul] at hflip
  linarith

/-- Local logarithmic child-fiber identity on squarefree support. -/
theorem sum_log_p_mu_parent_eq_neg_mu_log
    (n : ℕ) (hs : Squarefree n) :
    (∑ p ∈ n.primeFactors,
      moebiusReal (n / p) * Real.log p) =
      -moebiusReal n * Real.log n := by
  calc
    (∑ p ∈ n.primeFactors,
        moebiusReal (n / p) * Real.log p) =
      ∑ p ∈ n.primeFactors,
        (-moebiusReal n) * Real.log p := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [moebiusReal_div_prime_eq_neg hs hp]
    _ = (-moebiusReal n) *
        (∑ p ∈ n.primeFactors, Real.log p) := by
          rw [Finset.mul_sum]
    _ = -moebiusReal n * Real.log n := by
          rw [sum_log_primeFactors_eq_log hs]

/-- On squarefree support every prime divisor is fresh. -/
theorem freshPrimeDivisors_eq_primeFactors_of_squarefree
    {n : ℕ} (hs : Squarefree n) :
    freshPrimeDivisors n = n.primeFactors := by
  unfold freshPrimeDivisors
  apply Finset.filter_eq_self.mpr
  intro p hp
  exact prime_not_dvd_div_of_squarefree hs hp

/-- If `n` is not squarefree, removing a genuinely fresh prime cannot make it
squarefree: the repeated prime factor lies elsewhere. -/
theorem not_squarefree_div_of_fresh_prime
    {n p : ℕ} (hns : ¬Squarefree n)
    (hp : p ∈ freshPrimeDivisors n) :
    ¬Squarefree (n / p) := by
  rw [freshPrimeDivisors, Finset.mem_filter] at hp
  rcases hp with ⟨hpPF, hnot⟩
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpPF
  have hpDvd : p ∣ n := Nat.dvd_of_mem_primeFactors hpPF
  have hmul : p * (n / p) = n := Nat.mul_div_cancel' hpDvd
  intro hco
  have hcop : Nat.Coprime p (n / p) :=
    (hpPrime.coprime_iff_not_dvd).2 hnot
  have hsq : Squarefree (p * (n / p)) :=
    (Nat.squarefree_mul hcop).2 ⟨hpPrime.squarefree, hco⟩
  exact hns (by simpa [hmul] using hsq)

/-- **Complete fresh child fiber.**  The logarithmic identity holds for every
child, not only squarefree children.  Nonsquarefree children vanish termwise on
the fresh fiber. -/
theorem sum_freshPrimeDivisors_mu_parent_log_eq_neg_mu_log (n : ℕ) :
    (∑ p ∈ freshPrimeDivisors n,
      moebiusReal (n / p) * Real.log p) =
      -moebiusReal n * Real.log n := by
  by_cases hs : Squarefree n
  · rw [freshPrimeDivisors_eq_primeFactors_of_squarefree hs]
    exact sum_log_p_mu_parent_eq_neg_mu_log n hs
  · have hmuN : moebiusReal n = 0 := by
      unfold moebiusReal
      rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]
      norm_num
    rw [hmuN]
    simp only [neg_zero, zero_mul]
    apply Finset.sum_eq_zero
    intro p hp
    have hnsParent := not_squarefree_div_of_fresh_prime hs hp
    have hmuParent : moebiusReal (n / p) = 0 := by
      unfold moebiusReal
      rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsParent]
      norm_num
    rw [hmuParent, zero_mul]

/-- The child-first fresh logarithmic mass on the doubling block. -/
def logFreshChildFiberMass (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc N (2 * N),
    ∑ p ∈ freshPrimeDivisors n,
      moebiusReal (n / p) * Real.log p

/-- **Global child-first collapse.**  After grouping by the child product, the
entire fresh fiber is exactly the negative log-weighted Möbius block. -/
theorem logFreshChildFiberMass_eq_neg_logWeightedBlock (N : ℕ) :
    logFreshChildFiberMass N = -logWeightedBlock N := by
  unfold logFreshChildFiberMass logWeightedBlock
  calc
    (∑ n ∈ Finset.Ioc N (2 * N),
        ∑ p ∈ freshPrimeDivisors n,
          moebiusReal (n / p) * Real.log p) =
      ∑ n ∈ Finset.Ioc N (2 * N),
        (-moebiusReal n * Real.log n) := by
          apply Finset.sum_congr rfl
          intro n hn
          exact sum_freshPrimeDivisors_mu_parent_log_eq_neg_mu_log n
    _ = -∑ n ∈ Finset.Ioc N (2 * N),
        moebiusReal n * Real.log n := by
          rw [Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro n hn
          ring

end RHLean.Analysis
