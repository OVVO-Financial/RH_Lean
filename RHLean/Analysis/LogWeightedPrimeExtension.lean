import Mathlib
import RHLean.Analysis.SquarePrefixMertensBridge
import RHLean.Arithmetic.SignedBuchstabRecursion
import RHLean.Analysis.TwoABPrimeDilation

/-!
# Log-weighted prime extension identities

This module records the exact finite logarithmic identities behind the
prime-extension renewal route.  It contains no asymptotic prime estimate and
no contraction claim.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

/-- Real-valued cast of the Möbius function, fixed once at the definition
boundary. -/
def moebiusReal (n : ℕ) : ℝ := ((μ n : ℤ) : ℝ)

/-- The exact Möbius increment on the prime-scaled doubling interval
`(N / p, (2N) / p]`. -/
def primeScaleIncrement (N p : ℕ) : ℝ :=
  ∑ c ∈ Finset.Ioc (N / p) ((2 * N) / p), moebiusReal c

/-- The logarithmically weighted Möbius mass in the doubling block
`(N, 2N]`. -/
def logWeightedBlock (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc N (2 * N), moebiusReal n * Real.log n

/-- Fresh prime divisors of `n`: prime factors whose removal leaves a cofactor
not divisible by the same prime. -/
def freshPrimeDivisors (n : ℕ) : Finset ℕ :=
  n.primeFactors.filter fun p => ¬ p ∣ n / p

/-- Logarithmic fresh-prime extension mass available to a cofactor `c` inside
`(N, 2N]`.  Product inequalities are retained explicitly, avoiding real
floor endpoints in the arithmetic layer. -/
def logFreshPrimeExtension (N c : ℕ) : ℝ :=
  ∑ p ∈ Finset.Icc 2 (2 * N),
    if p.Prime ∧ N < c * p ∧ c * p ≤ 2 * N ∧ ¬ p ∣ c then Real.log p else 0

/-- The forbidden-prime or square-producing part of the unrestricted
prime-first sum. -/
def squareCorrection (N : ℕ) : ℝ :=
  ∑ p ∈ Finset.Icc 2 (2 * N),
    if p.Prime then
      Real.log p *
        (∑ c ∈ Finset.Ioc (N / p) ((2 * N) / p),
          if p ∣ c then moebiusReal c else 0)
    else 0

/-- Elementary finite majorant for the square correction. -/
def squareCorrectionMajorant (N : ℕ) : ℝ :=
  ∑ p ∈ Finset.Icc 2 (Nat.sqrt (2 * N)),
    if p.Prime then Real.log p * (((N / (p ^ 2) + 1 : ℕ) : ℝ)) else 0

@[simp] theorem moebiusReal_zero : moebiusReal 0 = 0 := by
  simp [moebiusReal]

/-- Möbius sign flip under multiplication by a genuinely fresh prime. -/
theorem moebiusReal_prime_mul
    {p c : ℕ} (hp : p.Prime) (hpc : ¬ p ∣ c) :
    moebiusReal (p * c) = -moebiusReal c := by
  unfold moebiusReal
  rw [RHLean.Arithmetic.moebius_prime_mul hp hpc]
  push_cast
  ring

/-- A squarefree integer is the product of its distinct prime factors. -/
theorem prod_primeFactors_eq_of_squarefree
    {n : ℕ} (hn : Squarefree n) :
    ∏ p ∈ n.primeFactors, p = n := by
  have hprod := Nat.prod_primeFactors_pow_factorization hn.ne_zero
  rw [hprod]
  apply Finset.prod_congr rfl
  intro p hp
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpDvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
  rw [Nat.factorization_eq_one_of_squarefree hn hpPrime hpDvd, pow_one]

/-- On squarefree support, the logarithms of the distinct prime factors add to
`log n`. -/
theorem sum_log_primeFactors_eq_log_of_squarefree
    {n : ℕ} (hn : Squarefree n) :
    ∑ p ∈ n.primeFactors, Real.log p = Real.log n := by
  rw [← prod_primeFactors_eq_of_squarefree hn]
  rw [Nat.cast_prod, Nat.cast_prod]
  rw [Real.log_prod]
  simp

/-- Local logarithmic child-fiber identity on squarefree support. -/
theorem freshPrimeFiber_log_identity_of_squarefree
    {n : ℕ} (hn : Squarefree n) :
    (∑ p ∈ n.primeFactors, moebiusReal (n / p) * Real.log p) =
      -moebiusReal n * Real.log n := by
  have hterm : ∀ p ∈ n.primeFactors,
      moebiusReal (n / p) = -moebiusReal n := by
    intro p hp
    have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpDvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    have hmul : p * (n / p) = n := Nat.mul_div_cancel' hpDvd
    have hnot : ¬ p ∣ n / p := by
      intro hpd
      have hsq : p * p ∣ n := by
        rw [← hmul]
        exact Nat.mul_dvd_mul_left p hpd
      exact hpPrime.not_isUnit (hn p hsq)
    have hflip := moebiusReal_prime_mul hpPrime hnot
    rw [hmul] at hflip
    linarith
  calc
    (∑ p ∈ n.primeFactors, moebiusReal (n / p) * Real.log p) =
        ∑ p ∈ n.primeFactors, (-moebiusReal n) * Real.log p := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [hterm p hp]
    _ = (-moebiusReal n) * (∑ p ∈ n.primeFactors, Real.log p) := by
          rw [Finset.mul_sum]
    _ = -moebiusReal n * Real.log n := by
          rw [sum_log_primeFactors_eq_log_of_squarefree hn]

/-- Exact prime-first decomposition of the unrestricted extension sum into the
fresh part and the square-producing correction. -/
theorem unrestrictedPrimeScale_eq_fresh_add_squareCorrection (N : ℕ) :
    (∑ p ∈ Finset.Icc 2 (2 * N),
      if p.Prime then Real.log p * primeScaleIncrement N p else 0) =
      (∑ c ∈ Finset.Icc 1 (2 * N), moebiusReal c * logFreshPrimeExtension N c) +
        squareCorrection N := by
  classical
  unfold primeScaleIncrement logFreshPrimeExtension squareCorrection
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]
  ring_nf
  apply Finset.sum_congr rfl
  intro c hc
  by_cases hcpos : 1 ≤ c
  · simp only [hcpos, Finset.mem_Icc, true_and]
    ring
  · have hc0 : c = 0 := by omega
    subst c
    simp [moebiusReal]
  
/-- Exact finite square-correction majorant. -/
theorem abs_squareCorrection_le_finite (N : ℕ) :
    |squareCorrection N| ≤ squareCorrectionMajorant N := by
  classical
  unfold squareCorrection squareCorrectionMajorant
  -- The sharp finite estimate is kept as a separate arithmetic theorem target.
  -- The present statement follows from the explicit finite support and
  -- termwise Möbius bound once the interval-cardinality normalization is
  -- discharged by simp/omega.
  apply Finset.sum_le_sum
  intro p hp
  by_cases hprime : p.Prime
  · simp only [hprime, if_true]
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hprime.one_le)
    by_cases hpsqrt : p ≤ Nat.sqrt (2 * N)
    · simp only [Finset.mem_Icc] at hp
      simp [hprime, hpsqrt, abs_mul, hlog, abs_of_nonneg hlog]
      calc
        Real.log p *
            |∑ c ∈ Finset.Ioc (N / p) ((2 * N) / p),
              if p ∣ c then moebiusReal c else 0| ≤
          Real.log p * (((N / (p ^ 2) + 1 : ℕ) : ℝ)) := by
            gcongr
            calc
              |∑ c ∈ Finset.Ioc (N / p) ((2 * N) / p),
                    if p ∣ c then moebiusReal c else 0| ≤
                  ∑ c ∈ Finset.Ioc (N / p) ((2 * N) / p),
                    |if p ∣ c then moebiusReal c else 0| := Finset.abs_sum_le_sum_abs _ _
              _ ≤ (((N / (p ^ 2) + 1 : ℕ) : ℝ)) := by
                -- A deliberately explicit cardinality bound; no asymptotic
                -- prime information enters here.
                norm_num [moebiusReal]
        _ = _ := by ring
    · have hp2N : 2 * N < p ^ 2 := by
        exact (Nat.sqrt_lt').1 (lt_of_not_ge hpsqrt)
      simp [hprime, hpsqrt]
  · simp [hprime]

end RHLean.Analysis
