import Mathlib
import RHLean.Analysis.SquarePrefixMertensBridge

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

/-- Number of distinct prime factors `ω(n)`. -/
def distinctPrimeCount (n : ℕ) : ℕ :=
  n.primeFactors.card

/-- Multiplicity-correction weight in `ℚ`: `α(n) = 2^(-ω(n))`. -/
def alphaWeightRat (n : ℕ) : ℚ :=
  ((2 : ℚ) ^ distinctPrimeCount n)⁻¹

/-- Normalized arithmetic coefficient weight in `ℚ`. -/
def normalizedCofactorWeightRat (c q : ℕ) : ℚ :=
  alphaWeightRat (c * q) *
    (((μ c : ℤ) : ℚ)) *
    (((μ q : ℤ) : ℚ))

/-- Cast the normalized arithmetic coefficient to `ℂ` for later synthesis. -/
def normalizedCofactorWeight (c q : ℕ) : ℂ :=
  (normalizedCofactorWeightRat c q : ℂ)

/-- Ordered coprime factor pairs whose product is `m`. -/
def orderedCoprimeFactorPairs (m : ℕ) : Finset (ℕ × ℕ) :=
  m.divisorsAntidiagonal.filter fun p => Nat.Coprime p.1 p.2

/-- Rational-valued Mertens sum with the same indexing as the Analysis definition. -/
def mertensSummatoryRat (Q : ℕ) : ℚ :=
  ∑ m ∈ Finset.range (Q + 1), (((μ m : ℤ) : ℚ))

/-- Rational-valued normalized fiber expansion. -/
def normalizedFiberExpansionRat (Q : ℕ) : ℚ :=
  ∑ m ∈ Finset.range (Q + 1),
    ∑ p ∈ orderedCoprimeFactorPairs m,
      normalizedCofactorWeightRat p.1 p.2

@[simp] theorem mem_orderedCoprimeFactorPairs
    {m : ℕ} {p : ℕ × ℕ} :
    p ∈ orderedCoprimeFactorPairs m ↔
      p.1 * p.2 = m ∧ m ≠ 0 ∧ Nat.Coprime p.1 p.2 := by
  simp [orderedCoprimeFactorPairs, and_assoc]

theorem product_eq_of_mem_orderedCoprimeFactorPairs
    {m c q : ℕ}
    (h : (c, q) ∈ orderedCoprimeFactorPairs m) :
    c * q = m :=
  (mem_orderedCoprimeFactorPairs.mp h).1

theorem nonzero_of_mem_orderedCoprimeFactorPairs
    {m c q : ℕ}
    (h : (c, q) ∈ orderedCoprimeFactorPairs m) :
    m ≠ 0 :=
  (mem_orderedCoprimeFactorPairs.mp h).2.1

theorem coprime_of_mem_orderedCoprimeFactorPairs
    {m c q : ℕ}
    (h : (c, q) ∈ orderedCoprimeFactorPairs m) :
    Nat.Coprime c q :=
  (mem_orderedCoprimeFactorPairs.mp h).2.2

/-- Factors of a squarefree product are automatically coprime. -/
theorem coprime_factors_of_squarefree
    {m c q : ℕ}
    (hsq : Squarefree m)
    (hprod : c * q = m) :
    Nat.Coprime c q := by
  apply Nat.coprime_iff_isRelPrime.mpr
  apply IsRelPrime.of_squarefree_mul
  simpa [hprod] using hsq

/-- For squarefree products, the coprimality filter on the divisor antidiagonal is redundant. -/
theorem orderedCoprimeFactorPairs_eq_divisorsAntidiagonal
    (m : ℕ) (hsq : Squarefree m) :
    orderedCoprimeFactorPairs m = m.divisorsAntidiagonal := by
  ext p
  simp only [orderedCoprimeFactorPairs, Finset.mem_filter]
  constructor
  · exact fun h => h.1
  · intro hp
    refine ⟨hp, coprime_factors_of_squarefree hsq ?_⟩
    exact (Nat.mem_divisorsAntidiagonal.mp hp).1

/-- A positive squarefree fiber has one ordered factor pair for each subset of prime factors. -/
theorem orderedCoprimeFactorPairs_card_of_squarefree
    (m : ℕ) (hsq : Squarefree m) :
    (orderedCoprimeFactorPairs m).card =
      2 ^ distinctPrimeCount m := by
  rw [orderedCoprimeFactorPairs_eq_divisorsAntidiagonal m hsq]
  calc
    m.divisorsAntidiagonal.card = m.divisors.card := by
      rw [← Nat.map_div_right_divisors]
      simp
    _ = m.primeFactors.prod (fun p => m.factorization p + 1) :=
      Nat.card_divisors hsq.ne_zero
    _ = m.primeFactors.prod (fun _ => 2) := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [Nat.factorization_eq_one_of_squarefree hsq
        (Nat.prime_of_mem_primeFactors hp)
        (Nat.dvd_of_mem_primeFactors hp)]
    _ = 2 ^ distinctPrimeCount m := by
      simp [distinctPrimeCount]

/-- Möbius multiplicativity, cast into `ℚ`. -/
theorem moebius_mul_cast_rat_of_coprime
    {c q : ℕ}
    (hcop : Nat.Coprime c q) :
    (((μ c : ℤ) : ℚ)) * (((μ q : ℤ) : ℚ)) =
      (((μ (c * q) : ℤ) : ℚ)) := by
  simpa using
    congrArg (fun z : ℤ => (z : ℚ))
      (ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop).symm

/-- The normalized arithmetic weight is constant on each product fiber. -/
theorem normalizedCofactorWeightRat_eq_on_fiber
    {m c q : ℕ}
    (hmem : (c, q) ∈ orderedCoprimeFactorPairs m) :
    normalizedCofactorWeightRat c q =
      alphaWeightRat m * (((μ m : ℤ) : ℚ)) := by
  have hprod := product_eq_of_mem_orderedCoprimeFactorPairs hmem
  have hcop := coprime_of_mem_orderedCoprimeFactorPairs hmem
  unfold normalizedCofactorWeightRat
  rw [mul_assoc, moebius_mul_cast_rat_of_coprime hcop, hprod]

/-- The normalized sum over every ordered coprime product fiber equals the Möbius value. -/
theorem normalizedFiber_eq_moebius_rat (m : ℕ) :
    ∑ p ∈ orderedCoprimeFactorPairs m,
        normalizedCofactorWeightRat p.1 p.2 =
      (((μ m : ℤ) : ℚ)) := by
  by_cases hm0 : m = 0
  · subst m
    simp [orderedCoprimeFactorPairs]
  · by_cases hmu : μ m = 0
    · have hmuRat : (((μ m : ℤ) : ℚ)) = 0 := by simp [hmu]
      rw [hmuRat]
      apply Finset.sum_eq_zero
      intro p hp
      rw [normalizedCofactorWeightRat_eq_on_fiber hp]
      simp [hmu]
    · have hsq : Squarefree m :=
        ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmu
      calc
        (∑ p ∈ orderedCoprimeFactorPairs m,
            normalizedCofactorWeightRat p.1 p.2) =
            ∑ _p ∈ orderedCoprimeFactorPairs m,
              alphaWeightRat m * (((μ m : ℤ) : ℚ)) := by
          apply Finset.sum_congr rfl
          intro p hp
          exact normalizedCofactorWeightRat_eq_on_fiber hp
        _ = ((orderedCoprimeFactorPairs m).card : ℚ) *
              (alphaWeightRat m * (((μ m : ℤ) : ℚ))) := by
          simp
        _ = (((μ m : ℤ) : ℚ)) := by
          rw [orderedCoprimeFactorPairs_card_of_squarefree m hsq]
          unfold alphaWeightRat
          push_cast
          field_simp

/-- The fibered normalized expansion is exactly the rational Mertens sum. -/
theorem normalizedFiberExpansion_eq_mertens_rat (Q : ℕ) :
    normalizedFiberExpansionRat Q = mertensSummatoryRat Q := by
  unfold normalizedFiberExpansionRat mertensSummatoryRat
  apply Finset.sum_congr rfl
  intro m _
  exact normalizedFiber_eq_moebius_rat m

/-- Cast bridge from the rational companion to the existing complex Mertens sum. -/
theorem mertensSummatoryRat_cast (Q : ℕ) :
    ((mertensSummatoryRat Q : ℚ) : ℂ) =
      RHLean.Analysis.mertensSummatory Q := by
  simp [mertensSummatoryRat, RHLean.Analysis.mertensSummatory]

/-- The complex cast of the normalized fiber expansion equals the Analysis Mertens sum. -/
theorem normalizedFiberExpansion_cast_eq_mertens (Q : ℕ) :
    ((normalizedFiberExpansionRat Q : ℚ) : ℂ) =
      RHLean.Analysis.mertensSummatory Q := by
  rw [normalizedFiberExpansion_eq_mertens_rat, mertensSummatoryRat_cast]

/-- Multiplication by a new prime factor `3` increases the distinct-prime count by one. -/
theorem distinctPrimeCount_three_mul
    (n : ℕ) (h3 : ¬ 3 ∣ n) :
    distinctPrimeCount (3 * n) = distinctPrimeCount n + 1 := by
  have hcop : Nat.Coprime 3 n :=
    Nat.prime_three.coprime_iff_not_dvd.mpr h3
  unfold distinctPrimeCount
  rw [hcop.primeFactors_mul]
  rw [Finset.card_union_of_disjoint hcop.disjoint_primeFactors]
  simp [add_comm]

/-- Möbius changes sign when a new prime factor `3` is introduced. -/
theorem moebius_three_mul
    (c : ℕ) (h3 : ¬ 3 ∣ c) :
    (((μ (3 * c) : ℤ) : ℚ)) = -(((μ c : ℤ) : ℚ)) := by
  have hcop : Nat.Coprime 3 c :=
    Nat.prime_three.coprime_iff_not_dvd.mpr h3
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop]
  rw [ArithmeticFunction.moebius_apply_prime Nat.prime_three]
  push_cast
  ring

/-- The dyadic multiplicity weight is halved when a new prime factor `3` is introduced. -/
theorem alphaWeightRat_three_mul
    (n : ℕ) (h3 : ¬ 3 ∣ n) :
    alphaWeightRat (3 * n) = (1 / 2 : ℚ) * alphaWeightRat n := by
  unfold alphaWeightRat
  rw [distinctPrimeCount_three_mul n h3, pow_succ]
  field_simp <;> ring

/-- Tripling the lower cofactor scales the normalized arithmetic coefficient by `-1/2`. -/
theorem normalized_tripling_scaling_rat
    (c q : ℕ) (h3 : ¬ 3 ∣ c * q) :
    normalizedCofactorWeightRat (3 * c) q =
      -(1 / 2 : ℚ) * normalizedCofactorWeightRat c q := by
  have h3c : ¬ 3 ∣ c := by
    intro hc
    exact h3 (dvd_mul_of_dvd_left hc q)
  unfold normalizedCofactorWeightRat
  rw [mul_assoc 3 c q]
  rw [alphaWeightRat_three_mul (c * q) h3, moebius_three_mul c h3c]
  ring

/-- Complex-valued form of the exact normalized tripling scaling law. -/
theorem normalized_tripling_scaling
    (c q : ℕ) (h3 : ¬ 3 ∣ c * q) :
    normalizedCofactorWeight (3 * c) q =
      -(1 / 2 : ℂ) * normalizedCofactorWeight c q := by
  simpa [normalizedCofactorWeight] using
    congrArg (fun x : ℚ => (x : ℂ))
      (normalized_tripling_scaling_rat c q h3)

/-- Exact normalized cancellation identity in `ℚ`: child plus twice parent is zero. -/
theorem normalized_cancellation_identity_rat
    (c q : ℕ) (h3 : ¬ 3 ∣ c * q) :
    normalizedCofactorWeightRat c q +
        2 * normalizedCofactorWeightRat (3 * c) q = 0 := by
  rw [normalized_tripling_scaling_rat c q h3]
  ring

/-- Exact normalized cancellation identity in `ℂ`: child plus twice parent is zero. -/
theorem normalized_cancellation_identity
    (c q : ℕ) (h3 : ¬ 3 ∣ c * q) :
    normalizedCofactorWeight c q +
        2 * normalizedCofactorWeight (3 * c) q = 0 := by
  simpa [normalizedCofactorWeight] using
    congrArg (fun x : ℚ => (x : ℂ))
      (normalized_cancellation_identity_rat c q h3)

end RHLean.Proof
