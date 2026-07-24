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

/-- Cast bridge from the rational companion to the existing complex Mertens sum. -/
theorem mertensSummatoryRat_cast (Q : ℕ) :
    ((mertensSummatoryRat Q : ℚ) : ℂ) =
      RHLean.Analysis.mertensSummatory Q := by
  simp [mertensSummatoryRat, RHLean.Analysis.mertensSummatory]

end RHLean.Proof
