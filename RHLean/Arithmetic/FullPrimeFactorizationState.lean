import Mathlib

/-!
# Full prime-factorization semantics for Möbius parity

This module is the semantic guardrail for every parent/cofactor construction in
`RH_Lean`.

A product display `n = c * q` is a transport edge between two distinct natural
numbers.  It is **not** a two-prime factorization unless both `c` and `q` are
prime.  Möbius parity is always computed from the complete prime factorization
of `n`, with multiplicity exposed.

For example, `102 = 6 * 17` is a valid transport edge, but the complete prime
factorization is `102 = 2 * 3 * 17`.  Hence its full factor depth is three, not
two.  The parent `6` and child `102` remain different Möbius arguments.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Arithmetic

/-- Complete prime-factor depth, counting prime factors with multiplicity.

This is the arithmetic-function `Ω(n)`.  It must not be replaced by the number
of visible factors in a compressed product such as `n = c * q`. -/
def fullPrimeFactorDepth (n : ℕ) : ℕ :=
  ArithmeticFunction.cardFactors n

/-- Distinct prime-factor depth `ω(n)`.  On squarefree integers this agrees with
`fullPrimeFactorDepth`; outside the squarefree support it does not determine the
Möbius value by parity. -/
def distinctPrimeFactorDepth (n : ℕ) : ℕ :=
  ArithmeticFunction.cardDistinctFactors n

/-- The complete set of distinct primes occurring in the factorization of `n`.
Multiplicity is separately retained by `fullPrimeFactorDepth`. -/
def fullPrimeSupport (n : ℕ) : Finset ℕ :=
  n.primeFactors

/-- On the squarefree support, Möbius is exactly parity of the complete prime
factorization depth. -/
theorem moebius_eq_negOnePow_fullPrimeFactorDepth
    {n : ℕ} (hsq : Squarefree n) :
    μ n = (-1 : ℤ) ^ fullPrimeFactorDepth n := by
  simpa [fullPrimeFactorDepth] using
    ArithmeticFunction.moebius_apply_of_squarefree hsq

/-- Repeated prime factors force Möbius value zero. -/
theorem moebius_eq_zero_of_not_squarefree_fullState
    {n : ℕ} (hsq : ¬ Squarefree n) :
    μ n = 0 :=
  ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq

/-- For a squarefree integer, the product of the complete prime support is the
integer itself.  This is the formal statement that the factorization must be
fully expanded into primes before parity is read. -/
theorem prod_fullPrimeSupport_eq
    {n : ℕ} (hsq : Squarefree n) :
    ∏ p ∈ fullPrimeSupport n, p = n := by
  simpa [fullPrimeSupport] using Nat.prod_primeFactors_of_squarefree hsq

/-- On squarefree integers, complete factor depth and distinct-prime depth
coincide. -/
theorem fullPrimeFactorDepth_eq_distinctPrimeFactorDepth
    {n : ℕ} (hsq : Squarefree n) :
    fullPrimeFactorDepth n = distinctPrimeFactorDepth n := by
  have hn0 : n ≠ 0 := hsq.ne_zero
  symm
  simpa [fullPrimeFactorDepth, distinctPrimeFactorDepth] using
    (ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree hn0).2 hsq

/-- A compressed product record is only a transport statement.  The parent and
child are separate Möbius arguments, and this structure deliberately contains
no factor-depth field. -/
structure PrimeTransportEdge where
  parent : ℕ
  terminal : ℕ
  terminal_prime : terminal.Prime
  child : ℕ
  product_eq : parent * terminal = child

namespace PrimeTransportEdge

/-- A fresh transport edge flips the Möbius value.  This theorem is a recurrence
between two complete arithmetic states; it does not count `parent` as one prime
factor. -/
theorem moebius_child_eq_neg_parent
    (e : PrimeTransportEdge) (hfresh : ¬ e.terminal ∣ e.parent) :
    μ e.child = -μ e.parent := by
  have hcop : Nat.Coprime e.parent e.terminal :=
    (e.terminal_prime.coprime_iff_not_dvd).2 hfresh |>.symm
  calc
    μ e.child = μ (e.parent * e.terminal) := by rw [e.product_eq]
    _ = μ e.parent * μ e.terminal :=
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
    _ = μ e.parent * (-1) := by
      rw [ArithmeticFunction.moebius_apply_prime e.terminal_prime]
    _ = -μ e.parent := by ring

/-- If the terminal prime already occurs in the complete parent factorization,
the child contains a repeated prime and has Möbius value zero. -/
theorem moebius_child_eq_zero_of_collision
    (e : PrimeTransportEdge) (hcollision : e.terminal ∣ e.parent) :
    μ e.child = 0 := by
  obtain ⟨k, hk⟩ := hcollision
  have hsq : e.terminal * e.terminal ∣ e.child := by
    refine ⟨k, ?_⟩
    calc
      e.child = e.parent * e.terminal := e.product_eq.symm
      _ = (e.terminal * k) * e.terminal := by rw [hk]
      _ = (e.terminal * e.terminal) * k := by ac_rfl
  have hnot : ¬ Squarefree e.child := by
    intro hs
    exact e.terminal_prime.not_isUnit (hs e.terminal hsq)
  exact ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnot

end PrimeTransportEdge

/-- The finite square block `[m²,(m+1)²)`. -/
def fullFactorSquareBlock (m : ℕ) : Finset ℕ :=
  Finset.Ico (m ^ 2) ((m + 1) ^ 2)

/-- Nonzero Möbius support of a square block. -/
def fullFactorSquareBlockSupport (m : ℕ) : Finset ℕ :=
  (fullFactorSquareBlock m).filter fun n => μ n ≠ 0

/-- Full prime depths represented on the nonzero support of a square block. -/
def fullFactorSquareBlockDepthValues (m : ℕ) : Finset ℕ :=
  (fullFactorSquareBlockSupport m).image fullPrimeFactorDepth

/-- The squarefree population at complete prime depth `k`. -/
def fullFactorSquareBlockDepthFiber (m k : ℕ) : Finset ℕ :=
  (fullFactorSquareBlockSupport m).filter fun n => fullPrimeFactorDepth n = k

/-- Population count at complete prime depth `k`. -/
def fullFactorSquareBlockDepthCount (m k : ℕ) : ℕ :=
  (fullFactorSquareBlockDepthFiber m k).card

/-- Exact elementary depth-parity identity for a square block.

Every nonzero Möbius term is grouped by its complete prime-factor depth.  No
analytic estimate is used. -/
theorem squareBlockMoebius_eq_fullDepthParity (m : ℕ) :
    ∑ n ∈ fullFactorSquareBlock m, μ n =
      ∑ k ∈ fullFactorSquareBlockDepthValues m,
        (fullFactorSquareBlockDepthCount m k : ℤ) * (-1 : ℤ) ^ k := by
  classical
  have hmaps :
      ∀ n ∈ fullFactorSquareBlockSupport m,
        fullPrimeFactorDepth n ∈ fullFactorSquareBlockDepthValues m := by
    intro n hn
    exact Finset.mem_image.mpr ⟨n, hn, rfl⟩
  calc
    (∑ n ∈ fullFactorSquareBlock m, μ n) =
        ∑ n ∈ fullFactorSquareBlockSupport m, μ n := by
      unfold fullFactorSquareBlockSupport
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hμ : μ n = 0
      · simp [hμ]
      · simp [hμ]
    _ = ∑ n ∈ fullFactorSquareBlockSupport m,
          (-1 : ℤ) ^ fullPrimeFactorDepth n := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnData : n ∈ fullFactorSquareBlock m ∧ μ n ≠ 0 := by
        simpa [fullFactorSquareBlockSupport] using hn
      have hsq : Squarefree n :=
        ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hnData.2
      exact moebius_eq_negOnePow_fullPrimeFactorDepth hsq
    _ = ∑ k ∈ fullFactorSquareBlockDepthValues m,
          (fullFactorSquareBlockDepthCount m k : ℤ) * (-1 : ℤ) ^ k := by
      unfold fullFactorSquareBlockDepthCount fullFactorSquareBlockDepthFiber
      calc
        (∑ n ∈ fullFactorSquareBlockSupport m,
            (-1 : ℤ) ^ fullPrimeFactorDepth n) =
          ∑ k ∈ fullFactorSquareBlockDepthValues m,
            ∑ _n ∈ fullFactorSquareBlockSupport m with
                fullPrimeFactorDepth _n = k,
              (-1 : ℤ) ^ k := by
            simpa using
              (Finset.sum_fiberwise_of_maps_to'
                (s := fullFactorSquareBlockSupport m)
                (t := fullFactorSquareBlockDepthValues m)
                (g := fullPrimeFactorDepth)
                hmaps
                (fun k : ℕ => (-1 : ℤ) ^ k)).symm
        _ = ∑ k ∈ fullFactorSquareBlockDepthValues m,
              (((fullFactorSquareBlockSupport m).filter fun n =>
                  fullPrimeFactorDepth n = k).card : ℤ) * (-1 : ℤ) ^ k := by
            apply Finset.sum_congr rfl
            intro k hk
            simp

end RHLean.Arithmetic
