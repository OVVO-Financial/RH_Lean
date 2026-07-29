import Mathlib
import RHLean.Analysis.PrimeBoundaryDefectBridge
import RHLean.Proof.RealSquareBlockIncrements

/-!
# Concrete fixed-prime defects for square blocks

This module instantiates the abstract prime-coordinate bridge with an explicit
finite parent sum for a square block.  For a prime `q`, the defect is

```text
sum_c μ(c) (1_I(c) - 1_I(cq)),
```

where `c` ranges over a finite prefix large enough to contain every parent that
can meet the block.  The only nontrivial arithmetic input is the exact
partition of the block into `q`-free endpoints and endpoints containing one
copy of `q`; endpoints containing `q^2` have Möbius value zero.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

/-- Upper endpoint of the square block `[m²,(m+1)²)`. -/
def squareBlockUpper (m : ℕ) : ℕ :=
  (m + 1) ^ 2

/-- Finite parent carrier sufficient for a fixed-prime defect of block `m`.
Every parent occurring either directly in the block or through a child `c*q`
in the block is strictly below the block's upper endpoint. -/
def squareBlockParentCarrier (m : ℕ) : Finset ℕ :=
  Finset.range (squareBlockUpper m)

/-- Explicit fixed-prime boundary defect for square block `m`. -/
def concretePrimeBoundaryDefect (m q : ℕ) : ℤ :=
  ∑ c ∈ squareBlockParentCarrier m with ¬ q ∣ c,
    μ c *
      (windowIndicator (canonicalSquareBlock m) c -
        windowIndicator (canonicalSquareBlock m) (c * q))

/-- The direct integer-valued Möbius increment of square block `m`. -/
def integerSquareBlockIncrement (m : ℕ) : ℤ :=
  ∑ n ∈ canonicalSquareBlock m, μ n

/-- Compatibility with the existing real square-block increment. -/
theorem integerSquareBlockIncrement_cast_real (m : ℕ) :
    ((integerSquareBlockIncrement m : ℤ) : ℝ) =
      realCanonicalTotalIncrement m := by
  classical
  simp [integerSquareBlockIncrement, realCanonicalTotalIncrement,
    realCanonicalMoebiusWeight]

/-- Every endpoint of the square block lies in the finite parent carrier. -/
theorem mem_squareBlockParentCarrier_of_mem_block
    {m n : ℕ} (hn : n ∈ canonicalSquareBlock m) :
    n ∈ squareBlockParentCarrier m := by
  have h := (Finset.mem_Ico.mp hn).2
  simpa [squareBlockParentCarrier, squareBlockUpper] using h

/-- Every parent whose child lies in the block also lies in the finite carrier,
provided the prime coordinate is nonzero. -/
theorem mem_squareBlockParentCarrier_of_mul_mem_block
    {m c q : ℕ} (hq : 0 < q)
    (hcq : c * q ∈ canonicalSquareBlock m) :
    c ∈ squareBlockParentCarrier m := by
  have hupper : c * q < squareBlockUpper m := by
    simpa [canonicalSquareBlock, squareBlockUpper] using
      (Finset.mem_Ico.mp hcq).2
  have hc_le : c ≤ c * q := by
    have hq1 : 1 ≤ q := hq
    simpa using Nat.mul_le_mul_left c hq1
  have hc_lt : c < squareBlockUpper m := lt_of_le_of_lt hc_le hupper
  simpa [squareBlockParentCarrier] using hc_lt

/-- Typed exact arithmetic target for a concrete fixed-prime coordinate.

The proof is the finite reindexing step: split the block into `q ∤ n`,
`q ∣ n ∧ q² ∤ n`, and `q² ∣ n`; reindex the middle class by `n=cq`; the final
class has Möbius value zero.  This statement is separated so pinned-mathlib
bijection details remain isolated from the rest of the architecture. -/
def ConcretePrimeBoundaryIdentityStatement : Prop :=
  ∀ m q : ℕ, q.Prime →
    concretePrimeBoundaryDefect m q = integerSquareBlockIncrement m

/-- Once the finite reindexing identity is supplied, the concrete defects form
an exact prime-boundary family over any finite prime set. -/
def concreteExactPrimeBoundaryFamily
    (hidentity : ConcretePrimeBoundaryIdentityStatement)
    (m : ℕ) (P : Finset ℕ)
    (hP : ∀ q ∈ P, q.Prime) :
    ExactPrimeBoundaryFamily P (integerSquareBlockIncrement m) where
  defect := concretePrimeBoundaryDefect m
  exact_on_primes := by
    intro q hq
    exact ⟨hP q hq, hidentity m q (hP q hq)⟩

/-- Raw aggregation over concrete prime coordinates duplicates the block
increment once per prime coordinate. -/
theorem sum_concretePrimeBoundaryDefect_eq_card_mul
    (hidentity : ConcretePrimeBoundaryIdentityStatement)
    (m : ℕ) (P : Finset ℕ)
    (hP : ∀ q ∈ P, q.Prime) :
    ∑ q ∈ P, concretePrimeBoundaryDefect m q =
      (P.card : ℤ) * integerSquareBlockIncrement m := by
  exact
    (concreteExactPrimeBoundaryFamily hidentity m P hP).sum_defect_eq_card_mul

/-- Exact concrete second-moment identity. -/
theorem sum_sq_concretePrimeBoundaryDefect_eq_card_mul_sq
    (hidentity : ConcretePrimeBoundaryIdentityStatement)
    (m : ℕ) (P : Finset ℕ)
    (hP : ∀ q ∈ P, q.Prime) :
    ∑ q ∈ P, (concretePrimeBoundaryDefect m q) ^ 2 =
      (P.card : ℤ) * (integerSquareBlockIncrement m) ^ 2 := by
  exact
    (concreteExactPrimeBoundaryFamily hidentity m P hP).sum_sq_defect_eq_card_mul_sq

/-- The unique canonical block total and every concrete fixed-prime coordinate
are two representations of the same integer increment. -/
def concreteCanonicalAndBoundaryBridge
    (hidentity : ConcretePrimeBoundaryIdentityStatement)
    (m : ℕ) (P : Finset ℕ)
    (hP : ∀ q ∈ P, q.Prime) :
    CanonicalAndBoundaryBridge P where
  increment := integerSquareBlockIncrement m
  canonicalContribution := integerSquareBlockIncrement m
  canonical_eq_increment := rfl
  boundaryFamily := concreteExactPrimeBoundaryFamily hidentity m P hP

/-- General proper-parent ceiling for a square block.  If `n=cq` lies below the
upper square and `q≥2`, then `c` is at most half of the largest possible child. -/
theorem parent_le_half_squareBlockUpper
    {m c q n : ℕ} (hq : 2 ≤ q) (hprod : c * q = n)
    (hn : n < squareBlockUpper m) :
    2 * c < squareBlockUpper m := by
  have htwo : c * 2 ≤ c * q := Nat.mul_le_mul_left c hq
  rw [Nat.mul_comm c 2, hprod] at htwo
  exact lt_of_le_of_lt htwo hn

/-- Concrete specialization: the block `[100,121)` needs no proper parent
beyond the completed square frontier `64`. -/
example {c q n : ℕ} (hq : 2 ≤ q) (hprod : c * q = n)
    (hn : n < 121) : c < 64 := by
  exact parent_lt_sixtyFour_of_mem_block_100_121 hq hprod hn

end RHLean.Analysis
