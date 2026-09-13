import Mathlib
import RHLean.Analysis.PrimeDilateTransportCompression
import RHLean.Analysis.LogWeightedPrimeExtension

/-!
# The logarithmic square correction is a q^2-and-deeper Mertens tower

The log-weighted prime-extension route separates fresh prime extensions from
square-producing collisions.  For a fixed prime `p`, a square-producing parent
is divisible by `p`; writing it as `p*d` puts the child at `p^2*d`.

The repository already proves the exact complete-prefix identity

```text
M(B) = P_p(B) - P_p(B/p),
```

where `P_p(B)` is the Mobius mass of positive cofactors through `B` that are
free of `p`.  This file records the immediate consequence needed by the current
post-#685 Mellin route:

```text
P_p(B) = M(B) + P_p(B/p).
```

Taking differences between two cutoffs gives

```text
Delta P_p(A,B)
  = Delta M(A,B) + Delta P_p(A/p,B/p).
```

Thus a square-correction block whose first cutoff is already `N/p^2` is a
literal `p^2` Mertens daughter plus a remainder at `p^3`; iterating leaves only
`p^2,p^3,...` scales.  There is no first-power `N/p` term hidden in the square
correction.

No norm, PNT estimate, or RH-scale hypothesis occurs here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

/-- Mobius mass of the positive prefix through `B` after deleting multiples of
`p`.  This is the exact `p`-free potential naturally produced by one
square-collision reindexing. -/
def canonicalPrimeFreeMobiusPrefixMass (p B : ℕ) : ℂ :=
  ∑ d ∈ primeFreeCofactorPrefix p B, canonicalMoebiusWeight d

/-- Signed `p`-free block mass between two prefix cutoffs. -/
def canonicalPrimeFreeMobiusBlockMass (p A B : ℕ) : ℂ :=
  canonicalPrimeFreeMobiusPrefixMass p B -
    canonicalPrimeFreeMobiusPrefixMass p A

/-- Signed ordinary Mobius block mass between two prefix cutoffs. -/
def canonicalMobiusBlockMass (A B : ℕ) : ℂ :=
  cofactorMobiusPrefixMass B - cofactorMobiusPrefixMass A

/-- **One exact prime-power peel.**  The `p`-free potential is the full Mobius
prefix plus the same `p`-free potential after one more division by `p`.

This is just the already-compiled arbitrary-prime cofactor compression read in
the opposite direction. -/
theorem canonicalPrimeFreeMobiusPrefixMass_eq_mertens_add_div
    (p B : ℕ) (hp : p.Prime) :
    canonicalPrimeFreeMobiusPrefixMass p B =
      cofactorMobiusPrefixMass B +
        canonicalPrimeFreeMobiusPrefixMass p (B / p) := by
  have hboundary := cofactorMobiusPrefixMass_eq_primeCofactorBoundaryMass p B hp
  have hsubset := primeFreeCofactorPrefix_div_subset p B
  have hpartition :
      (∑ d ∈ primeFreeCofactorPrefix p B \
          primeFreeCofactorPrefix p (B / p), canonicalMoebiusWeight d) +
        (∑ d ∈ primeFreeCofactorPrefix p (B / p), canonicalMoebiusWeight d) =
      ∑ d ∈ primeFreeCofactorPrefix p B, canonicalMoebiusWeight d :=
    Finset.sum_sdiff hsubset
  unfold canonicalPrimeFreeMobiusPrefixMass
  unfold primeCofactorBoundaryMass at hboundary
  unfold primeCofactorBoundary at hboundary
  rw [← hboundary] at hpartition
  exact hpartition.symm

/-- **Block form of the prime-power peel.**  Every `p`-free block is one full
Mobius block plus the same `p`-free block one scale deeper. -/
theorem canonicalPrimeFreeMobiusBlockMass_eq_mertensBlock_add_deeper
    (p A B : ℕ) (hp : p.Prime) :
    canonicalPrimeFreeMobiusBlockMass p A B =
      canonicalMobiusBlockMass A B +
        canonicalPrimeFreeMobiusBlockMass p (A / p) (B / p) := by
  unfold canonicalPrimeFreeMobiusBlockMass canonicalMobiusBlockMass
  rw [canonicalPrimeFreeMobiusPrefixMass_eq_mertens_add_div p B hp,
    canonicalPrimeFreeMobiusPrefixMass_eq_mertens_add_div p A hp]
  ring

/-- The first square-dilated specialization: a `p`-free block at scale `p^2`
is an ordinary q^2 Mertens block plus a p-free q^3 remainder. -/
theorem canonicalPrimeFreeQ2Block_eq_mertensQ2Block_add_q3Remainder
    (N p : ℕ) (hp : p.Prime) :
    canonicalPrimeFreeMobiusBlockMass p
        (N / (p * p)) ((2 * N) / (p * p)) =
      canonicalMobiusBlockMass
          (N / (p * p)) ((2 * N) / (p * p)) +
        canonicalPrimeFreeMobiusBlockMass p
          ((N / (p * p)) / p) (((2 * N) / (p * p)) / p) := by
  exact canonicalPrimeFreeMobiusBlockMass_eq_mertensBlock_add_deeper
    p (N / (p * p)) ((2 * N) / (p * p)) hp

/-- The q^3 remainder can be written with a single denominator `p^3`; this is
only floor arithmetic. -/
theorem canonicalPrimeFreeQ2Block_eq_mertensQ2Block_add_q3Remainder_pow
    (N p : ℕ) (hp : p.Prime) :
    canonicalPrimeFreeMobiusBlockMass p
        (N / (p * p)) ((2 * N) / (p * p)) =
      canonicalMobiusBlockMass
          (N / (p * p)) ((2 * N) / (p * p)) +
        canonicalPrimeFreeMobiusBlockMass p
          (N / ((p * p) * p)) ((2 * N) / ((p * p) * p)) := by
  rw [canonicalPrimeFreeQ2Block_eq_mertensQ2Block_add_q3Remainder N p hp]
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]

end RHLean.Proof
