import Mathlib
import RHLean.Proof.CanonicalRoughBoundaryProfileAbelReturn
import RHLean.Proof.CanonicalRoughTruncatedWheelManyPrimeTelescope

/-!
# Physical unweighted columns land on the Abel primitive

The literal physical fixed-`q` columns carry `mu(c)/c` and no `1/q`, so the
truncated Euler recurrence turns each of them into `q` times a discrete drop of
the canonical reciprocal boundary profile rather than into a telescoping
increment.  `CanonicalRoughTruncatedWheelManyPrimeTelescope` proves that
column-by-column, and `CanonicalRoughBoundaryProfileAbelReturn` closes the
resulting prime-weighted variation by finite summation by parts.

This file composes the two, so the physical column aggregate is identified
outright with the signed Abel primitive

```text
A_X(K) = sum_{n < K} B_n(X) - K * B_K(X).
```

Both a full prefix and a half-open prime band are covered, and the band form is
the one the physical ranges need: a post-root escape column runs over `q > R`
against the square endpoint, so it returns `A_{X_R}(X_R) - A_{X_R}(R)`, while a
birth column runs against the lower global cutoff and returns the corresponding
difference of `A_{R-1}`.  The profile is parameterized by the truncation, so a
single band theorem covers both orientations.

Nothing here is normed.  The whole point of routing through the primitive is
that the signed cancellation survives to the physical carriers, so no absolute
value is taken anywhere in this file.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

/-- **The physical unweighted column aggregate is the Abel primitive.**  This is
the composition of the unweighted-column law with the finite Abel return: the
literal `mu(c)/c`-weighted physical columns, summed over a complete prime
prefix, are exactly the signed primitive of the boundary profile. -/
theorem physicalUnweightedColumn_eq_abelPrimitive (X K : ℕ) :
    (∑ q ∈ primesUpTo K,
      (primorialTruncatedSignedReciprocalCube (primesUpTo (q - 1)) (X / q) -
        primorialSignedContractionFactor (primesUpTo (q - 1)))) =
      primorialTruncatedWheelAbelPrimitive X K := by
  rw [primorialTruncatedBoundary_unweightedUpperColumn_eq_primeWeightedDrops X K]
  exact primorialTruncatedBoundary_primeWeightedDrops_eq_abelPrimitive X K

/-- **Interval form.**  Over a half-open prime band the same aggregate returns
the difference of the two primitives at the band endpoints.  This is the shape
a physical range such as `q > R` produces. -/
theorem physicalUnweightedColumn_primeBand_eq_abelPrimitive_sub
    (X : ℕ) {K₀ K₁ : ℕ} (hK : K₀ ≤ K₁) :
    (∑ q ∈ primesUpTo K₁ \ primesUpTo K₀,
      (primorialTruncatedSignedReciprocalCube (primesUpTo (q - 1)) (X / q) -
        primorialSignedContractionFactor (primesUpTo (q - 1)))) =
      primorialTruncatedWheelAbelPrimitive X K₁ -
        primorialTruncatedWheelAbelPrimitive X K₀ := by
  have hcongr :
      (∑ q ∈ primesUpTo K₁ \ primesUpTo K₀,
        (primorialTruncatedSignedReciprocalCube (primesUpTo (q - 1)) (X / q) -
          primorialSignedContractionFactor (primesUpTo (q - 1)))) =
        ∑ q ∈ primesUpTo K₁ \ primesUpTo K₀,
          (q : ℝ) *
            (primorialTruncatedWheelBoundaryProfile X (q - 1) -
              primorialTruncatedWheelBoundaryProfile X q) := by
    refine Finset.sum_congr rfl ?_
    intro q hq
    exact primorialTruncatedBoundary_unweightedColumn_eq_prime_mul_boundaryDrop
      X (mem_primesUpTo_sdiff.mp hq).1
  rw [hcongr]
  exact primorialTruncatedBoundary_primeBand_eq_abelPrimitive_sub X hK

/-! ## The post-root orientation -/

/-- The square endpoint dominates the root once the root scale is at least two. -/
theorem le_squareRootEndpoint_self {R : ℕ} (hR : 2 ≤ R) :
    R ≤ squareRootEndpoint R := by
  unfold squareRootEndpoint
  have h : R * 2 ≤ R * R := Nat.mul_le_mul (le_refl R) hR
  rw [pow_two]
  omega

/-- **Post-root physical column aggregate.**  Summing the literal physical
columns over the complete external prime range `R < q <= X_R`, against the
square endpoint, returns exactly the interval Abel primitive
`A_{X_R}(X_R) - A_{X_R}(R)`.  No norm is taken, so the signed cancellation
inside the external range is still available to the external-terminal carrier. -/
theorem physicalPostRootColumn_eq_abelPrimitive_sub {R : ℕ} (hR : 2 ≤ R) :
    (∑ q ∈ primesUpTo (squareRootEndpoint R) \ primesUpTo R,
      (primorialTruncatedSignedReciprocalCube (primesUpTo (q - 1))
          (squareRootEndpoint R / q) -
        primorialSignedContractionFactor (primesUpTo (q - 1)))) =
      primorialTruncatedWheelAbelPrimitive (squareRootEndpoint R)
          (squareRootEndpoint R) -
        primorialTruncatedWheelAbelPrimitive (squareRootEndpoint R) R :=
  physicalUnweightedColumn_primeBand_eq_abelPrimitive_sub
    (squareRootEndpoint R) (le_squareRootEndpoint_self hR)

/-! ## The birth orientation -/

/-- **Birth physical column aggregate.**  The birth channel runs against the
lower global cutoff `R - 1` rather than the square endpoint, so the same band
theorem applies with that truncation and returns a difference of `A_{R-1}`.
Only the truncation argument changes; the mechanism is identical. -/
theorem physicalBirthColumn_eq_abelPrimitive_sub
    (R : ℕ) {K₀ K₁ : ℕ} (hK : K₀ ≤ K₁) :
    (∑ q ∈ primesUpTo K₁ \ primesUpTo K₀,
      (primorialTruncatedSignedReciprocalCube (primesUpTo (q - 1))
          ((R - 1) / q) -
        primorialSignedContractionFactor (primesUpTo (q - 1)))) =
      primorialTruncatedWheelAbelPrimitive (R - 1) K₁ -
        primorialTruncatedWheelAbelPrimitive (R - 1) K₀ :=
  physicalUnweightedColumn_primeBand_eq_abelPrimitive_sub (R - 1) hK

/-- **The signed post-root minus birth aggregate.**  Both physical orientations
resolve into interval Abel primitives at their own truncations, and their
difference is carried entirely by the four signed endpoint values.  This is the
identity the external-terminal and Go/root carriers have to be rotated into;
nothing has been normed on the way here. -/
theorem physicalPostRoot_sub_physicalBirth_eq_abelPrimitive_difference
    {R : ℕ} (hR : 2 ≤ R) {K₀ K₁ : ℕ} (hK : K₀ ≤ K₁) :
    ((∑ q ∈ primesUpTo (squareRootEndpoint R) \ primesUpTo R,
        (primorialTruncatedSignedReciprocalCube (primesUpTo (q - 1))
            (squareRootEndpoint R / q) -
          primorialSignedContractionFactor (primesUpTo (q - 1)))) -
      (∑ q ∈ primesUpTo K₁ \ primesUpTo K₀,
        (primorialTruncatedSignedReciprocalCube (primesUpTo (q - 1))
            ((R - 1) / q) -
          primorialSignedContractionFactor (primesUpTo (q - 1))))) =
      (primorialTruncatedWheelAbelPrimitive (squareRootEndpoint R)
            (squareRootEndpoint R) -
          primorialTruncatedWheelAbelPrimitive (squareRootEndpoint R) R) -
        (primorialTruncatedWheelAbelPrimitive (R - 1) K₁ -
          primorialTruncatedWheelAbelPrimitive (R - 1) K₀) := by
  rw [physicalPostRootColumn_eq_abelPrimitive_sub hR,
    physicalBirthColumn_eq_abelPrimitive_sub R hK]

end RHLean.Proof
