import «research.HALF_ROOT_PRIME_PAIR_WEIGHT»

/-!
# Half-root prime-pair discrepancy

The explicit half-root pair weight is supported only at reciprocal depths one
and three.  This file separates those two physical shells without taking a
norm.  The complete two-prime correction is exactly

`topPairMass - bottomPairMass`.

Both masses are unsigned counts written in `ℤ`; the subtraction is retained
until the final endpoint identity.  This isolates a literal prime-pair
hyperbolic discrepancy as the only depth-two term.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

/-- Number, as an integer, of ordered high-prime pairs on reciprocal depth one. -/
def halfRootTopPrimePairMass (R : ℕ) : ℤ :=
  ∑ p ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (squareRootEndpoint R),
    ∑ q ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (p - 1),
      if squareRootEndpoint R / (p * q) = 1 then 1 else 0

/-- Number, as an integer, of ordered high-prime pairs on reciprocal depth three. -/
def halfRootBottomPrimePairMass (R : ℕ) : ℤ :=
  ∑ p ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (squareRootEndpoint R),
    ∑ q ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (p - 1),
      if squareRootEndpoint R / (p * q) = 3 then 1 else 0

/-- The signed pair shell is exactly top count minus bottom count. -/
theorem halfRoot_primePairWeightSum_eq_top_sub_bottom
    (R : ℕ) :
    (∑ p ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (squareRootEndpoint R),
        ∑ q ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (p - 1),
          halfRootPrimePairWeight R p q) =
      halfRootTopPrimePairMass R - halfRootBottomPrimePairMass R := by
  unfold halfRootTopPrimePairMass halfRootBottomPrimePairMass
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  unfold halfRootPrimePairWeight
  by_cases h1 : squareRootEndpoint R / (p * q) = 1
  · simp [h1]
  by_cases h3 : squareRootEndpoint R / (p * q) = 3
  · simp [h1, h3]
  · simp [h1, h3]

/-- **Prime-pair discrepancy normal form.**  The depth-two correction in the
half-root proper-subwheel identity is now a difference of two positive
hyperbolic prime-pair populations.  Crucially this difference is kept signed;
there is no triangle inequality between the two shells. -/
theorem squareRootProperSubwheelFrozenCorrelation_eq_halfRootPairDiscrepancy
    (R : ℕ) (hR : 6 ≤ R) :
    squareRootProperSubwheelFrozenCorrelation R (R / 2) =
      frozenPrimeUniverseMass (primesUpTo (R / 2)) (squareRootEndpoint R) -
        (∑ p ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (squareRootEndpoint R),
          frozenPrimeUniverseMass (primesUpTo (R / 2))
            (squareRootEndpoint R / p)) +
        (halfRootTopPrimePairMass R - halfRootBottomPrimePairMass R) := by
  rw [squareRootProperSubwheelFrozenCorrelation_eq_halfRootPrimePairShell R hR,
    halfRoot_primePairWeightSum_eq_top_sub_bottom]

end RHLean.Proof
