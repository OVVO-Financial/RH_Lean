import «research.HALF_ROOT_WEIGHTED_FIRST_JUMP»

/-!
# Recoupled half-root pair shell on the existing first-jump carrier

The previous file identifies each nonzero pair weight with the corresponding
upper-half first-jump state slice.  Summing that identity before taking any
norm gives a direct recoupling of the full pair shell to the established
Othello/first-jump carrier.

The key difference from the completed fixed-prime no-go is explicit here: the
state slice is multiplied by the reciprocal-depth coefficient
`halfRootPrimePairWeight R p q`.  That coefficient is retained all the way
through the carrier map.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

/-- The existing first-jump slice carrier with the half-root reciprocal-depth
coefficient left attached. -/
def halfRootWeightedFirstJumpShell (R : ℕ) : ℂ :=
  ∑ p ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (squareRootEndpoint R),
    ∑ q ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (p - 1),
      (((halfRootPrimePairWeight R p q : ℤ) : ℂ)) *
        signedFirstJumpPrimeStateSlice R q (1, p)

/-- **Global recoupling.**  The complete finite prime-pair shell is exactly the
negative weighted first-jump shell on the old carrier.  No incidence is counted
by absolute value and the depth coefficient is not discarded. -/
theorem halfRoot_pairWeightSum_cast_eq_neg_weightedFirstJumpShell
    (R : ℕ) (hR : 9 ≤ R) :
    (((∑ p ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (squareRootEndpoint R),
        ∑ q ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (p - 1),
          halfRootPrimePairWeight R p q : ℤ) : ℂ)) =
      -halfRootWeightedFirstJumpShell R := by
  unfold halfRootWeightedFirstJumpShell
  push_cast
  calc
    (∑ p ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (squareRootEndpoint R),
        ∑ q ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (p - 1),
          (((halfRootPrimePairWeight R p q : ℤ) : ℂ))) =
      ∑ p ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (squareRootEndpoint R),
        ∑ q ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (p - 1),
          -((((halfRootPrimePairWeight R p q : ℤ) : ℂ)) *
            signedFirstJumpPrimeStateSlice R q (1, p)) := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      exact halfRootPrimePairWeight_eq_neg_weighted_firstJumpSlice hR hp hq
    _ = ∑ p ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (squareRootEndpoint R),
        -(∑ q ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (p - 1),
          (((halfRootPrimePairWeight R p q : ℤ) : ℂ)) *
            signedFirstJumpPrimeStateSlice R q (1, p)) := by
      apply Finset.sum_congr rfl
      intro p _hp
      rw [Finset.sum_neg_distrib]
    _ = -(∑ p ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (squareRootEndpoint R),
        ∑ q ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (p - 1),
          (((halfRootPrimePairWeight R p q : ℤ) : ℂ)) *
            signedFirstJumpPrimeStateSlice R q (1, p)) := by
      rw [Finset.sum_neg_distrib]

end RHLean.Proof
