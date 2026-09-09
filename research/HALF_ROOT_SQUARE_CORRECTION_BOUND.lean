import «research.HALF_ROOT_PAIR_COLUMN_CANCELLATION»

/-!
# Root-scale bound for the collapsed half-root square correction

`HALF_ROOT_PAIR_COLUMN_CANCELLATION` consumes the full two-prime shell inside
the common one-prime column.  Its only depth-two residue is

`halfRootPrimeSquareCorrection R = sum_{p>R/2} M(X_R/p^2)`.

This file proves that residue is already at the physical root scale.  Owners
`p > R` contribute zero because `p^2 > X_R`; the remaining owners lie in the
one-dimensional interval `(R/2,R]`, and every four-state square weight has
absolute value at most one.  Hence the entire correction is bounded by `R+1`
without PNT or any Mertens estimate.

So the pair/column cancellation really does change dimension and exponent: the
two-prime population from #607 is absorbed, and what it leaves behind is an
`O(R)` term at `X_R = R^2-1`.  The only remaining non-root-scale question is the
signed coupling of the common frozen base with the moving boundary column.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

/-- The square correction is supported only on owners at or below the physical
root. -/
theorem halfRootPrimeSquareCorrection_eq_middleSum
    (R : ℕ) (hR : 6 ≤ R) :
    halfRootPrimeSquareCorrection R =
      ∑ p ∈ frozenPrimeUniverseHighPrimeSet (R / 2) R,
        halfRootPrimeSquareWeight R p := by
  unfold halfRootPrimeSquareCorrection
  have hRX : R ≤ squareRootEndpoint R := by
    have hquad : R + 1 ≤ R ^ 2 := by nlinarith
    unfold squareRootEndpoint
    omega
  have hsub :
      frozenPrimeUniverseHighPrimeSet (R / 2) R ⊆
        frozenPrimeUniverseHighPrimeSet (R / 2) (squareRootEndpoint R) := by
    intro p hp
    have hpData := mem_frozenPrimeUniverseHighPrimeSet.mp hp
    exact mem_frozenPrimeUniverseHighPrimeSet.mpr
      ⟨hpData.1, hpData.2.1, hpData.2.2.trans hRX⟩
  symm
  refine Finset.sum_subset hsub ?_
  intro p hpFull hpNotMiddle
  have hpData := mem_frozenPrimeUniverseHighPrimeSet.mp hpFull
  have hRp : R < p := by
    by_contra hnot
    have hpR : p ≤ R := Nat.le_of_not_gt hnot
    apply hpNotMiddle
    exact mem_frozenPrimeUniverseHighPrimeSet.mpr
      ⟨hpData.1, hpData.2.1, hpR⟩
  exact halfRootPrimeSquareWeight_eq_zero_of_root_lt (by omega) hRp

/-- The number of possible nonzero square-correction owners is at most the
size of the ambient integer range `0,...,R`. -/
theorem card_halfRootMiddlePrimeSet_le_root_add_one
    (R : ℕ) :
    (frozenPrimeUniverseHighPrimeSet (R / 2) R).card ≤ R + 1 := by
  have hsub :
      frozenPrimeUniverseHighPrimeSet (R / 2) R ⊆ Finset.range (R + 1) := by
    intro p hp
    have hpData := mem_frozenPrimeUniverseHighPrimeSet.mp hp
    exact Finset.mem_range.mpr (by omega)
  have hcard := Finset.card_le_card hsub
  simpa using hcard

/-- **The collapsed square correction is root-scale.**

No prime-count estimate is used: support has at most `R+1` integer sites and
every signed atom has size at most one. -/
theorem abs_halfRootPrimeSquareCorrection_le_root_add_one
    (R : ℕ) (hR : 6 ≤ R) :
    |halfRootPrimeSquareCorrection R| ≤ (R + 1 : ℤ) := by
  rw [halfRootPrimeSquareCorrection_eq_middleSum R hR]
  calc
    |∑ p ∈ frozenPrimeUniverseHighPrimeSet (R / 2) R,
        halfRootPrimeSquareWeight R p| ≤
      ∑ p ∈ frozenPrimeUniverseHighPrimeSet (R / 2) R,
        |halfRootPrimeSquareWeight R p| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ frozenPrimeUniverseHighPrimeSet (R / 2) R, (1 : ℤ) := by
      apply Finset.sum_le_sum
      intro p _hp
      exact abs_halfRootPrimeSquareWeight_le_one R p
    _ = ((frozenPrimeUniverseHighPrimeSet (R / 2) R).card : ℤ) := by simp
    _ ≤ (R + 1 : ℤ) := by
      exact_mod_cast card_halfRootMiddlePrimeSet_le_root_add_one R

/-- The common frozen base minus the moving chronological boundary is the
coupled core left after the explicit pair cancellation. -/
def halfRootBoundaryCoupledCore (R : ℕ) : ℤ :=
  frozenPrimeUniverseMass (primesUpTo (R / 2)) (squareRootEndpoint R) -
    halfRootMovingBoundaryColumn R

/-- **Exponent-changing handoff.**  The exact square-endpoint Mertens
correlation differs from the coupled base/boundary core by at most `R+1`.
Thus the entire explicit prime-pair layer of #607 has been reduced to an
RH-scale additive remainder; any remaining exponent improvement must now come
from the signed base/boundary coupling itself, not from the pair shell. -/
theorem abs_squareRootProperSubwheelFrozenCorrelation_sub_halfRootBoundaryCoupledCore_le_root_add_one
    (R : ℕ) (hR : 6 ≤ R) :
    |squareRootProperSubwheelFrozenCorrelation R (R / 2) -
        halfRootBoundaryCoupledCore R| ≤ (R + 1 : ℤ) := by
  have hmain :=
    squareRootProperSubwheelFrozenCorrelation_eq_halfRootBoundary_sub_squareCorrection
      R hR
  have hdiff :
      squareRootProperSubwheelFrozenCorrelation R (R / 2) -
          halfRootBoundaryCoupledCore R =
        -halfRootPrimeSquareCorrection R := by
    rw [hmain]
    unfold halfRootBoundaryCoupledCore
    ring
  rw [hdiff, abs_neg]
  exact abs_halfRootPrimeSquareCorrection_le_root_add_one R hR

end RHLean.Proof
