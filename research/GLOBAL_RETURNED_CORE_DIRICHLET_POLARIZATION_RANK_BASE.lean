import Mathlib
import «research.GLOBAL_RETURNED_CORE_DIRICHLET_PAIR_POLARIZATION»

/-!
# Rank-zero base of the Dirichlet polarization induction

A pair with no remaining fresh-prime coordinate is diagonal on squarefree
support.  The Dirichlet polarization is favorable there.

The physical AMP coefficient is nonnegative, and its Dirichlet zero extension
remains nonnegative.  Therefore

  Pi_p(a,a) = -2 ell(a) j_p(a) <= 0.

If the p-child is clipped then `j_p(a)=0`, so the diagonal atom is exactly zero.
This is the base case for the finite greatest-owner induction and introduces no
boundary constant.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Dirichlet extension preserves nonnegativity of the AMP scalar weight. -/
theorem lowOwnerPhysicalDirichletWeight_nonneg (R n : ℕ) :
    0 ≤ lowOwnerPhysicalDirichletWeight R n := by
  unfold lowOwnerPhysicalDirichletWeight
  split
  · exact lowOwnerZeroFrequencyMobiusWeight_nonneg R n
  · norm_num

/-- Base and returned-child signed sites have nonnegative product because they
carry the same Mobius sign. -/
theorem lowOwnerFirstOwnerDirichletBase_mul_returned_nonneg
    (R p a : ℕ) :
    0 ≤ lowOwnerFirstOwnerDirichletBaseSite R a *
      lowOwnerFirstOwnerDirichletReturnedChildSite R p a := by
  unfold lowOwnerFirstOwnerDirichletBaseSite
    lowOwnerFirstOwnerDirichletReturnedChildSite
    lowOwnerZeroFrequencyMobiusSite
  have hw : 0 ≤ lowOwnerZeroFrequencyMobiusWeight R a :=
    lowOwnerZeroFrequencyMobiusWeight_nonneg R a
  have hj : 0 ≤ lowOwnerPhysicalDirichletWeight R (p * a) :=
    lowOwnerPhysicalDirichletWeight_nonneg R (p * a)
  calc
    (lowOwnerZeroFrequencyMobiusWeight R a * realMoebiusStep a) *
        (lowOwnerPhysicalDirichletWeight R (p * a) * realMoebiusStep a) =
      (lowOwnerZeroFrequencyMobiusWeight R a *
          lowOwnerPhysicalDirichletWeight R (p * a)) *
        (realMoebiusStep a) ^ 2 := by ring
    _ ≥ 0 := mul_nonneg (mul_nonneg hw hj) (sq_nonneg _)

/-- **Rank-zero diagonal is nonpositive.** -/
theorem lowOwnerFirstOwnerDirichletPolarizationAtom_diag_nonpos
    {R p a : ℕ} {sig : Finset ℕ}
    (ha : a ∈ lowOwnerFirstOwnerBaseFiber R p sig) :
    lowOwnerFirstOwnerDirichletPolarizationAtom R p (a, a) ≤ 0 := by
  rw [lowOwnerFirstOwnerDirichletPolarizationAtom_eq_mixed ha ha]
  have hprod := lowOwnerFirstOwnerDirichletBase_mul_returned_nonneg R p a
  nlinarith

/-- A clipped diagonal vanishes exactly. -/
theorem lowOwnerFirstOwnerDirichletPolarizationAtom_diag_eq_zero_of_clipped
    {R p a : ℕ} {sig : Finset ℕ}
    (ha : a ∈ lowOwnerFirstOwnerClippedBaseFiber R p sig) :
    lowOwnerFirstOwnerDirichletPolarizationAtom R p (a, a) = 0 := by
  exact lowOwnerFirstOwnerDirichletPolarizationAtom_eq_zero_of_both_clipped ha ha

/-- Any finite diagonal sum on one base fibre is nonpositive. -/
theorem sum_lowOwnerFirstOwnerDirichletPolarizationAtom_diagonal_nonpos
    (R p : ℕ) (sig : Finset ℕ) :
    (∑ a ∈ lowOwnerFirstOwnerBaseFiber R p sig,
      lowOwnerFirstOwnerDirichletPolarizationAtom R p (a, a)) ≤ 0 := by
  apply Finset.sum_nonpos
  intro a ha
  exact lowOwnerFirstOwnerDirichletPolarizationAtom_diag_nonpos ha

/-- Polarization atoms are symmetric. -/
theorem lowOwnerFirstOwnerDirichletPolarizationAtom_comm
    (R p a b : ℕ) :
    lowOwnerFirstOwnerDirichletPolarizationAtom R p (a, b) =
      lowOwnerFirstOwnerDirichletPolarizationAtom R p (b, a) := by
  unfold lowOwnerFirstOwnerDirichletPolarizationAtom
  ring

end RHLean.Proof
