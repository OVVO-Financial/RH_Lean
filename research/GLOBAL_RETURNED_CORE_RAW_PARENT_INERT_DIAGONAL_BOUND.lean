import Mathlib
import «research.GLOBAL_RETURNED_CORE_RAW_PARENT_INERT_OWNER_FUBINI»
import «research.GLOBAL_RETURNED_CORE_DIRICHLET_POLARIZATION_RANK_BASE»

/-!
# Favorable inert diagonal after exact signed owner reassembly

Only after the inert carrier has been decomposed exactly into its diagonal and
strictly-lower greatest-owner fibres do we use an inequality.  The diagonal is
the already-compiled rank-zero Dirichlet polarization and is nonpositive, so it
may be discarded in an upper bound with no boundary cost.

Thus the current descending layer is bounded by only

  next polarization + strictly-lower owner fibres.

No norm, square, triangle inequality, or Mertens estimate is introduced.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- The inert diagonal is favorable term-by-term. -/
theorem sum_lowOwnerFirstOwnerRawParentOrbitInertDiagonal_nonpos
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) :
    (∑ mn ∈ lowOwnerFirstOwnerRawParentOrbitInertDiagonalCarrier R p sig r,
      lowOwnerFirstOwnerDirichletPolarizationAtom R p mn) ≤ 0 := by
  apply Finset.sum_nonpos
  intro mn hmn
  rcases Finset.mem_filter.mp hmn with ⟨hinert, hdiag⟩
  rcases mn with ⟨a, b⟩
  dsimp at hdiag
  subst b
  rcases Finset.mem_filter.mp hinert with ⟨hcell, _hnotRaw⟩
  rcases Finset.mem_filter.mp hcell with ⟨_hsame, haBase, _hbBase⟩
  exact lowOwnerFirstOwnerDirichletPolarizationAtom_diag_nonpos haBase

/-- **First legal one-sided recursion.**  After the exact raw-parent and inert
owner Fubini identities, the only term discarded is the nonpositive diagonal.
Every surviving inert off-diagonal term has a greatest owner strictly below
`r`. -/
theorem lowOwnerFirstOwnerRevealedPolarizationEnergy_descending_le_next_add_lowerOwners
    {R p r : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r) :
    lowOwnerFirstOwnerRevealedPolarizationEnergy R p sig
        (lowOwnerRevealedPrimesAbove R r) ≤
      (∑ parent ∈ lowOwnerFirstOwnerPolarizationRawParentSet R p sig r,
        realMoebiusStep parent.1 * realMoebiusStep parent.2 *
          lowOwnerDirichletNextPolarizationScalar
            R p r parent.1 parent.2) +
      ∑ q ∈ lowOwnerFirstOwnerRawParentInertLowerOwnerSchedule R p r,
        ∑ mn ∈ lowOwnerFirstOwnerRawParentOrbitInertGreatestOwnerFiber
            R p sig r q,
          lowOwnerFirstOwnerDirichletPolarizationAtom R p mn := by
  have heq :=
    lowOwnerFirstOwnerRevealedPolarizationEnergy_descending_eq_next_add_diagonal_add_lowerOwners
      (R := R) (p := p) (r := r) (sig := sig) hp hr hpr
  have hdiag :=
    sum_lowOwnerFirstOwnerRawParentOrbitInertDiagonal_nonpos R p sig r
  linarith

end RHLean.Proof
