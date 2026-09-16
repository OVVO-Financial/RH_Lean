import Mathlib
import «research.GLOBAL_RETURNED_CORE_POLARIZATION_RAW_PARENT_FUBINI»
import «research.GLOBAL_RETURNED_CORE_SIGNED_POLARIZATION_OWNER_SPLICE»

/-!
# Raw-parent orbit partition with explicit inert survivor

This file performs only the exact carrier bookkeeping needed before any
completed-cube currency or reciprocal-energy estimate is used.

Fix one first-owner cell `(p,sig)` and one revealed prime `r`.  The descending
filtration already gives the exact signed identity

  polarization before r = polarization after r + owner fibre r.

The owner fibre has already been partitioned by orientation-preserving raw
parents.  The correction needed to turn that statement into an orbit statement
is that not every pair surviving after `r` need lie in an orbit whose raw parent
occurs in the owner fibre: some pairs never meet `r` on the physical clock.
Those pairs are retained explicitly as the `r`-inert survivor.

Thus the post-r same-branch carrier is split exactly into

  orbit-covered even pairs + inert pairs,

and the signed descending identity becomes

  before r = orbit-even mass + inert mass + owner-fibre mass.

No magnitude estimate, square, rank induction, or `2/9` contraction appears in
this file.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Same-branch packet after revealing `r`, restricted to one first-owner cell. -/
def lowOwnerFirstOwnerCellRevealedSameBranchCarrier
    (R p : ℕ) (sig S : Finset ℕ) (r : ℕ) : Finset (ℕ × ℕ) :=
  (lowOwnerRevealedSameBranchPairCarrier R S r).filter fun mn =>
    mn.1 ∈ lowOwnerFirstOwnerBaseFiber R p sig ∧
      mn.2 ∈ lowOwnerFirstOwnerBaseFiber R p sig

/-- The part of the same-branch survivor whose orientation-preserving raw parent
actually occurs underneath the current full-polarization owner fibre.  These are
the even corners of the raw-parent orbits seen by the current crossing packet. -/
def lowOwnerFirstOwnerRawParentOrbitEvenCarrier
    (R p : ℕ) (sig S : Finset ℕ) (r : ℕ) : Finset (ℕ × ℕ) :=
  (lowOwnerFirstOwnerCellRevealedSameBranchCarrier R p sig S r).filter fun mn =>
    lowOwnerFirstOwnerPolarizationRawParent r mn ∈
      lowOwnerFirstOwnerPolarizationRawParentSet R p sig r

/-- Same-branch pairs which survive revealing `r` but whose raw parent does not
occur below the current owner fibre.  They are the exact `r`-inert correction;
they are not absorbed into a boundary estimate. -/
def lowOwnerFirstOwnerRawParentOrbitInertCarrier
    (R p : ℕ) (sig S : Finset ℕ) (r : ℕ) : Finset (ℕ × ℕ) :=
  (lowOwnerFirstOwnerCellRevealedSameBranchCarrier R p sig S r).filter fun mn =>
    lowOwnerFirstOwnerPolarizationRawParent r mn ∉
      lowOwnerFirstOwnerPolarizationRawParentSet R p sig r

/-- Orbit-covered and inert survivor packets are disjoint. -/
theorem lowOwnerFirstOwnerRawParentOrbitEven_disjoint_inert
    (R p : ℕ) (sig S : Finset ℕ) (r : ℕ) :
    Disjoint
      (lowOwnerFirstOwnerRawParentOrbitEvenCarrier R p sig S r)
      (lowOwnerFirstOwnerRawParentOrbitInertCarrier R p sig S r) := by
  rw [Finset.disjoint_left]
  intro mn heven hinert
  have hmem := (Finset.mem_filter.mp heven).2
  have hnot := (Finset.mem_filter.mp hinert).2
  exact hnot hmem

/-- **Exact survivor support partition.**  No same-branch pair is lost: it is
orbit-covered exactly when its raw parent occurs under the current owner fibre,
and otherwise it is explicitly inert. -/
theorem lowOwnerFirstOwnerCellRevealedSameBranchCarrier_eq_orbitEven_union_inert
    (R p : ℕ) (sig S : Finset ℕ) (r : ℕ) :
    lowOwnerFirstOwnerCellRevealedSameBranchCarrier R p sig S r =
      lowOwnerFirstOwnerRawParentOrbitEvenCarrier R p sig S r ∪
        lowOwnerFirstOwnerRawParentOrbitInertCarrier R p sig S r := by
  ext mn
  constructor
  · intro hmn
    by_cases hparent :
        lowOwnerFirstOwnerPolarizationRawParent r mn ∈
          lowOwnerFirstOwnerPolarizationRawParentSet R p sig r
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hmn, hparent⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hmn, hparent⟩)
  · intro hmn
    rcases Finset.mem_union.mp hmn with heven | hinert
    · exact (Finset.mem_filter.mp heven).1
    · exact (Finset.mem_filter.mp hinert).1

/-- Exact signed Fubini of the same-branch survivor into orbit-even and inert
parts, for an arbitrary pair weight. -/
theorem sum_lowOwnerFirstOwnerCellRevealedSameBranch_eq_orbitEven_add_inert
    (R p : ℕ) (sig S : Finset ℕ) (r : ℕ)
    (f : ℕ × ℕ → ℝ) :
    (∑ mn ∈ lowOwnerFirstOwnerCellRevealedSameBranchCarrier R p sig S r,
        f mn) =
      (∑ mn ∈ lowOwnerFirstOwnerRawParentOrbitEvenCarrier R p sig S r,
        f mn) +
      ∑ mn ∈ lowOwnerFirstOwnerRawParentOrbitInertCarrier R p sig S r,
        f mn := by
  rw [lowOwnerFirstOwnerCellRevealedSameBranchCarrier_eq_orbitEven_union_inert,
    Finset.sum_union
      (lowOwnerFirstOwnerRawParentOrbitEven_disjoint_inert R p sig S r)]

/-- Zero-extension to one first-owner cell converts the revealed pair mass after
inserting `r` into the literal cell-restricted same-branch carrier. -/
theorem lowOwnerRevealedPairMassWith_insert_cellRestricted_eq_sameBranch
    {R p r : ℕ} {sig S : Finset ℕ}
    (hr : r.Prime) (hrS : r ∉ S) (v : ℕ → ℝ) :
    lowOwnerRevealedPairMassWith R (insert r S)
        (lowOwnerFirstOwnerCellRestrictedSite R p sig v) =
      ∑ mn ∈ lowOwnerFirstOwnerCellRevealedSameBranchCarrier R p sig S r,
        v mn.1 * v mn.2 := by
  unfold lowOwnerRevealedPairMassWith
  rw [lowOwnerRevealedPairCarrier_insert_eq_sameBranch hr hrS]
  unfold lowOwnerFirstOwnerCellRevealedSameBranchCarrier
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro mn _hmn
  by_cases h1 : mn.1 ∈ lowOwnerFirstOwnerBaseFiber R p sig
  · by_cases h2 : mn.2 ∈ lowOwnerFirstOwnerBaseFiber R p sig
    · simp [lowOwnerFirstOwnerCellRestrictedSite, h1, h2]
    · simp [lowOwnerFirstOwnerCellRestrictedSite, h1, h2]
  · simp [lowOwnerFirstOwnerCellRestrictedSite, h1]

/-- The signed polarization survivor after revealing `r` is exactly the signed
Dirichlet polarization mass on the cell same-branch carrier. -/
theorem lowOwnerFirstOwnerRevealedPolarizationEnergy_insert_eq_sameBranchAtoms
    {R p r : ℕ} {sig S : Finset ℕ}
    (hr : r.Prime) (hrS : r ∉ S) :
    lowOwnerFirstOwnerRevealedPolarizationEnergy R p sig (insert r S) =
      ∑ mn ∈ lowOwnerFirstOwnerCellRevealedSameBranchCarrier R p sig S r,
        lowOwnerFirstOwnerDirichletPolarizationAtom R p mn := by
  unfold lowOwnerFirstOwnerRevealedPolarizationEnergy
    lowOwnerFirstOwnerCellIncidenceSite
    lowOwnerFirstOwnerCellBaseSite
    lowOwnerFirstOwnerCellReturnedSite
  rw [lowOwnerRevealedPairMassWith_insert_cellRestricted_eq_sameBranch
      hr hrS (lowOwnerFirstOwnerDirichletIncidenceSite R p),
    lowOwnerRevealedPairMassWith_insert_cellRestricted_eq_sameBranch
      hr hrS (lowOwnerFirstOwnerDirichletBaseSite R),
    lowOwnerRevealedPairMassWith_insert_cellRestricted_eq_sameBranch
      hr hrS (lowOwnerFirstOwnerDirichletReturnedChildSite R p)]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro mn _hmn
  rfl

/-- **Post-r survivor = orbit-even + inert.**  This is the precise correction
needed before completing raw-parent cubes. -/
theorem lowOwnerFirstOwnerRevealedPolarizationEnergy_insert_eq_orbitEven_add_inert
    {R p r : ℕ} {sig S : Finset ℕ}
    (hr : r.Prime) (hrS : r ∉ S) :
    lowOwnerFirstOwnerRevealedPolarizationEnergy R p sig (insert r S) =
      (∑ mn ∈ lowOwnerFirstOwnerRawParentOrbitEvenCarrier R p sig S r,
        lowOwnerFirstOwnerDirichletPolarizationAtom R p mn) +
      ∑ mn ∈ lowOwnerFirstOwnerRawParentOrbitInertCarrier R p sig S r,
        lowOwnerFirstOwnerDirichletPolarizationAtom R p mn := by
  rw [lowOwnerFirstOwnerRevealedPolarizationEnergy_insert_eq_sameBranchAtoms
      hr hrS,
    sum_lowOwnerFirstOwnerCellRevealedSameBranch_eq_orbitEven_add_inert]

/-- **Exact corrected descending orbit identity.**

The current owner fibre is the odd-parity crossing packet; the post-r survivor
is split into even corners belonging to those raw-parent orbits plus the exact
inert complement.  This is an identity only: no completed-cube substitution or
energy estimate has yet been made. -/
theorem lowOwnerFirstOwnerRevealedPolarizationEnergy_descending_eq_orbitEven_add_inert_add_ownerFiber
    {R p r : ℕ} {sig : Finset ℕ} (hr : r.Prime) :
    lowOwnerFirstOwnerRevealedPolarizationEnergy R p sig
        (lowOwnerRevealedPrimesAbove R r) =
      (∑ mn ∈ lowOwnerFirstOwnerRawParentOrbitEvenCarrier R p sig
          (lowOwnerRevealedPrimesAbove R r) r,
        lowOwnerFirstOwnerDirichletPolarizationAtom R p mn) +
      (∑ mn ∈ lowOwnerFirstOwnerRawParentOrbitInertCarrier R p sig
          (lowOwnerRevealedPrimesAbove R r) r,
        lowOwnerFirstOwnerDirichletPolarizationAtom R p mn) +
      ∑ mn ∈ lowOwnerFirstOwnerPolarizationGreatestOwnerPairFiber R p sig r,
        lowOwnerFirstOwnerDirichletPolarizationAtom R p mn := by
  rw [lowOwnerFirstOwnerRevealedPolarizationEnergy_descending_eq_survivor_add_ownerFiber hr,
    lowOwnerFirstOwnerRevealedPolarizationEnergy_insert_eq_orbitEven_add_inert
      hr (owner_not_mem_lowOwnerRevealedPrimesAbove R r)]
  ring

end RHLean.Proof
