import Mathlib
import «research.GLOBAL_RETURNED_CORE_COMPLETED_POLARIZATION_CURRENCY»
import «research.GLOBAL_RETURNED_CORE_UNIQUE_OWNER_RANK_DROP»

/-!
# Aggregate completed-polarization ledger before rank induction

The local currency theorem from `GLOBAL_RETURNED_CORE_COMPLETED_POLARIZATION_CURRENCY`
is deliberately pointwise only.  This file performs the first legal aggregation:
on any finite family of fully physical completed `(r,a,b)` blocks, the signed
polarization cube is exactly

  aggregate incidence four-corner - aggregate same-branch four-corners.

No absolute value, square, or contraction is used.  The same-branch ledger keeps
base and returned-child four-corners together.

The second part records the rank bookkeeping on the actual unique-owner graph:
every stripped parent occurring in a fixed-parent block has fresh-prime rank
exactly one below each child which maps to it.  Thus the aggregate identity is
now in the correct shape for a subsequent carrier-level identification of the
same-branch ledger with a lower-rank signed ledger plus named exits.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- A block coordinate is stored as `(r,(a,b))`: owner prime plus the two
r-free parent coordinates. -/
abbrev LowOwnerCompletedPolarizationBlockIndex := ℕ × (ℕ × ℕ)

/-- Fully physical completed p/r block hypotheses used by the local currency
identity. -/
def LowOwnerCompletedPolarizationBlock
    (R p : ℕ) (x : LowOwnerCompletedPolarizationBlockIndex) : Prop :=
  let r := x.1
  let a := x.2.1
  let b := x.2.2
  r.Prime ∧ ¬ r ∣ a ∧ ¬ r ∣ b ∧
    a ≤ squareRootEndpoint R ∧
    p * a ≤ squareRootEndpoint R ∧
    r * a ≤ squareRootEndpoint R ∧
    p * (r * a) ≤ squareRootEndpoint R ∧
    b ≤ squareRootEndpoint R ∧
    p * b ≤ squareRootEndpoint R ∧
    r * b ≤ squareRootEndpoint R ∧
    p * (r * b) ≤ squareRootEndpoint R

/-- Full four-corner signed polarization mass of one completed block. -/
def lowOwnerCompletedPolarizationCubeMass
    (R p : ℕ) (x : LowOwnerCompletedPolarizationBlockIndex) : ℝ :=
  let r := x.1
  let a := x.2.1
  let b := x.2.2
  lowOwnerFirstOwnerDirichletPolarizationAtom R p (a, b) +
    lowOwnerFirstOwnerDirichletPolarizationAtom R p (r * a, b) +
    lowOwnerFirstOwnerDirichletPolarizationAtom R p (a, r * b) +
    lowOwnerFirstOwnerDirichletPolarizationAtom R p (r * a, r * b)

/-- Incidence four-corner currency of one completed block. -/
def lowOwnerCompletedIncidenceFourCornerMass
    (R p : ℕ) (x : LowOwnerCompletedPolarizationBlockIndex) : ℝ :=
  let r := x.1
  let a := x.2.1
  let b := x.2.2
  weightedMoebiusFreshPrimeFourCornerMass
    (lowOwnerThresholdOwnerIncidenceWeight R p) r a b

/-- The two same-branch four-corners are retained as one signed object. -/
def lowOwnerCompletedSameBranchFourCornerMass
    (R p : ℕ) (x : LowOwnerCompletedPolarizationBlockIndex) : ℝ :=
  let r := x.1
  let a := x.2.1
  let b := x.2.2
  weightedMoebiusFreshPrimeFourCornerMass
      (lowOwnerDirichletBaseCoefficient R) r a b +
    weightedMoebiusFreshPrimeFourCornerMass
      (lowOwnerDirichletReturnedCoefficient R p) r a b

/-- Local completed currency in the aggregate notation of this file. -/
theorem lowOwnerCompletedPolarizationCubeMass_eq_incidence_sub_sameBranch
    {R p : ℕ} {x : LowOwnerCompletedPolarizationBlockIndex}
    (hx : LowOwnerCompletedPolarizationBlock R p x) :
    lowOwnerCompletedPolarizationCubeMass R p x =
      lowOwnerCompletedIncidenceFourCornerMass R p x -
        lowOwnerCompletedSameBranchFourCornerMass R p x := by
  rcases x with ⟨r, a, b⟩
  rcases hx with
    ⟨hr, hraFresh, hrbFresh,
      ha, hpa, hra, hpra, hb, hpb, hrb, hprb⟩
  dsimp [lowOwnerCompletedPolarizationCubeMass,
    lowOwnerCompletedIncidenceFourCornerMass,
    lowOwnerCompletedSameBranchFourCornerMass]
  rw [lowOwnerDirichletPolarization_fourCorner_eq_threshold_sub_branchFourCorners_of_complete
    hr hraFresh hrbFresh ha hpa hra hpra hb hpb hrb hprb]
  ring

/-- **Aggregate signed-currency identity.**  The two same-branch terms are not
estimated; they remain inside one aggregate ledger. -/
theorem sum_lowOwnerCompletedPolarizationCubeMass_eq_incidence_sub_sameBranch
    {R p : ℕ}
    (blocks : Finset LowOwnerCompletedPolarizationBlockIndex)
    (hblocks : ∀ x ∈ blocks, LowOwnerCompletedPolarizationBlock R p x) :
    (∑ x ∈ blocks, lowOwnerCompletedPolarizationCubeMass R p x) =
      (∑ x ∈ blocks, lowOwnerCompletedIncidenceFourCornerMass R p x) -
        ∑ x ∈ blocks, lowOwnerCompletedSameBranchFourCornerMass R p x := by
  calc
    (∑ x ∈ blocks, lowOwnerCompletedPolarizationCubeMass R p x) =
        ∑ x ∈ blocks,
          (lowOwnerCompletedIncidenceFourCornerMass R p x -
            lowOwnerCompletedSameBranchFourCornerMass R p x) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact lowOwnerCompletedPolarizationCubeMass_eq_incidence_sub_sameBranch
        (hblocks x hx)
    _ = _ := by
      rw [Finset.sum_sub_distrib]

/-- A child in one cell-specific fixed-parent block has rank exactly one above
its stripped parent.  This is the rank annotation needed before any strong
induction can be started. -/
theorem lowOwnerFirstOwnerGreatestOwnerFixedParentCellFiber_parent_rank_add_one
    {R p r : ℕ} {sig : Finset ℕ} {parent child : ℕ × ℕ}
    (hp : p.Prime)
    (hchild : child ∈
      lowOwnerFirstOwnerGreatestOwnerFixedParentCellFiber
        R p sig r parent) :
    lowOwnerFreshPairRank parent + 1 = lowOwnerFreshPairRank child := by
  rcases child with ⟨m, n⟩
  rcases Finset.mem_filter.mp hchild with ⟨howner, hparent⟩
  have hrank :=
    lowOwnerFirstOwnerGreatestOwnerPositivePair_parent_rank_add_one
      hp howner
  simpa [hparent] using hrank

/-- In particular every fixed-parent block is genuinely lower rank than each
child it contains. -/
theorem lowOwnerFirstOwnerGreatestOwnerFixedParentCellFiber_parent_rank_lt
    {R p r : ℕ} {sig : Finset ℕ} {parent child : ℕ × ℕ}
    (hp : p.Prime)
    (hchild : child ∈
      lowOwnerFirstOwnerGreatestOwnerFixedParentCellFiber
        R p sig r parent) :
    lowOwnerFreshPairRank parent < lowOwnerFreshPairRank child := by
  have h :=
    lowOwnerFirstOwnerGreatestOwnerFixedParentCellFiber_parent_rank_add_one
      hp hchild
  omega

/-- Every parent label that actually occurs in the unique-owner parent Fubini
comes with a child one rank above it. -/
theorem lowOwnerFirstOwnerGreatestOwnerParentSet_has_rank_successor
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hp : p.Prime)
    (hparent : parent ∈
      lowOwnerFirstOwnerGreatestOwnerParentSet R p sig r) :
    ∃ child ∈ lowOwnerFirstOwnerGreatestOwnerFixedParentCellFiber
        R p sig r parent,
      lowOwnerFreshPairRank parent + 1 = lowOwnerFreshPairRank child := by
  rcases Finset.mem_image.mp hparent with ⟨child, hchild, hEq⟩
  refine ⟨child, ?_, ?_⟩
  · exact Finset.mem_filter.mpr ⟨hchild, hEq⟩
  · exact lowOwnerFirstOwnerGreatestOwnerFixedParentCellFiber_parent_rank_add_one
      hp (Finset.mem_filter.mpr ⟨hchild, hEq⟩)

end RHLean.Proof
