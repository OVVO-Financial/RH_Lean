import Mathlib
import «research.GLOBAL_RETURNED_CORE_RAW_PARENT_PREFIX_STAR_ENERGY»
import «research.GLOBAL_RETURNED_CORE_RAW_PARENT_INERT_PERSISTENCE»

/-!
# The inert survivor is exactly the prefix-star tail

The raw-parent recursion previously retained an explicit inert same-branch
survivor.  The prefix-star carrier theorem now identifies its support exactly.

An inert pair is already known to be r-free in both coordinates.  Since an
r-free same-branch pair is a raw parent exactly when at least one mixed r-child
remains physical, failure to be a raw parent is equivalent to

  X_R < r*a  and  X_R < r*b.

That is precisely the tail carrier introduced in the prefix-star energy
factorization.  Therefore the old inert packet is not an additional lower-owner
population: it is exactly the missing tail of the current r-orbit completion.

On the tail all three moved Dirichlet polarization corners vanish, so the
virtual next-polarization four-corner equals the original parent atom.  Combining
this with the raw prefix-star recursion yields one exact branch-wide identity
with no anonymous or lower-owner remainder.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- **Exact support identification: inert = prefix-star tail.** -/
theorem lowOwnerFirstOwnerRawParentOrbitInertCarrier_eq_tailCarrier
    {R p r : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r) :
    lowOwnerFirstOwnerRawParentOrbitInertCarrier R p sig
        (lowOwnerRevealedPrimesAbove R r) r =
      lowOwnerFirstOwnerRawParentTailCarrier R p sig r := by
  ext mn
  constructor
  · intro hinert
    rcases Finset.mem_filter.mp hinert with ⟨hcell, hnotRaw⟩
    rcases Finset.mem_filter.mp hcell with ⟨hsame, hbase⟩
    rcases Finset.mem_filter.mp hsame with ⟨_hprod, hsigAbove, _hdivIff⟩
    rcases hbase with ⟨haBase, hbBase⟩
    have hfree :=
      lowOwnerFirstOwnerRawParentOrbitInert_not_dvd_owner hp hr hpr hinert
    have hnoPhysical :
        ¬ (r * mn.1 ≤ squareRootEndpoint R ∨
          r * mn.2 ≤ squareRootEndpoint R) := by
      intro hphysical
      have hstar : mn ∈
          lowOwnerFirstOwnerRawParentPrefixStar R p sig r := by
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨haBase, hbBase⟩,
            ⟨hsigAbove, hfree.1, hfree.2, hphysical⟩⟩
      have hraw : mn ∈
          lowOwnerFirstOwnerPolarizationRawParentSet R p sig r :=
        lowOwnerFirstOwnerRawParentPrefixStar_subset_rawParentSet
          hp hr hpr hstar
      have hself :=
        lowOwnerFirstOwnerRawParentOrbitInert_rawParent_eq_self
          hp hr hpr hinert
      exact hnotRaw (by simpa [hself] using hraw)
    have hbranch : mn ∈
        lowOwnerFirstOwnerRawParentBranchCarrier R p sig r := by
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨haBase, hbBase⟩,
          ⟨hsigAbove, hfree.1, hfree.2⟩⟩
    exact Finset.mem_filter.mpr ⟨hbranch, hnoPhysical⟩
  · intro htail
    rcases Finset.mem_filter.mp htail with ⟨hbranch, hnoPhysical⟩
    rcases Finset.mem_filter.mp hbranch with
      ⟨hprod, hsigAbove, hra, hrb⟩
    rcases Finset.mem_product.mp hprod with ⟨haBase, hbBase⟩
    have haCar := (Finset.mem_filter.mp haBase).1
    have hbCar := (Finset.mem_filter.mp hbBase).1
    have hsame : mn ∈
        lowOwnerRevealedSameBranchPairCarrier R
          (lowOwnerRevealedPrimesAbove R r) r := by
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨haCar, hbCar⟩,
          ⟨hsigAbove, by simp [hra, hrb]⟩⟩
    have hcell : mn ∈
        lowOwnerFirstOwnerCellRevealedSameBranchCarrier R p sig
          (lowOwnerRevealedPrimesAbove R r) r :=
      Finset.mem_filter.mpr ⟨hsame, ⟨haBase, hbBase⟩⟩
    have hself : lowOwnerFirstOwnerPolarizationRawParent r mn = mn := by
      rcases mn with ⟨a, b⟩
      simp [lowOwnerFirstOwnerPolarizationRawParent,
        squarefreePrimeFamilyParent, hra, hrb]
    have hnotRaw :
        lowOwnerFirstOwnerPolarizationRawParent r mn ∉
          lowOwnerFirstOwnerPolarizationRawParentSet R p sig r := by
      intro hraw
      have hmnRaw : mn ∈
          lowOwnerFirstOwnerPolarizationRawParentSet R p sig r := by
        simpa [hself] using hraw
      have hstar : mn ∈
          lowOwnerFirstOwnerRawParentPrefixStar R p sig r := by
        rw [← lowOwnerFirstOwnerPolarizationRawParentSet_eq_prefixStar
          hp hr hpr]
        exact hmnRaw
      rcases Finset.mem_filter.mp hstar with
        ⟨_hprod, _hsig, _hra, _hrb, hphysical⟩
      exact hnoPhysical hphysical
    exact Finset.mem_filter.mpr ⟨hcell, hnotRaw⟩

/-- On a tail parent, the virtual r-four-corner next-polarization term is just
the surviving parent atom because every moved corner lies outside the physical
clock. -/
theorem lowOwnerFirstOwnerRawParentNextPolarizationTerm_eq_atom_of_tail
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hp : p.Prime) (hr : r.Prime)
    (htail : parent ∈ lowOwnerFirstOwnerRawParentTailCarrier R p sig r) :
    lowOwnerFirstOwnerRawParentNextPolarizationTerm R p r parent =
      lowOwnerFirstOwnerDirichletPolarizationAtom R p parent := by
  rcases Finset.mem_filter.mp htail with ⟨hbranch, hnoPhysical⟩
  rcases Finset.mem_filter.mp hbranch with
    ⟨_hprod, _hsig, hra, hrb⟩
  have hraOut : squareRootEndpoint R < r * parent.1 := by
    by_contra hnot
    have hle : r * parent.1 ≤ squareRootEndpoint R := Nat.le_of_not_gt hnot
    exact hnoPhysical (Or.inl hle)
  have hrbOut : squareRootEndpoint R < r * parent.2 := by
    by_contra hnot
    have hle : r * parent.2 ≤ squareRootEndpoint R := Nat.le_of_not_gt hnot
    exact hnoPhysical (Or.inr hle)
  have hfour :=
    lowOwnerDirichletPolarization_fourCorner_eq_nextPolarization
      (R := R) (p := p) hr hra hrb
  have hleft :
      lowOwnerFirstOwnerDirichletPolarizationAtom
          R p (r * parent.1, parent.2) = 0 :=
    lowOwnerFirstOwnerDirichletPolarizationAtom_eq_zero_of_first_outside
      hp.one_le hraOut
  have hright :
      lowOwnerFirstOwnerDirichletPolarizationAtom
          R p (parent.1, r * parent.2) = 0 :=
    lowOwnerFirstOwnerDirichletPolarizationAtom_eq_zero_of_second_outside
      hp.one_le hrbOut
  have hdouble :
      lowOwnerFirstOwnerDirichletPolarizationAtom
          R p (r * parent.1, r * parent.2) = 0 :=
    lowOwnerFirstOwnerDirichletPolarizationAtom_eq_zero_of_first_outside
      hp.one_le hraOut
  unfold lowOwnerFirstOwnerRawParentNextPolarizationTerm
  rw [hleft, hright, hdouble] at hfour
  linarith

/-- Exact arbitrary-weight branch partition: full branch = prefix star + tail. -/
theorem sum_lowOwnerFirstOwnerRawParentBranch_eq_rawParents_add_tail
    {R p r : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r)
    (f : ℕ × ℕ → ℝ) :
    (∑ parent ∈ lowOwnerFirstOwnerRawParentBranchCarrier R p sig r,
      f parent) =
      (∑ parent ∈ lowOwnerFirstOwnerPolarizationRawParentSet R p sig r,
        f parent) +
      ∑ parent ∈ lowOwnerFirstOwnerRawParentTailCarrier R p sig r,
        f parent := by
  have hpartition :=
    sum_lowOwnerFirstOwnerRawParentBranch_eq_prefix_add_tail
      R p sig r f
  rw [← lowOwnerFirstOwnerPolarizationRawParentSet_eq_prefixStar hp hr hpr]
    at hpartition
  exact hpartition

/-- **No inert remainder: the exact descending recursion is one full revealed
r-free branch of virtual next-polarization four-corners.** -/
theorem lowOwnerFirstOwnerRevealedPolarizationEnergy_descending_eq_branchNextPolarization
    {R p r : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r) :
    lowOwnerFirstOwnerRevealedPolarizationEnergy R p sig
        (lowOwnerRevealedPrimesAbove R r) =
      ∑ parent ∈ lowOwnerFirstOwnerRawParentBranchCarrier R p sig r,
        lowOwnerFirstOwnerRawParentNextPolarizationTerm R p r parent := by
  rw [lowOwnerFirstOwnerRevealedPolarizationEnergy_descending_eq_next_add_inert
    hp hr]
  rw [lowOwnerFirstOwnerRawParentOrbitInertCarrier_eq_tailCarrier hp hr hpr]
  have htail :
      (∑ parent ∈ lowOwnerFirstOwnerRawParentTailCarrier R p sig r,
        lowOwnerFirstOwnerDirichletPolarizationAtom R p parent) =
      ∑ parent ∈ lowOwnerFirstOwnerRawParentTailCarrier R p sig r,
        lowOwnerFirstOwnerRawParentNextPolarizationTerm R p r parent := by
    apply Finset.sum_congr rfl
    intro parent hparent
    exact
      (lowOwnerFirstOwnerRawParentNextPolarizationTerm_eq_atom_of_tail
        hp hr hparent).symm
  rw [htail]
  symm
  exact sum_lowOwnerFirstOwnerRawParentBranch_eq_rawParents_add_tail
    hp hr hpr
    (fun parent => lowOwnerFirstOwnerRawParentNextPolarizationTerm R p r parent)

end RHLean.Proof
