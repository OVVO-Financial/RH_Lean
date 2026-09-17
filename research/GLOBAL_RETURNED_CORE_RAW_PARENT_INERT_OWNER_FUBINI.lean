import Mathlib
import «research.GLOBAL_RETURNED_CORE_RAW_PARENT_INERT_PERSISTENCE»

/-!
# Exact lower-owner Fubini for the raw-parent inert survivor

The raw-parent full-orbit recursion leaves one explicitly named inert carrier.
The preceding persistence theorem proves that every fresh prime still
separating an inert pair is strictly below the current descending owner `r`.
This file removes the last ambiguity in that word "inert":

* split the inert carrier exactly into diagonal and off-diagonal parts;
* assign every off-diagonal inert pair to its unique greatest fresh owner;
* prove that this owner lies strictly between the first owner `p` and the
  current owner `r`;
* Fubini the signed inert mass over those lower owners with no multiplicity.

Consequently the descending raw-parent identity becomes

  current r-layer
    = next-polarization layer
    + inert diagonal
    + strictly-lower greatest-owner fibres.

There is no anonymous same-scale remainder and no energy estimate in this file.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Inert pairs on the diagonal. -/
def lowOwnerFirstOwnerRawParentOrbitInertDiagonalCarrier
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : Finset (ℕ × ℕ) :=
  (lowOwnerFirstOwnerRawParentOrbitInertCarrier R p sig
      (lowOwnerRevealedPrimesAbove R r) r).filter fun mn =>
    mn.1 = mn.2

/-- Inert pairs off the diagonal. -/
def lowOwnerFirstOwnerRawParentOrbitInertOffDiagonalCarrier
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : Finset (ℕ × ℕ) :=
  (lowOwnerFirstOwnerRawParentOrbitInertCarrier R p sig
      (lowOwnerRevealedPrimesAbove R r) r).filter fun mn =>
    mn.1 ≠ mn.2

/-- Prime schedule strictly between the fixed first owner `p` and the current
revealed owner `r`. -/
def lowOwnerFirstOwnerRawParentInertLowerOwnerSchedule
    (R p r : ℕ) : Finset ℕ :=
  (lowOwnerRevealedPrimesAbove R p).filter fun q => q < r

/-- Greatest-owner fibre of the inert off-diagonal carrier. -/
def lowOwnerFirstOwnerRawParentOrbitInertGreatestOwnerFiber
    (R p : ℕ) (sig : Finset ℕ) (r q : ℕ) : Finset (ℕ × ℕ) :=
  (lowOwnerFirstOwnerRawParentOrbitInertOffDiagonalCarrier R p sig r).filter
    fun mn => IsSquarefreePairGreatestFreshPrimeOwner q mn.1 mn.2

/-- Exact diagonal/off-diagonal partition of the inert carrier. -/
theorem sum_lowOwnerFirstOwnerRawParentOrbitInert_eq_diagonal_add_offDiagonal
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) (f : ℕ × ℕ → ℝ) :
    (∑ mn ∈ lowOwnerFirstOwnerRawParentOrbitInertCarrier R p sig
        (lowOwnerRevealedPrimesAbove R r) r,
      f mn) =
      (∑ mn ∈ lowOwnerFirstOwnerRawParentOrbitInertDiagonalCarrier
          R p sig r,
        f mn) +
      ∑ mn ∈ lowOwnerFirstOwnerRawParentOrbitInertOffDiagonalCarrier
          R p sig r,
        f mn := by
  unfold lowOwnerFirstOwnerRawParentOrbitInertDiagonalCarrier
    lowOwnerFirstOwnerRawParentOrbitInertOffDiagonalCarrier
  simpa only [not_eq] using
    (Finset.sum_filter_add_sum_filter_not
      (s := lowOwnerFirstOwnerRawParentOrbitInertCarrier R p sig
        (lowOwnerRevealedPrimesAbove R r) r)
      (p := fun mn : ℕ × ℕ => mn.1 = mn.2)
      (f := f)).symm

/-- Every inert off-diagonal pair has a unique greatest fresh owner, and that
owner is strictly below the current owner `r` while still strictly above `p`. -/
theorem lowOwnerFirstOwnerRawParentOrbitInertOffDiagonal_has_lowerGreatestOwner
    {R p r : ℕ} {sig : Finset ℕ} {mn : ℕ × ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r)
    (hmn : mn ∈
      lowOwnerFirstOwnerRawParentOrbitInertOffDiagonalCarrier R p sig r) :
    ∃ q ∈ lowOwnerFirstOwnerRawParentInertLowerOwnerSchedule R p r,
      IsSquarefreePairGreatestFreshPrimeOwner q mn.1 mn.2 := by
  rcases mn with ⟨m, n⟩
  rcases Finset.mem_filter.mp hmn with ⟨hinert, hne⟩
  rcases Finset.mem_filter.mp hinert with ⟨hcell, _hnotRaw⟩
  rcases Finset.mem_filter.mp hcell with ⟨_hsame, hmBase, hnBase⟩
  have hmCar := (Finset.mem_filter.mp hmBase).1
  have hnCar := (Finset.mem_filter.mp hnBase).1
  rcases lowOwnerNonzeroMobiusCarrier_squarefree_pos hmCar with
    ⟨hmSq, _hmPos⟩
  rcases lowOwnerNonzeroMobiusCarrier_squarefree_pos hnCar with
    ⟨hnSq, _hnPos⟩
  have hleast := squarefreePairFreshPrimeOwner_isOwner hmSq hnSq hne
  let S := squarefreePairFreshPrimeSet m n
  have hSnonempty : S.Nonempty :=
    ⟨squarefreePairFreshPrimeOwner m n, hleast.1⟩
  let q := S.max' hSnonempty
  have hqFresh : q ∈ S := Finset.max'_mem S hSnonempty
  have hqGreatest : ∀ s ∈ S, s ≤ q := by
    intro s hs
    exact Finset.le_max' S s hs
  have hqOwner : IsSquarefreePairGreatestFreshPrimeOwner q m n :=
    ⟨hqFresh, hqGreatest⟩
  have hqData := freshPrime_of_nonzeroPhysicalPair hmCar hnCar hqFresh
  have hpq := lowOwnerFirstOwnerBasePair_freshPrime_gt_owner
    hp hmBase hnBase hqFresh
  have hqr :=
    lowOwnerFirstOwnerRawParentOrbitInert_fresh_lt_owner
      hp hr hpr hinert hqFresh
  refine ⟨q, ?_, hqOwner⟩
  unfold lowOwnerFirstOwnerRawParentInertLowerOwnerSchedule
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_filter.mpr ⟨mem_primesUpTo.mpr hqData, hpq⟩, hqr⟩

/-- Distinct lower greatest owners have disjoint inert fibres. -/
theorem lowOwnerFirstOwnerRawParentOrbitInertGreatestOwnerFiber_pairwiseDisjoint
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) :
    Set.PairwiseDisjoint
      (↑(lowOwnerFirstOwnerRawParentInertLowerOwnerSchedule R p r))
      (lowOwnerFirstOwnerRawParentOrbitInertGreatestOwnerFiber R p sig r) := by
  intro q _hq s _hs hqs
  change Disjoint
    (lowOwnerFirstOwnerRawParentOrbitInertGreatestOwnerFiber R p sig r q)
    (lowOwnerFirstOwnerRawParentOrbitInertGreatestOwnerFiber R p sig r s)
  rw [Finset.disjoint_left]
  intro mn hqmem hsmem
  have hqo := (Finset.mem_filter.mp hqmem).2
  have hso := (Finset.mem_filter.mp hsmem).2
  exact hqs (squarefreePairGreatestFreshPrimeOwner_unique hqo hso)

/-- The lower-owner fibres cover the whole inert off-diagonal carrier. -/
theorem lowOwnerFirstOwnerRawParentOrbitInertGreatestOwnerFiber_biUnion
    {R p r : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r) :
    (lowOwnerFirstOwnerRawParentInertLowerOwnerSchedule R p r).biUnion
        (lowOwnerFirstOwnerRawParentOrbitInertGreatestOwnerFiber R p sig r) =
      lowOwnerFirstOwnerRawParentOrbitInertOffDiagonalCarrier R p sig r := by
  ext mn
  constructor
  · intro h
    rcases Finset.mem_biUnion.mp h with ⟨q, _hq, hmn⟩
    exact (Finset.mem_filter.mp hmn).1
  · intro hmn
    rcases lowOwnerFirstOwnerRawParentOrbitInertOffDiagonal_has_lowerGreatestOwner
      hp hr hpr hmn with ⟨q, hq, howner⟩
    exact Finset.mem_biUnion.mpr
      ⟨q, hq, Finset.mem_filter.mpr ⟨hmn, howner⟩⟩

/-- **Exact signed Fubini of the inert off-diagonal mass over strictly lower
owners.** -/
theorem sum_lowOwnerFirstOwnerRawParentOrbitInertOffDiagonal_eq_lowerOwners
    {R p r : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r)
    (f : ℕ × ℕ → ℝ) :
    (∑ mn ∈ lowOwnerFirstOwnerRawParentOrbitInertOffDiagonalCarrier R p sig r,
      f mn) =
      ∑ q ∈ lowOwnerFirstOwnerRawParentInertLowerOwnerSchedule R p r,
        ∑ mn ∈ lowOwnerFirstOwnerRawParentOrbitInertGreatestOwnerFiber
            R p sig r q,
          f mn := by
  rw [← lowOwnerFirstOwnerRawParentOrbitInertGreatestOwnerFiber_biUnion
    hp hr hpr]
  exact Finset.sum_biUnion
    (lowOwnerFirstOwnerRawParentOrbitInertGreatestOwnerFiber_pairwiseDisjoint
      R p sig r)

/-- **No anonymous inert remainder.**  The exact descending raw-parent recursion
is next polarization plus the inert diagonal plus fibres whose greatest owner
is strictly lower than `r`. -/
theorem lowOwnerFirstOwnerRevealedPolarizationEnergy_descending_eq_next_add_diagonal_add_lowerOwners
    {R p r : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r) :
    lowOwnerFirstOwnerRevealedPolarizationEnergy R p sig
        (lowOwnerRevealedPrimesAbove R r) =
      (∑ parent ∈ lowOwnerFirstOwnerPolarizationRawParentSet R p sig r,
        realMoebiusStep parent.1 * realMoebiusStep parent.2 *
          lowOwnerDirichletNextPolarizationScalar
            R p r parent.1 parent.2) +
      (∑ mn ∈ lowOwnerFirstOwnerRawParentOrbitInertDiagonalCarrier R p sig r,
        lowOwnerFirstOwnerDirichletPolarizationAtom R p mn) +
      ∑ q ∈ lowOwnerFirstOwnerRawParentInertLowerOwnerSchedule R p r,
        ∑ mn ∈ lowOwnerFirstOwnerRawParentOrbitInertGreatestOwnerFiber
            R p sig r q,
          lowOwnerFirstOwnerDirichletPolarizationAtom R p mn := by
  rw [lowOwnerFirstOwnerRevealedPolarizationEnergy_descending_eq_next_add_inert
    hp hr]
  rw [sum_lowOwnerFirstOwnerRawParentOrbitInert_eq_diagonal_add_offDiagonal]
  rw [sum_lowOwnerFirstOwnerRawParentOrbitInertOffDiagonal_eq_lowerOwners
    hp hr hpr]
  ring

end RHLean.Proof
