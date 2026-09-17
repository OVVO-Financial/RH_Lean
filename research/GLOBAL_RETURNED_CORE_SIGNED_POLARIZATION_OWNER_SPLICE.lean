import Mathlib
import «research.GLOBAL_RETURNED_CORE_SIGNED_POLARIZATION_FILTRATION»
import «research.GLOBAL_RETURNED_CORE_POLARIZATION_UNIQUE_OWNER_FUBINI»

/-!
# Splice signed revealed-prime polarization to the unique greatest-owner fibre

The signed revealed-prime filtration already proves that the same-branch mass
survives after inserting a fresh coordinate and that the removed mass is the
crossing packet.  This file identifies that crossing packet, after restricting
to one first-owner cell, with the repository's existing unique greatest-owner
polarization fibre.

Consequently the descending step has the exact form

  polarization before r
    = polarization after r
      + signed polarization on the r greatest-owner fibre.

This is the aggregate same-branch identity required before any reciprocal-energy
estimate is applied.  No absolute value, square, `2/9`, or boundary estimate is
used here.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- The global revealed crossing carrier restricted to one p-free base cell. -/
def lowOwnerFirstOwnerCellRevealedCrossCarrier
    (R p : ℕ) (sig S : Finset ℕ) (r : ℕ) : Finset (ℕ × ℕ) :=
  (lowOwnerRevealedCrossPairCarrier R S r).filter fun mn =>
    mn.1 ∈ lowOwnerFirstOwnerBaseFiber R p sig ∧
      mn.2 ∈ lowOwnerFirstOwnerBaseFiber R p sig

/-- Zero-extension to one cell simply filters an arbitrary crossing sum to the
pairs whose two coordinates lie in that cell. -/
theorem lowOwnerRevealedCrossPairMassWith_cellRestricted_eq
    (R p : ℕ) (sig S : Finset ℕ) (r : ℕ) (v : ℕ → ℝ) :
    lowOwnerRevealedCrossPairMassWith R S r
        (lowOwnerFirstOwnerCellRestrictedSite R p sig v) =
      ∑ mn ∈ lowOwnerFirstOwnerCellRevealedCrossCarrier R p sig S r,
        v mn.1 * v mn.2 := by
  unfold lowOwnerRevealedCrossPairMassWith
    lowOwnerFirstOwnerCellRevealedCrossCarrier
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro mn _hmn
  by_cases h1 : mn.1 ∈ lowOwnerFirstOwnerBaseFiber R p sig
  · by_cases h2 : mn.2 ∈ lowOwnerFirstOwnerBaseFiber R p sig
    · simp [lowOwnerFirstOwnerCellRestrictedSite, h1, h2]
    · simp [lowOwnerFirstOwnerCellRestrictedSite, h1, h2]
  · simp [lowOwnerFirstOwnerCellRestrictedSite, h1]

/-- The signed polarization crossing mass is exactly the sum of pointwise
Dirichlet polarization atoms on the cell-restricted crossing carrier. -/
theorem lowOwnerFirstOwnerRevealedPolarizationCrossMass_eq_sum_cellCross
    (R p : ℕ) (sig S : Finset ℕ) (r : ℕ) :
    lowOwnerFirstOwnerRevealedPolarizationCrossMass R p sig S r =
      ∑ mn ∈ lowOwnerFirstOwnerCellRevealedCrossCarrier R p sig S r,
        lowOwnerFirstOwnerDirichletPolarizationAtom R p mn := by
  unfold lowOwnerFirstOwnerRevealedPolarizationCrossMass
    lowOwnerFirstOwnerCellIncidenceSite
    lowOwnerFirstOwnerCellBaseSite
    lowOwnerFirstOwnerCellReturnedSite
  rw [lowOwnerRevealedCrossPairMassWith_cellRestricted_eq,
    lowOwnerRevealedCrossPairMassWith_cellRestricted_eq,
    lowOwnerRevealedCrossPairMassWith_cellRestricted_eq]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro mn _hmn
  rfl

/-- **Carrier splice.**  With all primes larger than r already revealed, the
cell-restricted r-crossing packet is exactly the full-polarization unique
greatest-owner fibre. -/
theorem lowOwnerFirstOwnerCellRevealedCrossCarrier_above_eq_polarizationGreatestOwner
    {R p r : ℕ} {sig : Finset ℕ} (hr : r.Prime) :
    lowOwnerFirstOwnerCellRevealedCrossCarrier R p sig
        (lowOwnerRevealedPrimesAbove R r) r =
      lowOwnerFirstOwnerPolarizationGreatestOwnerPairFiber R p sig r := by
  ext mn
  rcases mn with ⟨m, n⟩
  constructor
  · intro hmn
    rcases Finset.mem_filter.mp hmn with ⟨hcross, hmBase, hnBase⟩
    have howner := descendingCrossPair_greatestFreshOwner hr hcross
    have hne : m ≠ n := by
      intro heq
      subst n
      have hfresh := howner.1
      simp [squarefreePairFreshPrimeSet] at hfresh
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hmBase, hnBase⟩, hne⟩,
        howner⟩
  · intro hmn
    rcases Finset.mem_filter.mp hmn with ⟨hoff, howner⟩
    rcases Finset.mem_filter.mp hoff with ⟨hprod, _hne⟩
    rcases Finset.mem_product.mp hprod with ⟨hmBase, hnBase⟩
    have hmCar := (Finset.mem_filter.mp hmBase).1
    have hnCar := (Finset.mem_filter.mp hnBase).1
    have hcross := greatestFreshOwner_descendingCrossPair
      hr hmCar hnCar howner
    exact Finset.mem_filter.mpr ⟨hcross, hmBase, hnBase⟩

/-- The descending signed crossing mass is literally the signed polarization on
the unique greatest-owner fibre. -/
theorem lowOwnerFirstOwnerRevealedPolarizationCrossMass_above_eq_ownerFiber
    {R p r : ℕ} {sig : Finset ℕ} (hr : r.Prime) :
    lowOwnerFirstOwnerRevealedPolarizationCrossMass R p sig
        (lowOwnerRevealedPrimesAbove R r) r =
      ∑ mn ∈ lowOwnerFirstOwnerPolarizationGreatestOwnerPairFiber R p sig r,
        lowOwnerFirstOwnerDirichletPolarizationAtom R p mn := by
  rw [lowOwnerFirstOwnerRevealedPolarizationCrossMass_eq_sum_cellCross,
    lowOwnerFirstOwnerCellRevealedCrossCarrier_above_eq_polarizationGreatestOwner hr]

/-- **Exact descending signed-polarization telescope.**  The same-branch mass is
kept as the surviving revealed-prime ledger; the removed term is exactly the
current unique greatest-owner fibre. -/
theorem lowOwnerFirstOwnerRevealedPolarizationEnergy_descending_eq_survivor_add_ownerFiber
    {R p r : ℕ} {sig : Finset ℕ} (hr : r.Prime) :
    lowOwnerFirstOwnerRevealedPolarizationEnergy R p sig
        (lowOwnerRevealedPrimesAbove R r) =
      lowOwnerFirstOwnerRevealedPolarizationEnergy R p sig
          (insert r (lowOwnerRevealedPrimesAbove R r)) +
        ∑ mn ∈ lowOwnerFirstOwnerPolarizationGreatestOwnerPairFiber R p sig r,
          lowOwnerFirstOwnerDirichletPolarizationAtom R p mn := by
  rw [lowOwnerFirstOwnerRevealedPolarizationEnergy_descending_step hr,
    lowOwnerFirstOwnerRevealedPolarizationCrossMass_above_eq_ownerFiber hr]

end RHLean.Proof
