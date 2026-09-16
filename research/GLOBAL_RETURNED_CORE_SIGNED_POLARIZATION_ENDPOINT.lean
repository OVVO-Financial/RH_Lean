import Mathlib
import «research.GLOBAL_RETURNED_CORE_SIGNED_POLARIZATION_FILTRATION»
import «research.GLOBAL_RETURNED_CORE_DIRICHLET_PAIR_POLARIZATION»

/-!
# The revealed-prime signed polarization starts at the actual cell telescope

`GLOBAL_RETURNED_CORE_SIGNED_POLARIZATION_FILTRATION` introduced a signed
revealed-prime ledger for the three Dirichlet coordinates (incidence, base, and
returned child).  This file identifies its unrevealed endpoint with the
repository's existing first-owner signed cell telescope.

Thus the new filtration is not a parallel surrogate:

  PiEnergy(empty) = lowOwnerFirstOwnerSignedCellTelescope.

The proof is finite support bookkeeping only.  Zero-extension to one p/signature
cell turns the unrevealed global pair carrier into exactly the Cartesian square
of that cell, after which the existing pair-level polarization theorem applies.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- The unrevealed pair carrier is the full ordered nonzero-Mobius square. -/
theorem lowOwnerRevealedPairCarrier_empty (R : ℕ) :
    lowOwnerRevealedPairCarrier R ∅ =
      (lowOwnerNonzeroMobiusCarrier R).product
        (lowOwnerNonzeroMobiusCarrier R) := by
  simp [lowOwnerRevealedPairCarrier, lowOwnerRevealedPrimeSignature]

/-- A first-owner base cell is contained in the global nonzero-Mobius carrier. -/
theorem lowOwnerFirstOwnerBaseFiber_subset_nonzeroCarrier
    (R p : ℕ) (sig : Finset ℕ) :
    lowOwnerFirstOwnerBaseFiber R p sig ⊆ lowOwnerNonzeroMobiusCarrier R := by
  intro n hn
  exact (Finset.mem_filter.mp hn).1

/-- On the unrevealed carrier, zero-extension to one cell reduces an arbitrary
pair mass to the Cartesian square of that cell. -/
theorem lowOwnerRevealedPairMassWith_empty_cellRestricted_eq
    (R p : ℕ) (sig : Finset ℕ) (v : ℕ → ℝ) :
    lowOwnerRevealedPairMassWith R ∅
        (lowOwnerFirstOwnerCellRestrictedSite R p sig v) =
      ∑ mn ∈ (lowOwnerFirstOwnerBaseFiber R p sig).product
          (lowOwnerFirstOwnerBaseFiber R p sig),
        v mn.1 * v mn.2 := by
  let base := lowOwnerFirstOwnerBaseFiber R p sig
  let global := lowOwnerNonzeroMobiusCarrier R
  have hbase : base ⊆ global := by
    intro n hn
    exact lowOwnerFirstOwnerBaseFiber_subset_nonzeroCarrier R p sig hn
  have hprod : base.product base ⊆ global.product global := by
    intro mn hmn
    rcases Finset.mem_product.mp hmn with ⟨h1, h2⟩
    exact Finset.mem_product.mpr ⟨hbase h1, hbase h2⟩
  have hzero :
      ∀ mn ∈ global.product global, mn ∉ base.product base →
        lowOwnerFirstOwnerCellRestrictedSite R p sig v mn.1 *
            lowOwnerFirstOwnerCellRestrictedSite R p sig v mn.2 = 0 := by
    intro mn _hmn hnot
    by_cases h1 : mn.1 ∈ base
    · have h2 : mn.2 ∉ base := by
        intro h2
        exact hnot (Finset.mem_product.mpr ⟨h1, h2⟩)
      simp [lowOwnerFirstOwnerCellRestrictedSite, base, h1, h2]
    · simp [lowOwnerFirstOwnerCellRestrictedSite, base, h1]
  have hsubset := Finset.sum_subset hprod hzero
  have hinside :
      (∑ mn ∈ base.product base,
        lowOwnerFirstOwnerCellRestrictedSite R p sig v mn.1 *
          lowOwnerFirstOwnerCellRestrictedSite R p sig v mn.2) =
        ∑ mn ∈ base.product base, v mn.1 * v mn.2 := by
    apply Finset.sum_congr rfl
    intro mn hmn
    rcases Finset.mem_product.mp hmn with ⟨h1, h2⟩
    simp [lowOwnerFirstOwnerCellRestrictedSite, base, h1, h2]
  unfold lowOwnerRevealedPairMassWith
  rw [lowOwnerRevealedPairCarrier_empty]
  change
    (∑ mn ∈ global.product global,
      lowOwnerFirstOwnerCellRestrictedSite R p sig v mn.1 *
        lowOwnerFirstOwnerCellRestrictedSite R p sig v mn.2) =
      ∑ mn ∈ base.product base, v mn.1 * v mn.2
  rw [← hsubset, hinside]

/-- **Endpoint splice.**  Before any owner coordinate is revealed, the signed
polarization filtration is exactly the actual first-owner signed cell telescope. -/
theorem lowOwnerFirstOwnerRevealedPolarizationEnergy_empty_eq_signedCellTelescope
    {R p : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    lowOwnerFirstOwnerRevealedPolarizationEnergy R p sig ∅ =
      lowOwnerFirstOwnerSignedCellTelescope R p sig := by
  unfold lowOwnerFirstOwnerRevealedPolarizationEnergy
    lowOwnerFirstOwnerCellIncidenceSite
    lowOwnerFirstOwnerCellBaseSite
    lowOwnerFirstOwnerCellReturnedSite
  rw [lowOwnerRevealedPairMassWith_empty_cellRestricted_eq,
    lowOwnerRevealedPairMassWith_empty_cellRestricted_eq,
    lowOwnerRevealedPairMassWith_empty_cellRestricted_eq,
    lowOwnerFirstOwnerSignedCellTelescope_eq_sum_dirichletPolarizationAtoms hp]
  unfold lowOwnerFirstOwnerDirichletPolarizationAtom
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]

end RHLean.Proof
