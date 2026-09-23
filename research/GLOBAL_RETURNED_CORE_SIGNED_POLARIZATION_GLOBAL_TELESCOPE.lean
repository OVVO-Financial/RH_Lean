import Mathlib
import «research.GLOBAL_RETURNED_CORE_POLARIZATION_CELL_OWNER_FUBINI»
import «research.GLOBAL_RETURNED_CORE_POST789_DIAGONAL_SUBTRACTED_CONTROL»

/-!
# Post-#791 closure in the existing unique-owner polarization currency

The multiplicity-safe outer Fubini was already proved in
`GLOBAL_RETURNED_CORE_POLARIZATION_CELL_OWNER_FUBINI`:

  SignedCell(p,sig)
    = diagonal(p,sig)
      + 2 * sum_{r > p} OwnerFiber(p,sig,r).

The diagonal is nonpositive, so the owner-fibre term alone gives a stronger
one-sided target.  But the post-#789 lesson is that diagonal/cross cancellation
can be load-bearing.  Therefore this file keeps two interfaces:

1. an exact global signed ledger retaining the diagonal;
2. the stronger owner-fibre-only sufficient target.

The exact ledger is the preferred coordinate for the remaining global
q^2/wall reassembly.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Complete signed unique-greatest-owner polarization off-diagonal ledger.

The factor 2 restores the opposite orientation of every positive-lag pair. -/
def lowOwnerGlobalPolarizationOwnerFiberLedger (R : ℕ) : ℝ :=
  2 * ∑ p ∈ primesUpTo (squareRootEndpoint R),
    ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
      ∑ r ∈ lowOwnerRevealedPrimesAbove R p,
        ∑ ab ∈ lowOwnerFirstOwnerPolarizationGreatestOwnerPositiveFiber
            R p sig r,
          lowOwnerFirstOwnerDirichletPolarizationAtom R p ab

/-- Global terminal diagonal retained in the polarization coordinate. -/
def lowOwnerGlobalPolarizationDiagonalLedger (R : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo (squareRootEndpoint R),
    ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
      ∑ a ∈ lowOwnerFirstOwnerBaseFiber R p sig,
        lowOwnerFirstOwnerDirichletPolarizationAtom R p (a, a)

/-- Exact signed polarization ledger: favorable diagonal plus the unique-owner
off-diagonal ledger. -/
def lowOwnerGlobalPolarizationSignedLedger (R : ℕ) : ℝ :=
  lowOwnerGlobalPolarizationDiagonalLedger R +
    lowOwnerGlobalPolarizationOwnerFiberLedger R

/-- **Exact global unique-owner normal form.**

This is only finite Fubini plus the already-proved cell identity.  In
particular, no diagonal term is discarded. -/
theorem sum_lowOwnerFirstOwnerSignedCellTelescope_eq_globalPolarizationSignedLedger
    (R : ℕ) :
    (∑ p ∈ primesUpTo (squareRootEndpoint R),
      ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
        lowOwnerFirstOwnerSignedCellTelescope R p sig) =
      lowOwnerGlobalPolarizationSignedLedger R := by
  unfold lowOwnerGlobalPolarizationSignedLedger
    lowOwnerGlobalPolarizationDiagonalLedger
    lowOwnerGlobalPolarizationOwnerFiberLedger
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hpMem
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro sig _hsig
  exact lowOwnerFirstOwnerSignedCellTelescope_eq_diagonal_add_ownerFibers
    (mem_primesUpTo.mp hpMem).1

/-- The owner-fibre-only ledger is a valid but strictly stronger one-sided
majorant, obtained by discarding only the already-proved nonpositive diagonal. -/
theorem sum_lowOwnerFirstOwnerSignedCellTelescope_le_globalPolarizationOwnerFiberLedger
    (R : ℕ) :
    (∑ p ∈ primesUpTo (squareRootEndpoint R),
      ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
        lowOwnerFirstOwnerSignedCellTelescope R p sig) ≤
      lowOwnerGlobalPolarizationOwnerFiberLedger R := by
  unfold lowOwnerGlobalPolarizationOwnerFiberLedger
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hpMem
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro sig _hsig
  exact lowOwnerFirstOwnerSignedCellTelescope_le_two_ownerFibers
    (mem_primesUpTo.mp hpMem).1

/-- Preferred post-#791 target: keep the terminal polarization diagonal inside
the globally assembled signed ledger. -/
def LowOwnerPolarizationSignedLedgerQ2EnergyBound (B C : ℝ) : Prop :=
  ∀ R : ℕ, ∀ K : ℝ,
    56 ≤ R →
    LowerMertensCriticalEnvelope R K →
    lowOwnerGlobalPolarizationSignedLedger R ≤
      B * canonicalRoughLowQ2DaughterEnergy R +
        C * (R : ℝ) ^ 2 * K

/-- The exact signed-ledger target is literally equivalent to the #791
signed-cell target. -/
theorem polarizationSignedLedgerQ2EnergyBound_iff_signedCellQ2EnergyAssemblyBound
    (B C : ℝ) :
    LowOwnerPolarizationSignedLedgerQ2EnergyBound B C ↔
      LowOwnerSignedCellQ2EnergyAssemblyBound B C := by
  constructor
  · intro h R K hR hK
    rw [sum_lowOwnerFirstOwnerSignedCellTelescope_eq_globalPolarizationSignedLedger]
    exact h R K hR hK
  · intro h R K hR hK
    rw [← sum_lowOwnerFirstOwnerSignedCellTelescope_eq_globalPolarizationSignedLedger]
    exact h R K hR hK

/-- Direct RH consumer in the exact diagonal-retaining owner coordinate. -/
theorem riemannHypothesis_of_polarizationSignedLedgerQ2EnergyBound
    {B C : ℝ}
    (hBlo : -1 / 4 ≤ B) (hBhi : B ≤ 7 / 4) (hC : 0 ≤ C)
    (hLedger : LowOwnerPolarizationSignedLedgerQ2EnergyBound B C) :
    RiemannHypothesis := by
  exact
    riemannHypothesis_of_signedCellQ2EnergyAssemblyBound
      hBlo hBhi hC
      ((polarizationSignedLedgerQ2EnergyBound_iff_signedCellQ2EnergyAssemblyBound
        B C).1 hLedger)

/-- Stronger optional target obtained after dropping the favorable diagonal. -/
def LowOwnerPolarizationOwnerFiberQ2EnergyBound (B C : ℝ) : Prop :=
  ∀ R : ℕ, ∀ K : ℝ,
    56 ≤ R →
    LowerMertensCriticalEnvelope R K →
    lowOwnerGlobalPolarizationOwnerFiberLedger R ≤
      B * canonicalRoughLowQ2DaughterEnergy R +
        C * (R : ℝ) ^ 2 * K

/-- The stronger owner-fibre-only target implies the exact signed target. -/
theorem signedCellQ2EnergyAssemblyBound_of_polarizationOwnerFiber
    {B C : ℝ}
    (hOwner : LowOwnerPolarizationOwnerFiberQ2EnergyBound B C) :
    LowOwnerSignedCellQ2EnergyAssemblyBound B C := by
  intro R K hR hK
  exact
    (sum_lowOwnerFirstOwnerSignedCellTelescope_le_globalPolarizationOwnerFiberLedger R).trans
      (hOwner R K hR hK)

/-- Direct RH consumer for the stronger owner-fibre-only target. -/
theorem riemannHypothesis_of_polarizationOwnerFiberQ2EnergyBound
    {B C : ℝ}
    (hBlo : -1 / 4 ≤ B) (hBhi : B ≤ 7 / 4) (hC : 0 ≤ C)
    (hOwner : LowOwnerPolarizationOwnerFiberQ2EnergyBound B C) :
    RiemannHypothesis := by
  exact
    riemannHypothesis_of_signedCellQ2EnergyAssemblyBound
      hBlo hBhi hC
      (signedCellQ2EnergyAssemblyBound_of_polarizationOwnerFiber hOwner)

end RHLean.Proof
