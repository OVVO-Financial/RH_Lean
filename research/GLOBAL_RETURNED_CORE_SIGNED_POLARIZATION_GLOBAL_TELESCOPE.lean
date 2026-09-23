import Mathlib
import «research.GLOBAL_RETURNED_CORE_POLARIZATION_CELL_OWNER_FUBINI»
import «research.GLOBAL_RETURNED_CORE_POST789_DIAGONAL_SUBTRACTED_CONTROL»

/-!
# Post-#791 closure in the existing unique-owner polarization currency

The multiplicity-safe outer Fubini was already proved in
`GLOBAL_RETURNED_CORE_POLARIZATION_CELL_OWNER_FUBINI`:

  SignedCell(p,sig)
    = diagonal(p,sig)
      + 2 * sum_{r > p} OwnerFiber(p,sig,r),

with the terminal diagonal nonpositive.  Hence

  SignedCell(p,sig)
    <= 2 * sum_{r > p} OwnerFiber(p,sig,r).

This file does not reprove that Fubini.  It only wires the existing exact
unique-owner ledger into the sharper post-#791 q^2 consumer.  Therefore the
remaining quantitative theorem is stated directly on the signed owner fibres
which charge every off-diagonal pair exactly once.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Complete signed unique-greatest-owner polarization ledger.

The factor 2 restores the opposite orientation of every positive-lag pair. -/
def lowOwnerGlobalPolarizationOwnerFiberLedger (R : ℕ) : ℝ :=
  2 * ∑ p ∈ primesUpTo (squareRootEndpoint R),
    ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
      ∑ r ∈ lowOwnerRevealedPrimesAbove R p,
        ∑ ab ∈ lowOwnerFirstOwnerPolarizationGreatestOwnerPositiveFiber
            R p sig r,
          lowOwnerFirstOwnerDirichletPolarizationAtom R p ab

/-- The full signed-cell assembly is bounded by the already-compiled
multiplicity-safe unique-owner ledger.  The only discarded term is the
nonpositive cell diagonal. -/
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

/-- Remaining quantitative target after #791, now on the exact unique-owner
signed polarization ledger rather than on repeatedly-paid surviving energies. -/
def LowOwnerPolarizationOwnerFiberQ2EnergyBound (B C : ℝ) : Prop :=
  ∀ R : ℕ, ∀ K : ℝ,
    56 ≤ R →
    LowerMertensCriticalEnvelope R K →
    lowOwnerGlobalPolarizationOwnerFiberLedger R ≤
      B * canonicalRoughLowQ2DaughterEnergy R +
        C * (R : ℝ) ^ 2 * K

/-- Any q^2/root-scale bound on the unique-owner ledger gives exactly the #791
signed-cell assembly bound with the same coefficients. -/
theorem signedCellQ2EnergyAssemblyBound_of_polarizationOwnerFiber
    {B C : ℝ}
    (hOwner : LowOwnerPolarizationOwnerFiberQ2EnergyBound B C) :
    LowOwnerSignedCellQ2EnergyAssemblyBound B C := by
  intro R K hR hK
  exact
    (sum_lowOwnerFirstOwnerSignedCellTelescope_le_globalPolarizationOwnerFiberLedger R).trans
      (hOwner R K hR hK)

/-- Direct post-#791 RH consumer.

Any estimate on the exact owner-fibre ledger with an admissible q^2 coefficient
-1/4 <= B <= 7/4 closes through the existing CORR-4 chain. -/
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
