import Mathlib
import «research.GLOBAL_RETURNED_CORE_SIGNED_POLARIZATION_ENDPOINT»
import «research.GLOBAL_RETURNED_CORE_GLOBAL_DESCENDING_SITE_FUBINI»
import «research.GLOBAL_RETURNED_CORE_DIRICHLET_POLARIZATION_RANK_BASE»
import «research.GLOBAL_RETURNED_CORE_POST789_DIAGONAL_SUBTRACTED_CONTROL»

/-!
# Global signed-polarization telescope after #791

The post-#791 quantitative seam must not sum one positive branch energy for
every descending owner: those branch energies are surviving pre-owner energies
and would be paid repeatedly.

Instead keep the signed Dirichlet polarization intact through the global
greatest-owner filtration.  For one first-owner cell the unrevealed endpoint is
already exactly the signed cell telescope.  The global descending Fubini then
writes each of the three Dirichlet coordinates as

  empty energy = diagonal + sum of unique descending crossing packets.

Subtracting the base and returned-child identities from the incidence identity
therefore gives

  signed cell telescope
    = terminal diagonal polarization
      + sum_r signed polarization crossing packet_r.

The terminal diagonal is nonpositive by the rank-zero theorem.  Hence the
actual signed cell telescope is bounded by the sum of the signed crossing
packets, with every off-diagonal pair charged exactly once.

This is the multiplicity-safe replacement for summing the one-owner positive
branch-energy estimate.  It introduces no new analytic inequality beyond the
already-proved favorable diagonal sign.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Terminal diagonal contribution of the cell-restricted signed polarization. -/
def lowOwnerFirstOwnerDiagonalPolarizationMass
    (R p : ℕ) (sig : Finset ℕ) : ℝ :=
  lowOwnerGlobalDiagonalPairMassWith R
      (lowOwnerFirstOwnerCellIncidenceSite R p sig) -
    lowOwnerGlobalDiagonalPairMassWith R
      (lowOwnerFirstOwnerCellBaseSite R p sig) -
    lowOwnerGlobalDiagonalPairMassWith R
      (lowOwnerFirstOwnerCellReturnedSite R p sig)

/-- Restricting a diagonal arbitrary-site mass to one first-owner base cell is
exactly the sum of the site squares on that cell. -/
theorem lowOwnerGlobalDiagonalPairMassWith_cellRestricted_eq
    (R p : ℕ) (sig : Finset ℕ) (v : ℕ → ℝ) :
    lowOwnerGlobalDiagonalPairMassWith R
        (lowOwnerFirstOwnerCellRestrictedSite R p sig v) =
      ∑ n ∈ lowOwnerFirstOwnerBaseFiber R p sig, v n ^ 2 := by
  rw [lowOwnerGlobalDiagonalPairMassWith_eq_sum_sq]
  have hsub :
      lowOwnerFirstOwnerBaseFiber R p sig ⊆
        lowOwnerNonzeroMobiusCarrier R :=
    lowOwnerFirstOwnerBaseFiber_subset_nonzeroCarrier R p sig
  have hzero :
      ∀ n ∈ lowOwnerNonzeroMobiusCarrier R,
        n ∉ lowOwnerFirstOwnerBaseFiber R p sig →
          lowOwnerFirstOwnerCellRestrictedSite R p sig v n ^ 2 = 0 := by
    intro n _hn hnot
    simp [lowOwnerFirstOwnerCellRestrictedSite, hnot]
  calc
    (∑ n ∈ lowOwnerNonzeroMobiusCarrier R,
      lowOwnerFirstOwnerCellRestrictedSite R p sig v n ^ 2) =
        ∑ n ∈ lowOwnerFirstOwnerBaseFiber R p sig,
          lowOwnerFirstOwnerCellRestrictedSite R p sig v n ^ 2 := by
      exact (Finset.sum_subset hsub hzero).symm
    _ = ∑ n ∈ lowOwnerFirstOwnerBaseFiber R p sig, v n ^ 2 := by
      apply Finset.sum_congr rfl
      intro n hn
      simp [lowOwnerFirstOwnerCellRestrictedSite, hn]

/-- The terminal diagonal polarization is literally the existing sum of
pointwise diagonal Dirichlet-polarization atoms. -/
theorem lowOwnerFirstOwnerDiagonalPolarizationMass_eq_sum_diagAtoms
    (R p : ℕ) (sig : Finset ℕ) :
    lowOwnerFirstOwnerDiagonalPolarizationMass R p sig =
      ∑ a ∈ lowOwnerFirstOwnerBaseFiber R p sig,
        lowOwnerFirstOwnerDirichletPolarizationAtom R p (a, a) := by
  unfold lowOwnerFirstOwnerDiagonalPolarizationMass
    lowOwnerFirstOwnerCellIncidenceSite
    lowOwnerFirstOwnerCellBaseSite
    lowOwnerFirstOwnerCellReturnedSite
  rw [lowOwnerGlobalDiagonalPairMassWith_cellRestricted_eq,
    lowOwnerGlobalDiagonalPairMassWith_cellRestricted_eq,
    lowOwnerGlobalDiagonalPairMassWith_cellRestricted_eq]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _ha
  unfold lowOwnerFirstOwnerDirichletPolarizationAtom
  ring

/-- The fully revealed terminal polarization is favorable. -/
theorem lowOwnerFirstOwnerDiagonalPolarizationMass_nonpos
    (R p : ℕ) (sig : Finset ℕ) :
    lowOwnerFirstOwnerDiagonalPolarizationMass R p sig ≤ 0 := by
  rw [lowOwnerFirstOwnerDiagonalPolarizationMass_eq_sum_diagAtoms]
  exact sum_lowOwnerFirstOwnerDirichletPolarizationAtom_diagonal_nonpos R p sig

/-- **Exact all-owner signed-polarization telescope for one first-owner cell.**

Every descending crossing packet is evaluated at the state in which all larger
prime coordinates have already been revealed, hence each off-diagonal pair is
charged exactly once to its unique greatest fresh owner. -/
theorem lowOwnerFirstOwnerSignedCellTelescope_eq_diagonal_add_descendingCross
    {R p : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    lowOwnerFirstOwnerSignedCellTelescope R p sig =
      lowOwnerFirstOwnerDiagonalPolarizationMass R p sig +
        ∑ r ∈ primesUpTo (squareRootEndpoint R),
          lowOwnerFirstOwnerRevealedPolarizationCrossMass R p sig
            (lowOwnerRevealedPrimesAbove R r) r := by
  rw [← lowOwnerFirstOwnerRevealedPolarizationEnergy_empty_eq_signedCellTelescope hp]
  unfold lowOwnerFirstOwnerRevealedPolarizationEnergy
  have hInc :=
    lowOwnerRevealedPairMassWith_empty_eq_diagonal_add_descendingCross
      R (lowOwnerFirstOwnerCellIncidenceSite R p sig)
  have hBase :=
    lowOwnerRevealedPairMassWith_empty_eq_diagonal_add_descendingCross
      R (lowOwnerFirstOwnerCellBaseSite R p sig)
  have hRet :=
    lowOwnerRevealedPairMassWith_empty_eq_diagonal_add_descendingCross
      R (lowOwnerFirstOwnerCellReturnedSite R p sig)
  rw [hInc, hBase, hRet]
  unfold lowOwnerFirstOwnerDiagonalPolarizationMass
    lowOwnerFirstOwnerRevealedPolarizationCrossMass
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  ring

/-- **Multiplicity-safe one-cell upper bound.**

Only the nonpositive fully revealed diagonal is discarded.  No positive
ownerwise surviving energy is summed. -/
theorem lowOwnerFirstOwnerSignedCellTelescope_le_descendingCross
    {R p : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    lowOwnerFirstOwnerSignedCellTelescope R p sig ≤
      ∑ r ∈ primesUpTo (squareRootEndpoint R),
        lowOwnerFirstOwnerRevealedPolarizationCrossMass R p sig
          (lowOwnerRevealedPrimesAbove R r) r := by
  rw [lowOwnerFirstOwnerSignedCellTelescope_eq_diagonal_add_descendingCross hp]
  have hdiag :=
    lowOwnerFirstOwnerDiagonalPolarizationMass_nonpos R p sig
  linarith

/-- **Global signed-cell reduction to unique descending crossing packets.**

This is the all-first-owner/all-signature version of the preceding theorem.
The right side is still signed; no absolute values or owner-count factors have
been introduced. -/
theorem sum_lowOwnerFirstOwnerSignedCellTelescope_le_descendingPolarizationCross
    (R : ℕ) :
    (∑ p ∈ primesUpTo (squareRootEndpoint R),
      ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
        lowOwnerFirstOwnerSignedCellTelescope R p sig) ≤
      ∑ p ∈ primesUpTo (squareRootEndpoint R),
        ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
          ∑ r ∈ primesUpTo (squareRootEndpoint R),
            lowOwnerFirstOwnerRevealedPolarizationCrossMass R p sig
              (lowOwnerRevealedPrimesAbove R r) r := by
  apply Finset.sum_le_sum
  intro p hpMem
  apply Finset.sum_le_sum
  intro sig _hsig
  exact lowOwnerFirstOwnerSignedCellTelescope_le_descendingCross
    (mem_primesUpTo.mp hpMem).1

/-- The remaining post-#791 quantitative seam, now stated on the unique
descending signed crossing packets rather than on repeatedly-paid branch
energies. -/
def LowOwnerDescendingPolarizationCrossQ2EnergyBound (B C : ℝ) : Prop :=
  ∀ R : ℕ, ∀ K : ℝ,
    56 ≤ R →
    LowerMertensCriticalEnvelope R K →
    (∑ p ∈ primesUpTo (squareRootEndpoint R),
      ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
        ∑ r ∈ primesUpTo (squareRootEndpoint R),
          lowOwnerFirstOwnerRevealedPolarizationCrossMass R p sig
            (lowOwnerRevealedPrimesAbove R r) r) ≤
      B * canonicalRoughLowQ2DaughterEnergy R +
        C * (R : ℝ) ^ 2 * K

/-- Any q²/root-scale bound on the unique signed crossing ledger immediately
gives the #791 signed-cell assembly bound with exactly the same constants. -/
theorem signedCellQ2EnergyAssemblyBound_of_descendingPolarizationCross
    {B C : ℝ}
    (hCross : LowOwnerDescendingPolarizationCrossQ2EnergyBound B C) :
    LowOwnerSignedCellQ2EnergyAssemblyBound B C := by
  intro R K hR hK
  exact
    (sum_lowOwnerFirstOwnerSignedCellTelescope_le_descendingPolarizationCross R).trans
      (hCross R K hR hK)

/-- Direct RH consumer for the new multiplicity-safe crossing target. -/
theorem riemannHypothesis_of_descendingPolarizationCrossQ2EnergyBound
    {B C : ℝ}
    (hBlo : -1 / 4 ≤ B) (hBhi : B ≤ 7 / 4) (hC : 0 ≤ C)
    (hCross : LowOwnerDescendingPolarizationCrossQ2EnergyBound B C) :
    RiemannHypothesis := by
  exact
    riemannHypothesis_of_signedCellQ2EnergyAssemblyBound
      hBlo hBhi hC
      (signedCellQ2EnergyAssemblyBound_of_descendingPolarizationCross hCross)

end RHLean.Proof
