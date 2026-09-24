import Mathlib
import «research.GLOBAL_RETURNED_CORE_RAW_PARENT_BRANCH_CROSS_AMPLITUDE»
import «research.GLOBAL_RETURNED_CORE_SIGNED_POLARIZATION_ENDPOINT»
import «research.GLOBAL_RETURNED_CORE_SIGNED_POLARIZATION_GLOBAL_TELESCOPE»

/-!
# Complete branch energy through the global top-two Stokes telescope

Evaluate the completed branch at the largest physical prime, once per first
owner. The revealed set is empty, so incidence energy minus same-branch energy
is exactly the original signed cell. The largest first owner itself has no
larger branch coordinate and is retained separately.

This composes the endpoint-energy completion with the global two-toggle Fubini
without paying one surviving energy at every descending owner. It also exposes
the exact result: Q_R^2 plus the existing signed cross/diagonal remainder.
The endpoint completion does not identify that remainder with the exceptional
terminal sector, and no contraction estimate is asserted.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic StokesTerminalFrame

attribute [local instance] Classical.propDecidable

/-- There is no physical prime coordinate above the global top prime. -/
theorem lowOwnerRevealedPrimesAbove_topPrime_eq_empty
    {R : ℕ} (hR : 56 ≤ R) :
    lowOwnerRevealedPrimesAbove R (topPrime R hR) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro r hr
  rcases Finset.mem_filter.mp hr with ⟨hrMem, htop⟩
  have hrle : r ≤ topPrime R hR := Finset.le_max' _ r hrMem
  omega

/-- The completed physical branch is a surviving signed cell, with its
same-branch subtraction retained. It is not an ownerwise energy decrement. -/
theorem lowOwnerFirstOwnerSignedCellTelescope_eq_topCompletedBranch
    {R p : ℕ} (hR : 56 ≤ R)
    (hpMem : p ∈ primesUpTo (squareRootEndpoint R))
    (hpNe : p ≠ topPrime R hR) (sig : Finset ℕ) :
    lowOwnerFirstOwnerSignedCellTelescope R p sig =
      lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceEnergy
          R p sig (topPrime R hR) -
        lowOwnerFirstOwnerBranchSameBranchMass R p sig (topPrime R hR) := by
  have hp := (mem_primesUpTo.mp hpMem).1
  have hple : p ≤ topPrime R hR := Finset.le_max' _ p hpMem
  have hpt : p < topPrime R hR := by omega
  have h :=
    lowOwnerFirstOwnerRevealedPolarizationEnergy_descending_eq_branchEnergy_add_endpointCorrection_sub_sameBranch
      (R := R) (p := p) (r := topPrime R hR) (sig := sig)
      (by omega) hp (topPrime_prime hR) hpt
  rw [lowOwnerRevealedPrimesAbove_topPrime_eq_empty hR,
    lowOwnerFirstOwnerRevealedPolarizationEnergy_empty_eq_signedCellTelescope hp]
    at h
  rw [lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceEnergy_eq_branchThresholdEnergy_add_endpointCorrection
    (by omega) hp (topPrime_prime hR)]
  exact h

/-- Once-per-first-owner completed branch assembly. The top first owner is
the empty-schedule sector and is retained literally. -/
def lowOwnerTopCompletedBranchAssembly (R : ℕ) (hR : 56 ≤ R) : ℝ :=
  (∑ p ∈ (primesUpTo (squareRootEndpoint R)).erase (topPrime R hR),
    ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
      (lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceEnergy
          R p sig (topPrime R hR) -
        lowOwnerFirstOwnerBranchSameBranchMass R p sig (topPrime R hR))) +
    ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R (topPrime R hR),
      lowOwnerFirstOwnerSignedCellTelescope R (topPrime R hR) sig

/-- The global branch assembly is exactly the signed-cell ledger. -/
theorem lowOwnerTopCompletedBranchAssembly_eq_signedCells
    {R : ℕ} (hR : 56 ≤ R) :
    lowOwnerTopCompletedBranchAssembly R hR =
      ∑ p ∈ primesUpTo (squareRootEndpoint R),
        ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
          lowOwnerFirstOwnerSignedCellTelescope R p sig := by
  unfold lowOwnerTopCompletedBranchAssembly
  rw [← Finset.sum_erase_add _ _ (topPrime_mem hR)]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro sig _hsig
  exact (lowOwnerFirstOwnerSignedCellTelescope_eq_topCompletedBranch
    hR (Finset.mem_erase.mp hp).2 (Finset.mem_erase.mp hp).1 sig).symm

/-- **Completion composed with global top-two Stokes Fubini.** All endpoint
and same-branch terms have remained inside the signed assembly. -/
theorem lowOwnerTopCompletedBranchAssembly_eq_topTwo_add_terminal
    {R : ℕ} (hR : 56 ≤ R) :
    lowOwnerTopCompletedBranchAssembly R hR =
      lowOwnerCanonicalTopTwoStokesClipNormalForm R hR +
        lowOwnerCanonicalSignedStokesTopTerminalBoundary R := by
  rw [lowOwnerTopCompletedBranchAssembly_eq_signedCells hR,
    sum_lowOwnerFirstOwnerSignedCellTelescope_eq_globalPolarizationSignedLedger]
  exact lowOwnerGlobalPolarizationSignedLedger_eq_topTwoStokesClip_add_terminal hR

/-- **Exact output of the completed two-toggle assembly.** The q² column
square is accompanied by the signed endpoint cross/diagonal remainder. -/
theorem lowOwnerTopCompletedBranchAssembly_eq_q2Sq_add_signedRemainder
    {R : ℕ} (hR : 56 ≤ R) :
    lowOwnerTopCompletedBranchAssembly R hR =
      lowOwnerReciprocalMertensColumnReal R ^ 2 +
        lowOwnerPost789SignedCrossDiagonalRemainder R := by
  rw [lowOwnerTopCompletedBranchAssembly_eq_signedCells hR,
    sum_lowOwnerFirstOwnerSignedCellTelescope_eq_finalStokesBoundary
      (R := R) (by omega : 2 ≤ R)]
  exact lowOwnerCanonicalSignedStokesFinalBoundary_eq_q2Sq_add_post789Remainder hR

/-- The exceptional terminal is subtracted from the clip; it does not replace
the signed endpoint cross term. -/
theorem lowOwnerTopTwoStokesClip_eq_q2Sq_add_signedRemainder_sub_terminal
    {R : ℕ} (hR : 56 ≤ R) :
    lowOwnerCanonicalTopTwoStokesClipNormalForm R hR =
      lowOwnerReciprocalMertensColumnReal R ^ 2 +
        lowOwnerPost789SignedCrossDiagonalRemainder R -
        lowOwnerCanonicalSignedStokesTopTerminalBoundary R := by
  have ht := lowOwnerTopCompletedBranchAssembly_eq_topTwo_add_terminal hR
  have hq := lowOwnerTopCompletedBranchAssembly_eq_q2Sq_add_signedRemainder hR
  linarith

/-- Exact remaining pointwise inequality, with the actual Q² retained. This
equivalence introduces no estimate or additional analytic assumption. -/
theorem lowOwnerTopTwoStokesClip_q2_bound_iff_signedRemainder
    {R : ℕ} (hR : 56 ≤ R) (B C K : ℝ) :
    (lowOwnerCanonicalTopTwoStokesClipNormalForm R hR ≤
      B * canonicalRoughLowQ2DaughterEnergy R + C * (R : ℝ) ^ 2 * K) ↔
    (lowOwnerPost789SignedCrossDiagonalRemainder R ≤
      B * canonicalRoughLowQ2DaughterEnergy R -
        lowOwnerReciprocalMertensColumnReal R ^ 2 + C * (R : ℝ) ^ 2 * K +
        lowOwnerCanonicalSignedStokesTopTerminalBoundary R) := by
  rw [lowOwnerTopTwoStokesClip_eq_q2Sq_add_signedRemainder_sub_terminal hR]
  constructor <;> intro h <;> linarith

/-- The already-proved quarter-frame pays the q² column, leaving the signed
remainder and the literal exceptional terminal visible. -/
theorem lowOwnerTopTwoStokesClip_le_quarter_q2_add_signedRemainder_sub_terminal
    {R : ℕ} (hR : 56 ≤ R) :
    lowOwnerCanonicalTopTwoStokesClipNormalForm R hR ≤
      (1 / 4 : ℝ) * canonicalRoughLowQ2DaughterEnergy R +
        lowOwnerPost789SignedCrossDiagonalRemainder R -
        lowOwnerCanonicalSignedStokesTopTerminalBoundary R := by
  rw [lowOwnerTopTwoStokesClip_eq_q2Sq_add_signedRemainder_sub_terminal hR]
  have h := lowOwnerReciprocalMertensColumnReal_sq_le_quarter_lowQ2DaughterEnergy R
  linarith

end RHLean.Proof
