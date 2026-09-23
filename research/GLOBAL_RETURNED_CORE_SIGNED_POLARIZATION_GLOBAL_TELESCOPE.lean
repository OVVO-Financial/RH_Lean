import Mathlib
import «research.GLOBAL_RETURNED_CORE_POLARIZATION_CELL_OWNER_FUBINI»
import «research.GLOBAL_RETURNED_CORE_POST789_DIAGONAL_SUBTRACTED_CONTROL»
import «research.GLOBAL_RETURNED_CORE_STOKES_PHYSICAL_FRAME_BRIDGE»

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

/-! ## Collapse the exact signed ledger to the two surviving Stokes coordinates -/

/-- **Exact global collapse.**

The diagonal-retaining unique-owner polarization ledger is the literal final
Stokes boundary.  The existing Stokes DAG then reduces its nonterminal clip to
the two global top toggle coordinates; the only remainder is the already
classified zero/one-owner terminal sector. -/
theorem lowOwnerGlobalPolarizationSignedLedger_eq_topTwoStokesClip_add_terminal
    {R : ℕ} (hR : 56 ≤ R) :
    lowOwnerGlobalPolarizationSignedLedger R =
      lowOwnerCanonicalTopTwoStokesClipNormalForm R hR +
        lowOwnerCanonicalSignedStokesTopTerminalBoundary R := by
  rw [← sum_lowOwnerFirstOwnerSignedCellTelescope_eq_globalPolarizationSignedLedger R]
  rw [sum_lowOwnerFirstOwnerSignedCellTelescope_eq_finalStokesBoundary
    (R := R) (by omega : 2 ≤ R)]
  rw [lowOwnerCanonicalSignedStokesFinalBoundary_eq_clip_add_topTerminal]
  rw [lowOwnerCanonicalSignedStokesClipBoundary_eq_topTwoNormalForm hR]

/-- The #791-aware quantitative target on the already-collapsed top-two Stokes
clip.  Unlike the older root-scale target, this permits the genuine recursive
q² daughter energy to survive with coefficient B. -/
def LowOwnerTopTwoStokesClipQ2EnergyBound (B C : ℝ) : Prop :=
  ∀ R : ℕ, ∀ K : ℝ, ∀ hR : 56 ≤ R,
    LowerMertensCriticalEnvelope R K →
    lowOwnerCanonicalTopTwoStokesClipNormalForm R hR ≤
      B * canonicalRoughLowQ2DaughterEnergy R +
        C * (R : ℝ) ^ 2 * K

/-- A q²-aware top-two clip estimate gives the exact diagonal-retaining signed
ledger bound with the same recursive coefficient.  The exceptional terminal is
uniformly at most four, hence costs only one extra R²K. -/
theorem polarizationSignedLedgerQ2EnergyBound_of_topTwoStokesClip
    {B C : ℝ}
    (hClip : LowOwnerTopTwoStokesClipQ2EnergyBound B C) :
    LowOwnerPolarizationSignedLedgerQ2EnergyBound B (C + 1) := by
  intro R K hR hK
  rw [lowOwnerGlobalPolarizationSignedLedger_eq_topTwoStokesClip_add_terminal hR]
  have hclip := hClip R K hR hK
  have hterm :=
    lowOwnerCanonicalSignedStokesTopTerminalBoundary_le_four hR
  have hKone : 1 ≤ K :=
    lowerMertensCriticalEnvelope_one_le (by omega) hK
  have hscale : (4 : ℝ) ≤ (R : ℝ) ^ 2 * K := by
    have hRreal : (56 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
    nlinarith
  calc
    lowOwnerCanonicalTopTwoStokesClipNormalForm R hR +
        lowOwnerCanonicalSignedStokesTopTerminalBoundary R ≤
      (B * canonicalRoughLowQ2DaughterEnergy R +
        C * (R : ℝ) ^ 2 * K) + 4 := add_le_add hclip hterm
    _ ≤ (B * canonicalRoughLowQ2DaughterEnergy R +
        C * (R : ℝ) ^ 2 * K) + (R : ℝ) ^ 2 * K :=
      add_le_add_left hscale _
    _ = B * canonicalRoughLowQ2DaughterEnergy R +
        (C + 1) * (R : ℝ) ^ 2 * K := by ring

/-- **Sharpened post-#791 Stokes consumer.**

It is enough to control the globally assembled two surviving Stokes
cross-decrements by any q² coefficient in the admissible interval
[-1/4, 7/4], plus a nonnegative root-scale envelope.  The bounded exceptional
terminal does not alter B. -/
theorem riemannHypothesis_of_topTwoStokesClipQ2EnergyBound
    {B C : ℝ}
    (hBlo : -1 / 4 ≤ B) (hBhi : B ≤ 7 / 4) (hC : 0 ≤ C)
    (hClip : LowOwnerTopTwoStokesClipQ2EnergyBound B C) :
    RiemannHypothesis := by
  exact
    riemannHypothesis_of_polarizationSignedLedgerQ2EnergyBound
      hBlo hBhi (by linarith : 0 ≤ C + 1)
      (polarizationSignedLedgerQ2EnergyBound_of_topTwoStokesClip hClip)


end RHLean.Proof
