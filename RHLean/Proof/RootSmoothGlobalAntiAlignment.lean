import Mathlib
import RHLean.Proof.RootSmoothCrossRegionGram
import RHLean.Proof.SquareRootAncestryParentFibres

/-!
# Global signed root-smooth anti-alignment

This module states the analytic target in the form that an actual proof must
establish.  The complete root and smooth channels are assembled before every
inequality.  No estimate on either channel separately is introduced.

Write

`D_R = U_R^2 + V_R^2`

for the joint diagonal Gram and

`O_R = U_R V_R`

for the signed root-smooth cross term.  Since the terminal energy is exactly

`D_R + 2 O_R`,

the sharp global anti-alignment statement

`2 O_R <= -D_R + C_eps R^(2+eps)`

is algebraically equivalent to the RH-scale root-smooth energy bound already
formalized in `RootSmoothCrossRegionGram`.

A weaker fixed-delta estimate

`2 O_R <= -(1-delta) D_R + E_R`

leaves the residual `delta D_R`.  The lemma below records that fact exactly, so
such an estimate cannot be treated as a terminal bound unless a further *joint*
contraction controls the residual diagonal without separating the two channels.

Finally, the existing complete parent-fibre ledger is identified with `-O_R`.
This gives a concrete lower-scale attack surface while preserving the full
signed sum.  No fixed-prime, pairwise, or absolute-value estimate occurs here.
-/

noncomputable section

namespace RHLean.Proof

/-- The exact global signed anti-alignment target.  This proposition is open. -/
def RootSmoothGlobalSignedAntiAlignmentStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧
      ∀ R : ℕ, 2 ≤ R →
        2 * squareRootPrimeSmoothOffDiagonalGram R ≤
          -squareRootPrimeSmoothDiagonalGram R +
            C * Real.rpow (R : ℝ) (2 + ε)

/-- A fixed-delta anti-alignment estimate at one scale.  This is deliberately
not declared sufficient for the terminal criterion: it leaves `delta * D_R`. -/
def RootSmoothFixedDeltaAntiAlignmentAt
    (δ E : ℝ) (R : ℕ) : Prop :=
  2 * squareRootPrimeSmoothOffDiagonalGram R ≤
    -(1 - δ) * squareRootPrimeSmoothDiagonalGram R + E

/-- Exact bookkeeping for a fixed-delta estimate.  The unabsorbed term is the
joint diagonal `delta * D_R`; no root or smooth norm has been separated. -/
theorem rootSmoothCrossRegionEnergy_le_deltaDiagonal_add_error
    {δ E : ℝ} {R : ℕ}
    (h : RootSmoothFixedDeltaAntiAlignmentAt δ E R) :
    squareRootPrimeSmoothCrossRegionGram R ≤
      δ * squareRootPrimeSmoothDiagonalGram R + E := by
  unfold RootSmoothFixedDeltaAntiAlignmentAt at h
  unfold squareRootPrimeSmoothCrossRegionGram
  nlinarith

/-- The complete source parent-fibre ledger is the negative root-smooth cross
term.  The sign comes from the ancestry successor being `-V_R`. -/
theorem squareRootPrimeSmoothOffDiagonalGram_eq_neg_sourceLedger
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootPrimeSmoothOffDiagonalGram R =
      -(((squareRootRootSuccessorCrossLedger
          (squareRootEndpoint R) R : ℤ) : ℝ)) := by
  let B := squareRootEndpoint R
  have hB : squareRootEndpoint R ≤ B := by simp [B]
  have hledger :
      (((squareRootRootSuccessorCrossLedger B R : ℤ) : ℝ)) =
        squareRootLegalRootReal B R * squareRootLegalSuccessorReal B R := by
    rw [squareRootRootSuccessorCrossLedger_eq_mul]
    unfold squareRootLegalRootReal squareRootLegalSuccessorReal
    push_cast
    rfl
  rw [squareRootLegalRootReal_eq_primeMass hR hB,
    squareRootLegalSuccessorReal_eq_neg_smoothMass hR hB] at hledger
  unfold squareRootPrimeSmoothOffDiagonalGram
    squareRootPrimeRootReal squareRootSmoothMassReal
  dsimp [B] at hledger
  nlinarith

/-- The same global target expressed on the already-formalized complete
root-by-parent-fibre ledger.  It asks the entire signed ledger to absorb the
joint diagonal, up to the RH-scale error.  No individual ledger entry is
estimated. -/
def RootSmoothSourceLedgerCoercivityStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧
      ∀ R : ℕ, 2 ≤ R →
        squareRootPrimeSmoothDiagonalGram R ≤
          2 * (((squareRootRootSuccessorCrossLedger
            (squareRootEndpoint R) R : ℤ) : ℝ)) +
          C * Real.rpow (R : ℝ) (2 + ε)

/-- Parent-fibre ledger coercivity is exactly the global signed anti-alignment
statement.  The equivalence is only a sign rewrite of the complete ledger. -/
theorem rootSmoothSourceLedgerCoercivity_iff_globalSignedAntiAlignment :
    RootSmoothSourceLedgerCoercivityStatement ↔
      RootSmoothGlobalSignedAntiAlignmentStatement := by
  constructor
  · intro hledger ε hε
    rcases hledger ε hε with ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro R hR
    have h := hbound R hR
    rw [← squareRootPrimeSmoothOffDiagonalGram_eq_neg_sourceLedger R hR] at h
    linarith
  · intro hanti ε hε
    rcases hanti ε hε with ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro R hR
    have h := hbound R hR
    rw [squareRootPrimeSmoothOffDiagonalGram_eq_neg_sourceLedger R hR] at h
    linarith

/-- The sharp global signed anti-alignment theorem is algebraically equivalent
to the complete root-smooth RH-scale energy bound. -/
theorem rootSmoothGlobalSignedAntiAlignment_iff_crossRegionEnergyBound :
    RootSmoothGlobalSignedAntiAlignmentStatement ↔
      RootSmoothCrossRegionEnergyBound := by
  constructor
  · intro hanti ε hε
    rcases hanti ε hε with ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro R hR
    have h := hbound R hR
    unfold squareRootPrimeSmoothCrossRegionGram
    linarith
  · intro henergy ε hε
    rcases henergy ε hε with ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro R hR
    have h := hbound R hR
    unfold squareRootPrimeSmoothCrossRegionGram at h
    linarith

/-- Consequently the complete parent-fibre coercivity statement is itself
exactly the terminal root-smooth energy target. -/
theorem rootSmoothSourceLedgerCoercivity_iff_crossRegionEnergyBound :
    RootSmoothSourceLedgerCoercivityStatement ↔
      RootSmoothCrossRegionEnergyBound := by
  rw [rootSmoothSourceLedgerCoercivity_iff_globalSignedAntiAlignment,
    rootSmoothGlobalSignedAntiAlignment_iff_crossRegionEnergyBound]

/-- Any proof of the sharp global anti-alignment target closes the existing
terminal chain to the Riemann Hypothesis. -/
theorem rootSmoothGlobalSignedAntiAlignment_imp_riemannHypothesis
    (hanti : RootSmoothGlobalSignedAntiAlignmentStatement) :
    RHLean.Analysis.RiemannHypothesisStatement :=
  rootSmoothCrossRegionEnergyBound_imp_riemannHypothesis
    (rootSmoothGlobalSignedAntiAlignment_iff_crossRegionEnergyBound.mp hanti)

end RHLean.Proof
