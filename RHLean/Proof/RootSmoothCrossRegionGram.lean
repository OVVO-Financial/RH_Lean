import Mathlib
import RHLean.Proof.SquareRootAncestryParentFibres
import RHLean.Proof.SquareRootCrossRegionAmplification
import RHLean.Proof.SquareRootLegalAncestryGramReduction
import RHLean.Analysis.MertensEnergyRHForward

/-!
# Root-smooth cross-region Gram

The centered distinguished-prime coefficient Gram is not used in this module.
The analytic object is the already-formalized square-root ancestry root together
with the complete smooth ancestry mass, kept signed until after recombination.

At the complete-square endpoint `X_R = R^2 - 1`, the existing ancestry theorems
identify the real root-smooth state with

`M(X_R) - 1`.

The corresponding energy is therefore exactly the squared norm of the shifted
square-prefix Mertens state.  No root norm and no smooth norm is estimated
separately.

The module also records the existing orientation decomposition

`M(X_R) = positiveSmooth(R) + matched(R)`

where `matched(R) = bornSmooth(R) - transport(R)`.  This identity is important
for notation: the born-smooth/high-transport matched channel is a signed
cross-region subchannel, but it is not by itself the full terminal square-prefix
state unless the positive-smooth term is also accounted for.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

/-- Exact terminal reconstruction of the signed ancestry root and complete
smooth mass before any norm is taken. -/
theorem rootSmoothCrossRegionState_eq_shiftedSquarePrefixMertens
    (R : ℕ) (hR : 2 ≤ R) :
    ((squareRootPrimeRootReal R + squareRootSmoothMassReal R : ℝ) : ℂ) =
      RHLean.Analysis.squarePrefixMertens (R - 1) - 1 :=
  squareRootPrimeSmoothState_cast_eq_shiftedSquarePrefixMertens R hR

/-- The same terminal state in real arithmetic coordinates. -/
theorem rootSmoothCrossRegionStateReal_eq_shiftedSquarePrefixMertens_re
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootPrimeRootReal R + squareRootSmoothMassReal R =
      (RHLean.Analysis.squarePrefixMertens (R - 1)).re - 1 :=
  squareRootPrimeSmoothState_eq_shiftedSquarePrefixMertens_re R hR

/-- Exact unshifted square-prefix reconstruction in the born-smooth/high-
transport coordinates already present in the repository.  No estimate is made
on either summand. -/
theorem rootSmoothCrossRegion_squarePrefix_eq_positiveSmooth_add_matched
    (R : ℕ) (hR : 2 ≤ R) :
    RHLean.Analysis.squarePrefixMertens (R - 1) =
      squareRootPositiveSmoothMass R +
        squareRootMatchedBornSmoothTransport R := by
  exact squarePrefixMertens_eq_positiveSmooth_add_matched R (by omega)

/-- Shifted form of the same exact reconstruction.  This makes explicit that
`bornSmooth - transport` is the matched signed subchannel, while the complete
root-smooth terminal state also contains the positive-smooth contribution. -/
theorem rootSmoothCrossRegionState_eq_positiveSmooth_add_matchedShift
    (R : ℕ) (hR : 2 ≤ R) :
    ((squareRootPrimeRootReal R + squareRootSmoothMassReal R : ℝ) : ℂ) =
      squareRootPositiveSmoothMass R +
        (squareRootMatchedBornSmoothTransport R - 1) := by
  rw [rootSmoothCrossRegionState_eq_shiftedSquarePrefixMertens R hR]
  rw [rootSmoothCrossRegion_squarePrefix_eq_positiveSmooth_add_matched R hR]
  ring

/-- Exact root-smooth Gram reconstruction.  The full signed interaction is
retained before the norm; this is precisely `D_R + 2 O_R` from the ancestry
root and complete smooth channels. -/
theorem rootSmoothCrossRegionGram_eq_shiftedSquarePrefixEnergy
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootPrimeSmoothCrossRegionGram R =
      ‖RHLean.Analysis.squarePrefixMertens (R - 1) - 1‖ ^ 2 :=
  squareRootPrimeSmoothCrossRegionGram_eq_shiftedSquarePrefixMertens_norm_sq R hR

/-- The open RH-scale bound on the complete signed root-smooth cross-region
Gram.  This is a proposition only; no analytic estimate is asserted here. -/
def RootSmoothCrossRegionEnergyBound : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧
      ∀ R : ℕ, 2 ≤ R →
        squareRootPrimeSmoothCrossRegionGram R ≤
          C * Real.rpow (R : ℝ) (2 + ε)

private theorem norm_sq_le_two_shifted_add_two (z : ℂ) :
    ‖z‖ ^ 2 ≤ 2 * ‖z - 1‖ ^ 2 + 2 := by
  have hnorm : ‖z‖ ≤ ‖z - 1‖ + 1 := by
    have h := norm_add_le (z - 1) (1 : ℂ)
    simpa only [sub_add_cancel, norm_one] using h
  have hz : 0 ≤ ‖z‖ := norm_nonneg _
  have hshift : 0 ≤ ‖z - 1‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖z - 1‖ - 1)]

/-- The complete signed root-smooth RH-scale bound implies the repository's
square-prefix Mertens energy criterion.  The only auxiliary inequality removes
the harmless exceptional-source shift `-1`; it never separates root from
smooth. -/
theorem squarePrefixEnergyBounded_of_rootSmoothCrossRegionEnergyBound
    (hroot : RootSmoothCrossRegionEnergyBound) :
    RHLean.Analysis.SquarePrefixEnergyBoundedStatement := by
  intro ε hε
  rcases hroot ε hε with ⟨C, hC, hbound⟩
  refine ⟨2 * C + 2, by positivity, ?_⟩
  intro n
  by_cases hn : n = 0
  · subst n
    have hconst : 0 ≤ 2 * C + 2 := by positivity
    simpa [RHLean.Analysis.squarePrefixMertens,
      RHLean.Analysis.squarePrefixEndpoint] using hconst
  · have hR : 2 ≤ n + 1 := by omega
    have hshift := hbound (n + 1) hR
    rw [rootSmoothCrossRegionGram_eq_shiftedSquarePrefixEnergy (n + 1) hR] at hshift
    simp only [Nat.add_sub_cancel] at hshift
    have hsum := norm_sq_le_two_shifted_add_two
      (RHLean.Analysis.squarePrefixMertens n)
    have hbase : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
    have hpow :
        1 ≤ Real.rpow ((n + 1 : ℕ) : ℝ) (2 + ε) :=
      Real.one_le_rpow hbase (by linarith)
    nlinarith

/-- The root-smooth bound therefore implies the ordinary full Mertens energy
criterion by the already-proved square-sampling interpolation. -/
theorem mertensEnergyBounded_of_rootSmoothCrossRegionEnergyBound
    (hroot : RootSmoothCrossRegionEnergyBound) :
    RHLean.Analysis.MertensEnergyBoundedStatement :=
  RHLean.Analysis.mertensEnergyBounded_of_squarePrefixEnergyBounded
    (squarePrefixEnergyBounded_of_rootSmoothCrossRegionEnergyBound hroot)

/-- Exact terminal implication: once the complete signed root-smooth bound is
proved, the repository's constructed Mertens-to-RH forward theorem closes the
Riemann Hypothesis. -/
theorem rootSmoothCrossRegionEnergyBound_imp_riemannHypothesis
    (hroot : RootSmoothCrossRegionEnergyBound) :
    RHLean.Analysis.RiemannHypothesisStatement := by
  change RiemannHypothesis
  exact RHLean.Analysis.riemannHypothesis_of_mertensEnergy
    (mertensEnergyBounded_of_rootSmoothCrossRegionEnergyBound hroot)

/-! ## Exact global anti-alignment target -/

/-- The exact global signed anti-alignment target.  The complete root and smooth
channels are assembled before the inequality.  This proposition is open. -/
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
joint diagonal `delta * D_R`; no root or smooth energy has been separated. -/
theorem rootSmoothCrossRegionEnergy_le_deltaDiagonal_add_error
    {δ E : ℝ} {R : ℕ}
    (h : RootSmoothFixedDeltaAntiAlignmentAt δ E R) :
    squareRootPrimeSmoothCrossRegionGram R ≤
      δ * squareRootPrimeSmoothDiagonalGram R + E := by
  unfold RootSmoothFixedDeltaAntiAlignmentAt at h
  unfold squareRootPrimeSmoothCrossRegionGram
  nlinarith

/-- The complete source parent-fibre ledger is the negative root-smooth cross
term.  The sign comes from the ancestry successor being the negative of the
complete smooth mass. -/
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
  rw [squareRootLegalRootReal_eq_primeMass hR hB,
    squareRootLegalSuccessorReal_eq_neg_smoothMass hR hB] at hledger
  unfold squareRootPrimeSmoothOffDiagonalGram
    squareRootPrimeRootReal squareRootSmoothMassReal
  dsimp [B] at hledger
  nlinarith

/-- The same global target on the already-formalized complete root-by-parent-
fibre ledger.  It asks the entire signed ledger to absorb the joint diagonal;
no individual ledger entry is estimated. -/
def RootSmoothSourceLedgerCoercivityStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧
      ∀ R : ℕ, 2 ≤ R →
        squareRootPrimeSmoothDiagonalGram R ≤
          2 * (((squareRootRootSuccessorCrossLedger
            (squareRootEndpoint R) R : ℤ) : ℝ)) +
          C * Real.rpow (R : ℝ) (2 + ε)

/-- Parent-fibre ledger coercivity is exactly the global signed anti-alignment
statement.  This is only a sign rewrite of the complete global ledger. -/
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

/-- Consequently complete parent-fibre ledger coercivity is itself exactly the
terminal root-smooth energy target. -/
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