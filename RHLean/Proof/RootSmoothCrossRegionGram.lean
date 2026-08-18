import Mathlib
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
    simp [RHLean.Analysis.squarePrefixMertens,
      RHLean.Analysis.squarePrefixEndpoint]
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hR : 2 ≤ n + 1 := by omega
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

end RHLean.Proof
