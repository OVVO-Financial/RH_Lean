import Mathlib
import RHLean.Proof.LowWheelCanonicalRepeatedTerminalInternalMate
import RHLean.Proof.LowWheelCanonicalDowncrossBoundaryMultiplicity
import RHLean.Proof.SquareRootCanonicalDowncrossFinalSeam

/-!
# Frozen/top/far residual is not a smaller quantitative seam

The frozen/top/far reductions isolate the canonical defect as

`D_R = FrozenTopFarResidual_R + U_R + Near_R - ERuniq_R`,

where the three terms outside the residual have total norm at most `9*R`.
Thus a linear bound on the residual is not a weaker intermediate theorem: up to
this already-compiled root-scale error it is exactly the old canonical
root-downcross seam.

This file records that quantitative no-go explicitly.  It is deliberately an
inequality/equivalence theorem, not another carrier reindexing.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis

/-- Eventual linear bound on the isolated frozen/top/far residual.  The cutoff
`56` is exactly the cutoff already used by the far-survivor rigidity theorem. -/
def SquareRootFrozenTopFarResidualLinearBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ R : ℕ, 56 ≤ R →
      ‖lowWheelFrozenTopFarResidual R‖ ≤ C * (R : ℝ)

/-- Reverse quantitative comparison.  The existing frozen reduction already
proved `||D_R|| <= ||F_R|| + 9R`; solving the exact same identity for `F_R`
gives the converse inequality with the same root-scale loss. -/
theorem norm_lowWheelFrozenTopFarResidual_le_canonicalDowncross_add_nine_root
    (R : ℕ) (hR : 56 ≤ R) :
    ‖lowWheelFrozenTopFarResidual R‖ ≤
      ‖lowWheelCanonicalDowncrossLedger R‖ + 9 * (R : ℝ) := by
  have hD :=
    lowWheelCanonicalDefectLedger_eq_frozenTopFarResidual_add_rootTerms R hR
  rw [lowWheelCanonicalDefectLedger_eq_downcrossLedger] at hD
  have hU := norm_lowWheelCanonicalDowncrossUniqueParentLedger_le_root R
  have hN := norm_squareRootNearPrimeTransport_le R hR
  have hE := norm_squareRootERuniq_le_root R
  have hF :
      lowWheelFrozenTopFarResidual R =
        lowWheelCanonicalDowncrossLedger R -
          lowWheelCanonicalDowncrossUniqueParentLedger R -
          squareRootNearPrimeTransport R + squareRootERuniq R := by
    linear_combination hD
  rw [hF]
  calc
    ‖lowWheelCanonicalDowncrossLedger R -
        lowWheelCanonicalDowncrossUniqueParentLedger R -
        squareRootNearPrimeTransport R + squareRootERuniq R‖ ≤
      ‖lowWheelCanonicalDowncrossLedger R -
          lowWheelCanonicalDowncrossUniqueParentLedger R -
          squareRootNearPrimeTransport R‖ + ‖squareRootERuniq R‖ :=
        norm_add_le _ _
    _ ≤ (‖lowWheelCanonicalDowncrossLedger R -
          lowWheelCanonicalDowncrossUniqueParentLedger R‖ +
        ‖squareRootNearPrimeTransport R‖) + ‖squareRootERuniq R‖ := by
      gcongr
      exact norm_sub_le _ _
    _ ≤ ((‖lowWheelCanonicalDowncrossLedger R‖ +
          ‖lowWheelCanonicalDowncrossUniqueParentLedger R‖) +
        ‖squareRootNearPrimeTransport R‖) + ‖squareRootERuniq R‖ := by
      gcongr
      exact norm_sub_le _ _
    _ ≤ ((‖lowWheelCanonicalDowncrossLedger R‖ + (R : ℝ)) +
          7 * (R : ℝ)) + (R : ℝ) := by
      gcongr
    _ = ‖lowWheelCanonicalDowncrossLedger R‖ + 9 * (R : ℝ) := by ring

/-- A canonical downcross linear bound gives the isolated residual linear bound;
there is no gain in exponent. -/
theorem frozenTopFarResidualLinear_of_canonicalDowncrossLinear
    (h : SquareRootCanonicalDowncrossLinearBound) :
    SquareRootFrozenTopFarResidualLinearBound := by
  rcases h with ⟨C, hC, hD⟩
  refine ⟨C + 9, by linarith, ?_⟩
  intro R hR
  have hcomp :=
    norm_lowWheelFrozenTopFarResidual_le_canonicalDowncross_add_nine_root R hR
  have hbound := hD R (by omega)
  calc
    ‖lowWheelFrozenTopFarResidual R‖ ≤
        ‖lowWheelCanonicalDowncrossLedger R‖ + 9 * (R : ℝ) := hcomp
    _ ≤ C * (R : ℝ) + 9 * (R : ℝ) := add_le_add_right hbound _
    _ = (C + 9) * (R : ℝ) := by ring

/-- Conversely, an eventual residual linear bound already proves the full
canonical downcross linear seam.  The finitely many roots below `56` are paid
for by the unconditional quartic bound, so no asymptotic hypothesis is hidden
in the cutoff. -/
theorem canonicalDowncrossLinear_of_frozenTopFarResidualLinear
    (h : SquareRootFrozenTopFarResidualLinearBound) :
    SquareRootCanonicalDowncrossLinearBound := by
  rcases h with ⟨C, hC, hF⟩
  let C' : ℝ := C + 9 + (55 : ℝ) ^ 4
  refine ⟨C', by dsimp [C']; positivity, ?_⟩
  intro R hR
  by_cases hlarge : 56 ≤ R
  · have hcomp :=
      norm_lowWheelCanonicalDefectLedger_le_frozenTopFarResidual_add_nine_root
        R hlarge
    rw [lowWheelCanonicalDefectLedger_eq_downcrossLedger] at hcomp
    have hbound := hF R hlarge
    have hCR :
        C * (R : ℝ) + 9 * (R : ℝ) ≤ C' * (R : ℝ) := by
      have hR0 : 0 ≤ (R : ℝ) := Nat.cast_nonneg R
      have hcoeff : C + 9 ≤ C' := by
        dsimp [C']
        positivity
      calc
        C * (R : ℝ) + 9 * (R : ℝ) = (C + 9) * (R : ℝ) := by ring
        _ ≤ C' * (R : ℝ) := mul_le_mul_of_nonneg_right hcoeff hR0
    exact hcomp.trans <| (add_le_add_right hbound _).trans hCR
  · have hRle : R ≤ 55 := by omega
    have hquart := norm_lowWheelCanonicalDowncrossLedger_le_quartic R
    have hcast : (R : ℝ) ≤ (55 : ℝ) := by exact_mod_cast hRle
    have hpow : (R : ℝ) ^ 4 ≤ (55 : ℝ) ^ 4 := by
      gcongr
    have hRone : (1 : ℝ) ≤ (R : ℝ) := by
      exact_mod_cast (show 1 ≤ R by omega)
    have h55nonneg : 0 ≤ (55 : ℝ) ^ 4 := by positivity
    have hscale : (55 : ℝ) ^ 4 ≤ (55 : ℝ) ^ 4 * (R : ℝ) := by
      have hm := mul_le_mul_of_nonneg_left hRone h55nonneg
      simpa using hm
    have hR0 : 0 ≤ (R : ℝ) := Nat.cast_nonneg R
    have hcoeff : (55 : ℝ) ^ 4 ≤ C' := by
      dsimp [C']
      linarith
    have hlast : (55 : ℝ) ^ 4 * (R : ℝ) ≤ C' * (R : ℝ) :=
      mul_le_mul_of_nonneg_right hcoeff hR0
    exact hquart.trans (hpow.trans (hscale.trans hlast))

/-- **Quantitative no-go.**  The isolated frozen/top/far residual linear bound
is exactly the old canonical downcross linear seam, up to already-bounded root
terms.  Isolating this residual therefore did not lower the analytic strength
of the problem. -/
theorem frozenTopFarResidualLinear_iff_canonicalDowncrossLinear :
    SquareRootFrozenTopFarResidualLinearBound ↔
      SquareRootCanonicalDowncrossLinearBound :=
  ⟨canonicalDowncrossLinear_of_frozenTopFarResidualLinear,
    frozenTopFarResidualLinear_of_canonicalDowncrossLinear⟩

/-- In particular, a residual linear bound is already sufficient for the
repository's formal Riemann-hypothesis theorem. -/
theorem riemannHypothesis_of_frozenTopFarResidualLinear
    (h : SquareRootFrozenTopFarResidualLinearBound) :
    RiemannHypothesis :=
  riemannHypothesis_of_canonicalDowncrossLinear
    (canonicalDowncrossLinear_of_frozenTopFarResidualLinear h)

end RHLean.Proof
