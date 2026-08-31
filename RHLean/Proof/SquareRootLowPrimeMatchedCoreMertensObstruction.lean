import Mathlib
import RHLean.Proof.SquareRootLowPrimeMatchedCoreBound
import RHLean.Proof.SquareRootLowPrimeSmoothTransportRecoupling

/-!
# Matched core as an exact Mertens-minus-middle obstruction

The structural reductions on the low-prime branch eventually expose the signed
core

`core R = bornSmooth R + farUpperSurvivor (R - 1)`.

The far-survivor bridge also gives

`matched R = core R - nearPrimeTransport R`,

while the original square-prefix identity gives

`M(R^2 - 1) = positiveSmooth R + matched R`.

Therefore the core is exactly

`core R = M(R^2 - 1) - (positiveSmooth R - nearPrimeTransport R)`.

The parenthesized term is named `squareRootLowPrimeMiddleMertensMass` below.
It is the signed middle population which, after source reindexing, is the
canonical positive-orientation source mass through the first seven prime
coordinates above the root.

This module deliberately proves only exact identities and equivalences of bound
statements.  In particular, it does **not** assert that bounding the displayed
difference is equivalent to a standalone classical bound on `M(R^2 - 1)`:
the middle term is correlated with the square-prefix Mertens value and may carry
essential cancellation.

No asymptotic estimate, PNT input, Mertens hypothesis, or RH implication is
introduced here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis

/-- The exact signed middle term left when the seven-coordinate near-prime strip
is absorbed back into the positive-orientation square-prefix source mass. -/
def squareRootLowPrimeMiddleMertensMass (R : ℕ) : ℂ :=
  squareRootPositiveSmoothMass R - squareRootNearPrimeTransport R

/-- The predecessor square-prefix sample is literally `M(R^2 - 1)`. -/
theorem squarePrefixMertens_pred_eq_mertens_squareRootEndpoint
    (R : ℕ) (hR : 1 ≤ R) :
    RHLean.Analysis.squarePrefixMertens (R - 1) =
      RHLean.Analysis.mertensSummatory (squareRootEndpoint R) := by
  unfold RHLean.Analysis.squarePrefixMertens
    RHLean.Analysis.squarePrefixEndpoint squareRootEndpoint
  rw [Nat.sub_add_cancel hR]

/-- **Exact obstruction identity in square-prefix coordinates.** -/
theorem squareRootLowPrimeMatchedCore_eq_squarePrefixMertens_sub_middleMertensMass
    (R : ℕ) (hR : 56 ≤ R) :
    squareRootLowPrimeMatchedCore R =
      RHLean.Analysis.squarePrefixMertens (R - 1) -
        squareRootLowPrimeMiddleMertensMass R := by
  unfold squareRootLowPrimeMiddleMertensMass
  rw [squarePrefixMertens_eq_positiveSmooth_add_matched R (by omega)]
  rw [squareRootMatchedBornSmoothTransport_eq_core_sub_near R hR]
  ring

/-- **Exact obstruction identity in literal Mertens coordinates.**

With `X = R^2 - 1`, the matched core is exactly `M(X)` minus the signed middle
population. -/
theorem squareRootLowPrimeMatchedCore_eq_mertens_sub_middleMertensMass
    (R : ℕ) (hR : 56 ≤ R) :
    squareRootLowPrimeMatchedCore R =
      RHLean.Analysis.mertensSummatory (squareRootEndpoint R) -
        squareRootLowPrimeMiddleMertensMass R := by
  rw [← squarePrefixMertens_pred_eq_mertens_squareRootEndpoint R (by omega)]
  exact squareRootLowPrimeMatchedCore_eq_squarePrefixMertens_sub_middleMertensMass
    R hR

/-- Norm-form Mertens-minus-middle target, with the constant left free. -/
def SquareRootLowPrimeMertensMiddleBound (C : ℝ) (R : ℕ) : Prop :=
  ‖RHLean.Analysis.mertensSummatory (squareRootEndpoint R) -
      squareRootLowPrimeMiddleMertensMass R‖ ≤ C * (R : ℝ)

/-- The matched-core norm bound is exactly the Mertens-minus-middle norm bound. -/
theorem squareRootLowPrimeMatchedCoreBound_iff_mertensMiddleBound
    {C : ℝ} {R : ℕ} (hR : 56 ≤ R) :
    SquareRootLowPrimeMatchedCoreBound C R ↔
      SquareRootLowPrimeMertensMiddleBound C R := by
  unfold SquareRootLowPrimeMatchedCoreBound SquareRootLowPrimeMertensMiddleBound
  rw [squareRootLowPrimeMatchedCore_eq_mertens_sub_middleMertensMass R hR]

/-- Real-coordinate form of the same obstruction.  This is the minimal target
actually consumed by the terminal real imbalance. -/
def SquareRootLowPrimeMertensMiddleRealBound (C : ℝ) (R : ℕ) : Prop :=
  |(RHLean.Analysis.mertensSummatory (squareRootEndpoint R) -
      squareRootLowPrimeMiddleMertensMass R).re| ≤ C * (R : ℝ)

/-- The minimal matched-core real bound is exactly the corresponding
Mertens-minus-middle real bound. -/
theorem squareRootLowPrimeMatchedCoreRealBound_iff_mertensMiddleRealBound
    {C : ℝ} {R : ℕ} (hR : 56 ≤ R) :
    SquareRootLowPrimeMatchedCoreRealBound C R ↔
      SquareRootLowPrimeMertensMiddleRealBound C R := by
  unfold SquareRootLowPrimeMatchedCoreRealBound
    SquareRootLowPrimeMertensMiddleRealBound
  rw [squareRootLowPrimeMatchedCore_eq_mertens_sub_middleMertensMass R hR]

end RHLean.Proof