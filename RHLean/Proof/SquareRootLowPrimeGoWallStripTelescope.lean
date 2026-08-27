import Mathlib
import RHLean.Proof.SquareRootPredecessorPrimeCells

/-!
# Go-wall strip telescope

The first-owner wall is already a no-liberty boundary.  Its old-prime windows
should therefore be treated as boundary strips rather than as another interior
matching problem.

For consecutive old primes `ell < q`, the strip

`F_{q^-}(X/q) - F_{q^-}(X/ell)`

has one exact fresh-prime decomposition.  The moving boundary term telescopes
across consecutive primes, while the sole non-endpoint residual is evaluated at
one additional division by `q`:

`F_{q^-}((X/q)/q)`.

This is the square-dilated Go residual.  No estimate is asserted here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

/-- One old-prime Go boundary strip, written in the frozen predecessor universe
immediately before `q`. -/
def squareRootLowPrimeGoWallStripMass (ell q X : ℕ) : ℤ :=
  frozenPrimeUniverseMass (primesUpTo (q - 1)) (X / q) -
    frozenPrimeUniverseMass (primesUpTo (q - 1)) (X / ell)

/-- The moving boundary state after the prime `q` has itself been admitted. -/
def squareRootLowPrimeGoWallBoundaryState (q X : ℕ) : ℤ :=
  frozenPrimeUniverseMass (primesUpTo q) (X / q)

/-- The no-liberty residual after one additional attempted `q` contact. -/
def squareRootLowPrimeGoWallSquareResidual (q X : ℕ) : ℤ :=
  frozenPrimeUniverseMass (primesUpTo (q - 1)) ((X / q) / q)

/-- **Exact one-strip Go descent.**  If `ell` is the previous prime coordinate,
so the predecessor universe before `q` is exactly the universe through `ell`,
then the wall strip is the difference of adjacent moving boundary states plus
one square-dilated residual.

This is the quantitative seam: summing consecutive strips can telescope the
first two terms, while the surviving term has lost an additional factor `q` in
scale. -/
theorem squareRootLowPrimeGoWallStripMass_eq_boundaryDiff_add_squareResidual
    {ell q X : ℕ} (hq : q.Prime)
    (hpred : primesUpTo (q - 1) = primesUpTo ell) :
    squareRootLowPrimeGoWallStripMass ell q X =
      squareRootLowPrimeGoWallBoundaryState q X -
        squareRootLowPrimeGoWallBoundaryState ell X +
          squareRootLowPrimeGoWallSquareResidual q X := by
  have hstep :=
    frozenPrimeUniverseMass_primesUpTo_step_eq_sub_predecessor q (X / q) hq
  unfold predecessorPrimeMass at hstep
  unfold squareRootLowPrimeGoWallStripMass
    squareRootLowPrimeGoWallBoundaryState
    squareRootLowPrimeGoWallSquareResidual
  rw [hpred]
  rw [hpred] at hstep
  omega

/-- The square residual is literally the predecessor-prime mass at the already
reciprocal cutoff `X/q`. -/
theorem squareRootLowPrimeGoWallSquareResidual_eq_predecessorPrimeMass
    (q X : ℕ) :
    squareRootLowPrimeGoWallSquareResidual q X =
      predecessorPrimeMass q (X / q) := by
  rfl

/-- Equivalent `q^2` notation for the square-dilated cutoff. -/
theorem squareRootLowPrimeGoWallSquareResidual_eq_squareCutoff
    (q X : ℕ) :
    squareRootLowPrimeGoWallSquareResidual q X =
      frozenPrimeUniverseMass (primesUpTo (q - 1)) (X / (q * q)) := by
  unfold squareRootLowPrimeGoWallSquareResidual
  rw [Nat.div_div_eq_div_mul]

end RHLean.Proof
