import Mathlib
import RHLean.Proof.SquareRootAncestryParentFibres
import RHLean.Proof.LowWheelDoubleCubeSequentialFold

/-!
# Sequential low-wheel operator inside the ancestry cross ledger

The ancestry and square-root decompositions already identify the two scalar
factors of the legal root-successor cross term:

`root = positiveSmooth - transport`,
`successor = 1 - bornSmooth`.

The new transport realization rewrites `transport` as the full two-copy
low-prime Boolean cube.  Therefore the actual RH-critical ancestry cross ledger
contains the double-cube operator *exactly*, before any norm is taken.

At a prime root cutoff `R`, the sequential fresh-prime fold can then be
substituted as well: the transport factor is the geometrically localized
`R`-coordinate shell state built over the previously processed prime universe
`primesUpTo (R-1)`.

This module is only an exact bridge.  It asserts no RH-scale estimate.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

/-- The ancestry root factor with the high transport replaced by the symmetric
low-wheel double cube. -/
theorem sourceRootPrefix_cast_eq_positiveSmooth_sub_lowWheelDoubleCube
    {B R : ℕ} (hR : 2 ≤ R)
    (hB : squareRootEndpoint R ≤ B) :
    ((sourceRootPrefix B (R - 1) : ℤ) : ℂ) =
      squareRootPositiveSmoothMass R -
        lowWheelDoubleCubeTransportLedger R := by
  rw [sourceRootPrefix_cast_eq_positiveSmooth_sub_transport hR hB]
  rw [← squareRootTransportCofactorFirst_eq_primeFirst]
  rw [squareRootTransportCofactorFirst_eq_lowWheelDoubleCube R hR]

/-- **Cross-ledger factorization through the low-wheel operator.**  The exact
root-successor cross term is the product of the positive-smooth correction minus
the two-cube transport operator and the born-smooth successor factor. -/
theorem squareRootRootSuccessorCrossLedger_cast_eq_lowWheelDoubleCube
    {B R : ℕ} (hR : 2 ≤ R)
    (hB : squareRootEndpoint R ≤ B) :
    ((squareRootRootSuccessorCrossLedger B R : ℤ) : ℂ) =
      (squareRootPositiveSmoothMass R -
          lowWheelDoubleCubeTransportLedger R) *
        (1 - squareRootBornSmoothMass R) := by
  rw [squareRootRootSuccessorCrossLedger_eq_mul]
  push_cast
  rw [sourceRootPrefix_cast_eq_positiveSmooth_sub_lowWheelDoubleCube hR hB,
    sourceSuccessorPrefix_cast_eq_one_sub_bornSmooth hR hB]

/-- At a prime root coordinate, the RH-critical cross ledger contains the
literal sequential fresh-prime shell state: every transport contribution is
indexed only by prime faces from the already-processed universe
`primesUpTo (R-1)` and lies on the two `R`-scaled geometric shells. -/
theorem squareRootRootSuccessorCrossLedger_cast_eq_sequentialShells_of_prime
    {B R : ℕ} (hR : 2 ≤ R) (hprime : R.Prime)
    (hB : squareRootEndpoint R ≤ B) :
    ((squareRootRootSuccessorCrossLedger B R : ℤ) : ℂ) =
      (squareRootPositiveSmoothMass R -
        (∑ u ∈ (RHLean.Arithmetic.primesUpTo (R - 1)).powerset,
          ∑ t ∈ (RHLean.Arithmetic.primesUpTo (R - 1)).powerset,
            ∑ k ∈ Finset.Icc 1 (squareRootEndpoint R),
              (RHLean.Arithmetic.booleanCubeSign u : ℂ) *
                (RHLean.Arithmetic.booleanCubeSign t : ℂ) *
                lowWheelSequentialShellDifferenceC R R (squareRootEndpoint R)
                  (RHLean.Arithmetic.primeFaceProduct t * k)
                  ((RHLean.Arithmetic.primeFaceProduct u *
                    RHLean.Arithmetic.primeFaceProduct t) * k))) *
        (1 - squareRootBornSmoothMass R) := by
  rw [squareRootRootSuccessorCrossLedger_cast_eq_lowWheelDoubleCube hR hB]
  have hshell :=
    squareRootTransportCofactorFirst_eq_sequentialShells_of_prime R hR hprime
  have hdouble :
      lowWheelDoubleCubeTransportLedger R =
        ∑ u ∈ (RHLean.Arithmetic.primesUpTo (R - 1)).powerset,
          ∑ t ∈ (RHLean.Arithmetic.primesUpTo (R - 1)).powerset,
            ∑ k ∈ Finset.Icc 1 (squareRootEndpoint R),
              (RHLean.Arithmetic.booleanCubeSign u : ℂ) *
                (RHLean.Arithmetic.booleanCubeSign t : ℂ) *
                lowWheelSequentialShellDifferenceC R R (squareRootEndpoint R)
                  (RHLean.Arithmetic.primeFaceProduct t * k)
                  ((RHLean.Arithmetic.primeFaceProduct u *
                    RHLean.Arithmetic.primeFaceProduct t) * k) := by
    rw [← squareRootTransportCofactorFirst_eq_lowWheelDoubleCube R hR]
    exact hshell
  rw [hdouble]

end RHLean.Proof
