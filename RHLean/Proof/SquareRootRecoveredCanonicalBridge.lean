import Mathlib
import RHLean.Analysis.SquareRootMatchedDegreeOneRecovery
import RHLean.Proof.SquareRootCanonicalOrientedEpsilonBound

/-!
# Recovered matched transport is the existing canonical RH seam

`SquareRootMatchedDegreeOneRecovery` restores the positive-orientation
ancestral correction that is absent from the matched born-smooth/high-transport
channel.  The correction is not a new analytic term: by the exact positive
smooth collapse it restores the complete smooth population before the high
transport is subtracted.

Thus, on the square-root clock,

```text
matched - positivePrimeTransform
  = smooth - transport
  = M(R) - canonicalDefect.
```

The last quantity is precisely the canonical root-downcross seam already used
by `SquareRootCanonicalOrientedEpsilonBound`.  Consequently the existing
frozen/top/far `R^(1+eps)` target feeds the recovered matched statement from
#650 through the already-compiled `9R` comparison and square-prefix energy
bridge.  No arithmetic estimate is added here.
-/

noncomputable section

namespace RHLean.Proof

open RHLean.Analysis

/-- Restoring the ancestral correction turns the matched channel back into the
complete smooth-minus-high-transport endpoint. -/
theorem squareRootRecoveredMatchedTransport_eq_smooth_sub_transport
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootMatchedBornSmoothTransport R -
        squareRootPositiveSmoothPrimeMertensTransform R =
      squareRootSmoothMass (R - 1) -
        squareRootTransportCofactorFirst R := by
  rw [squareRootMatched_sub_positivePrimeTransform_eq_squarePrefixMertens
    R (by omega),
    squarePrefixMertens_eq_squareRootSmooth_sub_transport,
    squareRootTransportMass_pred_eq_cofactorFirst R (by omega)]

/-- The recovered signed target is exactly lower-root Mertens minus the
canonical mate-crosses-root defect.  This is the existing canonical seam, not a
new residual coordinate. -/
theorem squareRootRecoveredMatchedTransport_eq_lowerMertens_sub_canonicalDefect
    (R : ℕ) (hR : 3 ≤ R) :
    squareRootMatchedBornSmoothTransport R -
        squareRootPositiveSmoothPrimeMertensTransform R =
      mertensSummatory R - lowWheelCanonicalDefectLedger R := by
  rw [squareRootMatched_sub_positivePrimeTransform_eq_squarePrefixMertens
    R (by omega),
    squarePrefixMertens_eq_mertens_sub_canonicalDefect R hR]

/-- The q^2/frozen-top-far quantitative target already present in the repository
supplies the recovered #650 bound.  The proof deliberately routes through the
canonical oriented seam and the square-prefix energy criterion; it does not
bound the ancestral transform separately. -/
theorem recoveredMatchedTransportBounded_of_frozenTopFarResidualEpsilon
    (h : OrientedEpsilonBound.SquareRootFrozenTopFarResidualEpsilonBound) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ R : ℕ, 2 ≤ R →
          ‖squareRootMatchedBornSmoothTransport R -
              squareRootPositiveSmoothPrimeMertensTransform R‖ ^ 2 ≤
            C * Real.rpow (R : ℝ) (2 + ε) := by
  apply squarePrefixEnergyBounded_iff_recoveredMatchedTransportBounded.mp
  exact OrientedEpsilonBound.squarePrefixEnergyBounded_of_canonicalOrientedEpsilon
    (OrientedEpsilonBound.canonicalOrientedEpsilon_of_frozenTopFarResidualEpsilon h)

/-- Explicit terminal route through the corrected recovered target.  This is a
wiring theorem only; the frozen/top/far epsilon hypothesis remains the open
arithmetic estimate. -/
theorem riemannHypothesis_of_frozenTopFarResidualEpsilon_via_recovered
    (h : OrientedEpsilonBound.SquareRootFrozenTopFarResidualEpsilonBound) :
    RiemannHypothesis :=
  riemannHypothesis_of_recoveredMatchedTransportBounded
    (recoveredMatchedTransportBounded_of_frozenTopFarResidualEpsilon h)

end RHLean.Proof
