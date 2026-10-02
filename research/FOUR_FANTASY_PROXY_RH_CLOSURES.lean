import Mathlib
import «research.VF_MID_FRACTIONAL_PRIME_CLUSTER»
import «research.LI_FLOOR_PRIME_COUNT_FANTASY»
import «research.VF_MID_LINEAR_INTERPOLATION_FANTASY»

/-!
# Four fantasy prime-count proxy closures

This file makes the four counterfactual proxy scenarios explicit and routes
each of them to the same classical von-Koch/RH interface.

The four fantasy identifications are:

1. actual prime count equals continuous Li;
2. actual prime count at square endpoints equals the exact discrete VF-mid
   fractional-prime cluster;
3. actual prime count equals the literal midpoint-to-midpoint VF interpolant;
4. actual prime count equals floor(Li).

Each identification is intentionally an explicit hypothesis.  The deterministic
error theorem for each corresponding proxy is proved elsewhere (or trivially
zero in the continuous-Li case), and each hypothesis is consumed here by the
same classical criterion.
-/

noncomputable section

namespace RHLean.Analysis

/-! ## Fantasy 1: continuous Li is actual prime count -/

/-- Counterfactual identification of actual prime count with continuous Li. -/
def ContinuousLiIdentifiesActualPrimes : Prop :=
  ∀ x : ℝ, 4 ≤ x →
    vfMidPrimeCount x = vfMidLogarithmicIntegralFromTwo x

/-- If actual prime count is exactly Li, the classical discrepancy is identically
zero and therefore satisfies the von-Koch bound with constant zero. -/
theorem primeLiVonKochBounded_of_continuousLiIdentification
    (hident : ContinuousLiIdentifiesActualPrimes) :
    PrimeLiVonKochBoundedStatement := by
  refine ⟨0, le_rfl, ?_⟩
  intro x hx
  unfold vfMidPrimeLiError
  rw [hident x hx]
  simp

/-- Fantasy 1 closes RH through the repository's classical criterion. -/
theorem riemannHypothesis_of_continuousLiIdentification
    (criterion : ClassicalVonKochRHCriterion)
    (hident : ContinuousLiIdentifiesActualPrimes) :
    VFMidRiemannHypothesisStatement :=
  criterion.iff_riemannHypothesis.mp
    (primeLiVonKochBounded_of_continuousLiIdentification hident)

/-! ## Fantasy 2: exact discrete VF-mid fractional cluster is actual primes -/

/-- Counterfactual square-endpoint identification of actual prime count with
the exact integer-lattice VF-mid fractional-prime cluster. -/
def VFMidFractionalClusterIdentifiesActualPrimes : Prop :=
  ∀ R : ℕ, 2 ≤ R →
    vfMidPrimeCount ((R : ℝ) ^ 2) =
      vfMidFractionalPrimeClusterMass R

/-- Under exact identification with the fractional VF cluster, the square
endpoint prime-minus-VF error is identically zero. -/
theorem vfMidSquareEndpointVonKochBounded_of_fractionalClusterIdentification
    (hident : VFMidFractionalClusterIdentifiesActualPrimes) :
    VFMidSquareEndpointVonKochBoundedStatement := by
  refine ⟨0, le_rfl, ?_⟩
  intro R hR
  unfold vfMidPrimeError
  rw [hident R hR, vfMidFractionalPrimeClusterMass_eq_vfMid_sq R hR]
  simp

/-- Fantasy 2 closes RH through the already-compiled square-endpoint bridge. -/
theorem riemannHypothesis_of_vfMidFractionalClusterIdentification
    (criterion : ClassicalVonKochRHCriterion)
    (hident : VFMidFractionalClusterIdentifiesActualPrimes) :
    VFMidRiemannHypothesisStatement :=
  riemannHypothesis_of_vfMidSquareEndpoint criterion
    (vfMidSquareEndpointVonKochBounded_of_fractionalClusterIdentification hident)

/-! ## Fantasies 3 and 4

Fantasy 3 is closed by:
  riemannHypothesis_of_vfMidLinearMidpointIdentification

Fantasy 4 is closed by:
  riemannHypothesis_of_liFloorPrimeCountIdentification

Those theorem statements live with the corresponding proxy definitions so the
error estimates and their RH consumers remain adjacent in the source.
-/

end RHLean.Analysis
