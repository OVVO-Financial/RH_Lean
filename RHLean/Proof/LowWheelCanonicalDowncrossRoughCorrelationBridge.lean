import Mathlib
import RHLean.Proof.LowWheelCanonicalDefectReduction
import RHLean.Analysis.SquareRootCanonicalRoughCovariance

/-!
# Canonical downcross = the old canonical rough correlation seam

The current root-downcross ledger and the earlier canonical rough-prime
correlation were obtained by very different coordinate systems.  They are not
independent hard populations.

At the square endpoint the downcross identity says

`M(X_R) = M(R) - D_R`,

while the rough-prime renewal/covariance identity says

`C_R = M(R-1) - M(X_R)`.

Eliminating the common endpoint gives

`D_R = C_R + (M(R) - M(R-1))`.

Thus the new repeated-parent frontier is exactly the old canonical rough seam,
up to the single root increment.  This theorem records that synthesis directly
in the kernel.  It is an identity, not a new estimate.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

/-- The #496 downcross object and the older rough-prime correlation are the
same hard scalar up to the one-step root increment. -/
theorem lowWheelCanonicalDowncrossLedger_eq_canonicalRoughCorrelation_add_rootIncrement
    (R : ℕ) (hR : 3 ≤ R) :
    lowWheelCanonicalDowncrossLedger R =
      squareRootCanonicalRoughCorrelation R +
        (mertensSummatory R - mertensSummatory (R - 1)) := by
  have hdown :=
    squarePrefixMertens_eq_mertens_sub_canonicalDowncross R hR
  have hcorr :=
    squareRootCanonicalRoughCorrelation_eq_mertens_pred_sub_endpoint
      R (by omega : 2 ≤ R)
  have hprefix :
      squarePrefixMertens (R - 1) =
        mertensSummatory (squareRootEndpoint R) := by
    unfold squarePrefixMertens squarePrefixEndpoint squareRootEndpoint
    have hpred : R - 1 + 1 = R := Nat.sub_add_cancel (by omega : 1 ≤ R)
    rw [hpred]
  rw [hprefix] at hdown
  linear_combination hdown - hcorr

end RHLean.Proof
