import Mathlib
import RHLean.Proof.MatchedFarSurvivorBridge
import RHLean.Analysis.NativePNTTransfer

/-!
# Stable far-wall logarithmic-integral asymptotic

This module attacks only the deterministic main term of the stable far wall.
The target is the unconditional second-order asymptotic

```text
(log X_R)^2 / X_R * W_R -> -1,
```

with `X_R = R^2 - 1`.  The exact wall decomposition is first transported to
the reciprocal quotient fibres.  No RH-scale estimate is assumed here.
-/

noncomputable section

open Filter
open scoped BigOperators Topology

namespace RHLean.Proof

/-- The far wall in the quotient-fibre coordinates where the deterministic Li
mass and the actual-prime discrepancy are both indexed by the lower Mertens
quotient. -/
theorem squareRootFarPrimeTransport_eq_reciprocalPNTBulk_add_error_sub_near
    (R : ℕ) (hR : 56 ≤ R) :
    squareRootFarPrimeTransport R =
      RHLean.Analysis.primeSieveReciprocalPNTBulk R (squareRootEndpoint R) +
        RHLean.Analysis.primeSieveReciprocalPNTError R (squareRootEndpoint R) -
          squareRootNearPrimeTransport R := by
  rw [squareRootFarPrimeTransport_eq_pntBulk_add_pntError_sub_near R hR,
    RHLean.Analysis.primeSievePNTBulk_eq_reciprocalPNTBulk,
    RHLean.Analysis.primeSievePNTError_eq_reciprocalPNTError]

end RHLean.Proof
