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

/-- Squaring the elementary `log R / sqrt R -> 0` limit gives the normalization
needed for every root-scale remainder in the wall decomposition. -/
private theorem log_sq_div_natCast_atTop :
    Tendsto (fun R : ℕ => (Real.log (R : ℝ)) ^ 2 / (R : ℝ)) atTop (𝓝 0) := by
  have h := RHLean.Analysis.nativeLog_div_sqrt_natCast_atTop
  have hsq := h.mul h
  rw [zero_mul] at hsq
  refine hsq.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with R hR
  have hRnonneg : (0 : ℝ) ≤ (R : ℝ) := by positivity
  rw [div_mul_div_comm, Real.mul_self_sqrt hRnonneg]
  ring

/-- The seven-coordinate strip omitted by the stable far cutoff is negligible
on the natural square-root normalization.  This is completely elementary and
uses no prime-density information. -/
theorem squareRootNearPrimeTransport_logSq_div_RSq_tendsto_zero :
    Tendsto
      (fun R : ℕ =>
        ‖squareRootNearPrimeTransport R‖ * (Real.log (R : ℝ)) ^ 2 /
          (R : ℝ) ^ 2)
      atTop (𝓝 0) := by
  have hupper :
      Tendsto (fun R : ℕ => 7 * ((Real.log (R : ℝ)) ^ 2 / (R : ℝ)))
        atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul log_sq_div_natCast_atTop :
      Tendsto (fun R : ℕ =>
        (7 : ℝ) * ((Real.log (R : ℝ)) ^ 2 / (R : ℝ))) atTop (𝓝 (7 * 0)))
  refine squeeze_zero' ?_ ?_ hupper
  · exact Eventually.of_forall fun R => by positivity
  · filter_upwards [eventually_ge_atTop 56] with R hR
    have hnear := norm_squareRootNearPrimeTransport_le R hR
    have hRposNat : 0 < R := by omega
    have hRpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hRposNat
    have hlogSq : 0 ≤ (Real.log (R : ℝ)) ^ 2 := sq_nonneg _
    calc
      ‖squareRootNearPrimeTransport R‖ * (Real.log (R : ℝ)) ^ 2 /
          (R : ℝ) ^ 2 ≤
        (7 * (R : ℝ)) * (Real.log (R : ℝ)) ^ 2 / (R : ℝ) ^ 2 := by
          gcongr
      _ = 7 * ((Real.log (R : ℝ)) ^ 2 / (R : ℝ)) := by
        field_simp [hRpos.ne']
        ring

end RHLean.Proof
