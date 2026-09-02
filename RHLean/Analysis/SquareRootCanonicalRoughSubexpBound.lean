import Mathlib
import RHLean.Analysis.SquareRootCanonicalRoughCovariance

/-!
# Strict subquartic bound on the canonical rough covariance seam

The endpoint-only reduction identifies the remaining canonical rough covariance
expression with the post-crossing coupled tail at `X_R = R^2 - 1`.  The
repository already proves an unconditional strong-Mertens subexponential norm
bound for that tail.  This file records the corresponding **energy** estimate
directly on the exact mean-plus-covariance seam.

This is a genuine quantitative reduction from the crude quartic support
envelope: instead of `O(R^4)`, the exact seam is bounded by

```text
(C * X_R * exp (-c * (log X_R)^(1/10)) + K_0)^2.
```

No mean/covariance split and no extra triangle inequality is introduced here;
the only squaring is applied after the already-coupled tail estimate.
-/

noncomputable section

open Filter
open scoped ArithmeticFunction.Moebius BigOperators Topology

namespace RHLean.Proof

open RHLean.Analysis

/-- The strongest currently compiled premise-free energy envelope on the exact
canonical mean-plus-covariance seam.  Compared with the raw `R^4` support
bound, it carries a subexponential saving at every sufficiently large square
endpoint. -/
def SquareRootCanonicalRoughCovarianceSubexpEnergyStatement (K₀ : ℕ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
    ∀ R K j : ℕ,
      3 ≤ R →
      K ≤ K₀ →
      SquareRootPacketCrossesAt R K →
      j ≤ squareRootReciprocalPrimeLayerCard R K →
      0 ≤ squareRootCrossingLayerPartialPacketInt R K j →
      squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ) →
      ‖squareRootPostCrossingCanonicalBaseline R K j -
          (squareRootCanonicalRoughCofactorCard R : ℂ) *
            (squareRootCanonicalRoughParityMean R *
                squareRootCanonicalRoughResponseMean R +
              squareRootCanonicalRoughCovariance R)‖ ^ 2 ≤
        (C * (squareRootEndpoint R : ℝ) *
            Real.exp
              (-c *
                (Real.log (squareRootEndpoint R : ℝ)) ^ ((1 : ℝ) / 10)) +
          (K₀ : ℝ)) ^ 2

/-- **Strictly reduced covariance-seam bound.**  The strong-Mertens tail
estimate, kept in its coupled signed form, gives the same subexponential
saving directly on the canonical rough covariance energy. -/
theorem squareRootCanonicalRoughCovarianceSubexpEnergy
    (K₀ : ℕ) :
    SquareRootCanonicalRoughCovarianceSubexpEnergyStatement K₀ := by
  rcases postCrossingCoupledTailSubexp K₀ with ⟨c, C, hc, hC, htail⟩
  refine ⟨c, C, hc, hC, ?_⟩
  intro R K j hR hK hcross hj hV0 hVK
  have hKR : K < R := by
    rcases squareRootPacketCrossing_has_postRootPrime hcross with
      ⟨q, _hqPrime, hRq, _hqX, hqK⟩
    rw [← hqK]
    exact squareRootEndpoint_div_lt_root_of_root_le (by omega) (by omega)
  have hnorm := htail R K j hR hK hcross hj hV0 hVK
  rw [squareRootPostCrossingCoupledTail_eq_baseline_sub_mean_covariance
    R K j hR hcross.1 hKR] at hnorm
  exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2

end RHLean.Proof
