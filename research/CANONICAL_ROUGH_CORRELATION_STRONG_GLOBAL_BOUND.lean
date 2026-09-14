import Mathlib
import «research.CANONICAL_ROUGH_GLOBAL_BOUNDS»
import RHLean.Analysis.StrongMertensLogNineBalance
import RHLean.Analysis.NativePNTQuantitativeStatements

/-!
# Unconditional strong global bound for the canonical rough correlation

The canonical rough correlation is exactly the Mertens interval

  Corr_R = M(R-1) - M(R^2-1).

The repository already proves the unconditional global Strong-Mertens estimate

  |M(N)| <= C N exp(-c (log N)^(1/10))

for every natural endpoint `N >= 3`, with fixed constants `c>0`, `C>=0`.
Applying it to the two exact endpoints gives a genuine all-scale quantitative
bound on `Corr_R`; no sampled-range qualification, q^2 hypothesis, lower
envelope, or RH-strength premise is used.
-/

noncomputable section

open Filter
open scoped ArithmeticFunction.Moebius BigOperators Topology

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

/-- The exact Strong-Mertens envelope inherited by the two endpoints of the
canonical rough correlation. -/
def canonicalRoughCorrelationStrongEnvelope (c C : ℝ) (R : ℕ) : ℝ :=
  C *
    ((((R - 1 : ℕ) : ℝ) *
        Real.exp (-c * strongMertensScale (((R - 1 : ℕ) : ℝ)))) +
      ((squareRootEndpoint R : ℝ) *
        Real.exp (-c * strongMertensScale (squareRootEndpoint R : ℝ))))

/-- **Unconditional global correlation bound.**  There are fixed constants
`c>0`, `C>=0` such that every `R>=4` satisfies the literal two-endpoint
Strong-Mertens estimate. -/
theorem squareRootCanonicalRoughCorrelation_strongSubexp_global :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
      ∀ R : ℕ, 4 ≤ R →
        ‖squareRootCanonicalRoughCorrelation R‖ ≤
          canonicalRoughCorrelationStrongEnvelope c C R := by
  rcases strongNativeMertensSubexp with ⟨c, C, hc, hC, hM⟩
  refine ⟨c, C, hc, hC, ?_⟩
  intro R hR
  have hpred : 3 ≤ R - 1 := by omega
  have hsq : 16 ≤ R ^ 2 := by nlinarith
  have hend : 3 ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    omega
  have hp :
      ‖mertensSummatory (R - 1)‖ ≤
        C * (((R - 1 : ℕ) : ℝ) *
          Real.exp (-c * strongMertensScale (((R - 1 : ℕ) : ℝ)))) := by
    rw [norm_mertensSummatory_eq_abs_nativeMertensSummatory]
    simpa [strongMertensScale, mul_assoc] using hM (R - 1) hpred
  have hx :
      ‖mertensSummatory (squareRootEndpoint R)‖ ≤
        C * ((squareRootEndpoint R : ℝ) *
          Real.exp (-c * strongMertensScale (squareRootEndpoint R : ℝ))) := by
    rw [norm_mertensSummatory_eq_abs_nativeMertensSummatory]
    simpa [strongMertensScale, mul_assoc] using hM (squareRootEndpoint R) hend
  rw [squareRootCanonicalRoughCorrelation_eq_mertens_pred_sub_endpoint R (by omega)]
  unfold canonicalRoughCorrelationStrongEnvelope
  calc
    ‖mertensSummatory (R - 1) - mertensSummatory (squareRootEndpoint R)‖ ≤
        ‖mertensSummatory (R - 1)‖ +
          ‖mertensSummatory (squareRootEndpoint R)‖ := norm_sub_le _ _
    _ ≤
        C * (((R - 1 : ℕ) : ℝ) *
          Real.exp (-c * strongMertensScale (((R - 1 : ℕ) : ℝ)))) +
        C * ((squareRootEndpoint R : ℝ) *
          Real.exp (-c * strongMertensScale (squareRootEndpoint R : ℝ))) :=
      add_le_add hp hx
    _ = C *
        ((((R - 1 : ℕ) : ℝ) *
            Real.exp (-c * strongMertensScale (((R - 1 : ℕ) : ℝ)))) +
          ((squareRootEndpoint R : ℝ) *
            Real.exp (-c * strongMertensScale (squareRootEndpoint R : ℝ)))) := by
      ring

/-- Energy form of the same unconditional all-scale estimate. -/
theorem squareRootCanonicalRoughCorrelation_energy_strongSubexp_global :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
      ∀ R : ℕ, 4 ≤ R →
        ‖squareRootCanonicalRoughCorrelation R‖ ^ 2 ≤
          (canonicalRoughCorrelationStrongEnvelope c C R) ^ 2 := by
  rcases squareRootCanonicalRoughCorrelation_strongSubexp_global with
    ⟨c, C, hc, hC, hbound⟩
  refine ⟨c, C, hc, hC, ?_⟩
  intro R hR
  have h := hbound R hR
  have hleft : 0 ≤ ‖squareRootCanonicalRoughCorrelation R‖ := norm_nonneg _
  have hright : 0 ≤ canonicalRoughCorrelationStrongEnvelope c C R := by
    unfold canonicalRoughCorrelationStrongEnvelope
    positivity
  exact (sq_le_sq₀ hleft hright).2 h

end RHLean.Proof
