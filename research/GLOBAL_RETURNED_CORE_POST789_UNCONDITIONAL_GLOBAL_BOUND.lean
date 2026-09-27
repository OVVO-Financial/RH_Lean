import Mathlib
import RHLean.Analysis.NativePNTQuantitativeStatements
import RHLean.Analysis.StrongMertensLogNineBalance
import «research.GLOBAL_RETURNED_CORE_POST789_CORRELATION_EQUIVALENCE»

/-!
# Unconditional global bound for the post-#789 signed remainder

The repository already compiles the unconditional zero-free-region estimate
`strongNativeMertensSubexp`:

  |M(N)| <= C N exp(-c (log N)^(1/10)),   N >= 3.

Feeding it through the Young comparison of
`GLOBAL_RETURNED_CORE_POST789_CORRELATION_EQUIVALENCE` gives a bound on the
signed remainder that holds for every `R >= 56`, with no envelope hypothesis:

  X_R <= (1/4) E_R + 4 B(R^2 - 1)^2 + 4 B(R - 1)^2,
  B(x) = C x exp(-c (log x)^(1/10)).

This is the strongest global bound on `X_R` currently available from compiled
unconditional input.  It is not the RH consumer's bound.  The consumer needs
`X_R <= (3/2) E_R + C R^2 K`, while `B(R^2 - 1)^2` is of size
`R^4 exp(-c' (log R)^(1/10))`.  The gap is a factor
`R^2 exp(-c' (log R)^(1/10))`.  By the lower comparison
`(1/2) corr^2 - (1/2) E - 3 R^2 <= X_R`, that gap cannot be closed inside
`X_R`: closing it is an RH-strength top-endpoint Mertens estimate.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Pure algebra: a Young bound plus a triangle bound on the correlation
norm. -/
private theorem post789_global_bound_algebra
    {X E n bR bN : ℝ}
    (hY : X ≤ (1 + 1) * n ^ 2 + 1 / 4 * E)
    (hn0 : 0 ≤ n) (hn : n ≤ bR + bN) :
    X ≤ 1 / 4 * E + 4 * bN ^ 2 + 4 * bR ^ 2 := by
  nlinarith [sq_nonneg (bR - bN), mul_nonneg hn0 (sub_nonneg.mpr hn),
    sq_nonneg (bR + bN - n)]

/-- **Unconditional global bound.** For every `R >= 56` the post-#789 signed
remainder is at most a quarter of the q² energy plus the squared
zero-free-region Mertens envelopes at the two correlation endpoints. -/
theorem post789SignedRemainder_unconditional_global_bound :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
      ∀ R : ℕ, 56 ≤ R →
        lowOwnerPost789SignedCrossDiagonalRemainder R ≤
          (1 / 4 : ℝ) * canonicalRoughLowQ2DaughterEnergy R +
            4 * (C * (squareRootEndpoint R : ℝ) *
              Real.exp (-c * (Real.log (squareRootEndpoint R : ℝ)) ^
                ((1 : ℝ) / 10))) ^ 2 +
            4 * (C * ((R - 1 : ℕ) : ℝ) *
              Real.exp (-c * (Real.log ((R - 1 : ℕ) : ℝ)) ^
                ((1 : ℝ) / 10))) ^ 2 := by
  rcases strongNativeMertensSubexp with ⟨c, C, hc, hC, hM⟩
  refine ⟨c, C, hc, hC, ?_⟩
  intro R hR
  have hN : 3 ≤ squareRootEndpoint R := by
    have hsquare : 2 ^ 2 ≤ R ^ 2 :=
      Nat.pow_le_pow_left (by omega : 2 ≤ R) 2
    unfold squareRootEndpoint
    omega
  have hMN := hM (squareRootEndpoint R) hN
  have hMR := hM (R - 1) (by omega)
  rw [← norm_mertensSummatory_eq_abs_nativeMertensSummatory] at hMN
  rw [← norm_mertensSummatory_eq_abs_nativeMertensSummatory] at hMR
  have hcorr :=
    (norm_sub_le (mertensSummatory (R - 1))
      (mertensSummatory (squareRootEndpoint R))).trans (add_le_add hMR hMN)
  rw [← squareRootCanonicalRoughCorrelation_eq_mertens_pred_sub_endpoint
    R (by omega)] at hcorr
  have hY := post789SignedRemainder_le_correlationSq_young
    (R := R) (by omega) (a := 1) (b := 1 / 4) (by norm_num) (by norm_num)
  exact post789_global_bound_algebra hY (norm_nonneg _) hcorr

end RHLean.Proof
