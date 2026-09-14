import Mathlib
import «research.CANONICAL_ROUGH_CORRELATION_STRONG_GLOBAL_BOUND»
import «research.LOW_OWNER_PHYSICAL_CENSUS_CORRELATION»

/-!
# Unconditional strong global bound on the exact low-owner physical census

The exact census theorem on this branch gives

  Corr_R = Census_R - Root_R,    ||Root_R|| <= 8 R.

The unconditional Strong-Mertens theorem gives a global subexponential envelope
for `Corr_R`.  Combining the two produces an explicit all-scale bound on the
complete signed physical census itself.  No q^2 energy hypothesis, lower-envelope
hypothesis, or RH-strength estimate is used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

/-- **Global amplitude bound for the complete physical census.** -/
theorem lowOwnerPhysicalFarCensus_strongSubexp_global :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
      ∀ R : ℕ, 56 ≤ R →
        ‖lowOwnerPhysicalFarCensus R‖ ≤
          canonicalRoughCorrelationStrongEnvelope c C R + 8 * (R : ℝ) := by
  rcases squareRootCanonicalRoughCorrelation_strongSubexp_global with
    ⟨c, C, hc, hC, hcorr⟩
  refine ⟨c, C, hc, hC, ?_⟩
  intro R hR
  have hrepr :=
    squareRootCanonicalRoughCorrelation_eq_physicalFarCensus_sub_root R hR
  have hroot := norm_frozenTopFarRoughRootCorrection_le_eight_root R hR
  have hcorrBound := hcorr R (by omega)
  have hsum :
      lowOwnerPhysicalFarCensus R =
        squareRootCanonicalRoughCorrelation R +
          frozenTopFarRoughRootCorrection R := by
    linear_combination -hrepr
  rw [hsum]
  calc
    ‖squareRootCanonicalRoughCorrelation R +
        frozenTopFarRoughRootCorrection R‖ ≤
      ‖squareRootCanonicalRoughCorrelation R‖ +
        ‖frozenTopFarRoughRootCorrection R‖ := norm_add_le _ _
    _ ≤ canonicalRoughCorrelationStrongEnvelope c C R + 8 * (R : ℝ) :=
      add_le_add hcorrBound hroot

/-- Energy form, retaining the exact cancellation up to the already-proved
root correction.  The factor two is only the universal two-vector inequality. -/
theorem lowOwnerPhysicalFarCensus_energy_strongSubexp_global :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
      ∀ R : ℕ, 56 ≤ R →
        ‖lowOwnerPhysicalFarCensus R‖ ^ 2 ≤
          2 * (canonicalRoughCorrelationStrongEnvelope c C R) ^ 2 +
            128 * (R : ℝ) ^ 2 := by
  rcases squareRootCanonicalRoughCorrelation_strongSubexp_global with
    ⟨c, C, hc, hC, hcorr⟩
  refine ⟨c, C, hc, hC, ?_⟩
  intro R hR
  have hrepr :=
    squareRootCanonicalRoughCorrelation_eq_physicalFarCensus_sub_root R hR
  have hroot := norm_frozenTopFarRoughRootCorrection_le_eight_root R hR
  have hcorrBound := hcorr R (by omega)
  have hsum :
      lowOwnerPhysicalFarCensus R =
        squareRootCanonicalRoughCorrelation R +
          frozenTopFarRoughRootCorrection R := by
    linear_combination -hrepr
  rw [hsum]
  have htri :
      ‖squareRootCanonicalRoughCorrelation R +
          frozenTopFarRoughRootCorrection R‖ ≤
        ‖squareRootCanonicalRoughCorrelation R‖ +
          ‖frozenTopFarRoughRootCorrection R‖ := norm_add_le _ _
  have hnon :
      0 ≤ canonicalRoughCorrelationStrongEnvelope c C R := by
    unfold canonicalRoughCorrelationStrongEnvelope
    positivity
  have hroot0 : 0 ≤ 8 * (R : ℝ) := by positivity
  have hsumBound :
      ‖squareRootCanonicalRoughCorrelation R +
          frozenTopFarRoughRootCorrection R‖ ≤
        canonicalRoughCorrelationStrongEnvelope c C R + 8 * (R : ℝ) :=
    htri.trans (add_le_add hcorrBound hroot)
  have hsquare :
      ‖squareRootCanonicalRoughCorrelation R +
          frozenTopFarRoughRootCorrection R‖ ^ 2 ≤
        (canonicalRoughCorrelationStrongEnvelope c C R + 8 * (R : ℝ)) ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _) (add_nonneg hnon hroot0)).2 hsumBound
  calc
    ‖squareRootCanonicalRoughCorrelation R +
        frozenTopFarRoughRootCorrection R‖ ^ 2 ≤
      (canonicalRoughCorrelationStrongEnvelope c C R + 8 * (R : ℝ)) ^ 2 := hsquare
    _ ≤ 2 * (canonicalRoughCorrelationStrongEnvelope c C R) ^ 2 +
          128 * (R : ℝ) ^ 2 := by
      nlinarith [sq_nonneg
        (canonicalRoughCorrelationStrongEnvelope c C R - 8 * (R : ℝ))]

end RHLean.Proof
