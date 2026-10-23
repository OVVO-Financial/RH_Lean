import Mathlib

/-!
# Exact exponent budget for ORIGINAL OpenAI principal-source comparison

OAI.SevenEighths.ProbePrincipalNormalized.actual_ray_principal_comparison
(source: Detector/PrincipalNormalized.lean) gives the already PROVED
normalized principal row minus HeckeSignal.signal error:
  C*(Z^(beta-11/16-17/48000+nu)
       +Z^(beta-11/16+e-(7/8)*ellMin)).

The expected high-row target is exponent beta-11/16-sigma.

Both principal terms fit that target under the TWO actual margins
 sigma + nu <= 17/48000 and sigma + e <= 7*ellMin/8.
This is pure algebraic transport of the ORIGINAL lower-level estimate,
not an assumed new holomorphic contour at 1/2-sigma.

The principal comparison theorem has its own geometry, Schwartz support,
ray-class, positivity and zero-free-beta hypotheses; all remain in
force. The remaining nonprincipal compensated fiber bounds and
inter-fiber Gauss/Poisson moments are NOT proved by this lemma.
-/

noncomputable section

namespace RHLean.Analysis

/-- Exactly the two source-true exponent inequalities needed to
    absorb both terms of OpenAI's original principal comparison. -/
theorem oai_original_principal_rate_exponents_le
    (beta sigma nu e ellMin : ℝ)
    (hnu : sigma + nu ≤ 17 / 48000)
    (hell : sigma + e ≤ (7 / 8 : ℝ) * ellMin) :
    beta - 11 / 16 - 17 / 48000 + nu ≤
      beta - 11 / 16 - sigma ∧
    beta - 11 / 16 + e - (7 / 8 : ℝ) * ellMin ≤
      beta - 11 / 16 - sigma := by
  constructor <;> linarith

/-- The original principal-source estimate, without losing hidden
    constants or silently discarding either power: two terms give
    the explicit factor 2 in the target rate for Z>=1. -/
theorem oai_original_principal_two_term_bound_to_sigma
    (beta sigma nu e ellMin Z C : ℝ)
    (hZ : 1 ≤ Z) (hC : 0 ≤ C)
    (hnu : sigma + nu ≤ 17 / 48000)
    (hell : sigma + e ≤ (7 / 8 : ℝ) * ellMin) :
    C * (Z ^ (beta - 11 / 16 - 17 / 48000 + nu) +
         Z ^ (beta - 11 / 16 + e - (7 / 8 : ℝ) * ellMin)) ≤
      2 * C * Z ^ (beta - 11 / 16 - sigma) := by
  obtain ⟨ha, hb⟩ :=
    oai_original_principal_rate_exponents_le
      beta sigma nu e ellMin hnu hell
  have h1 := Real.rpow_le_rpow_of_exponent_le hZ ha
  have h2 := Real.rpow_le_rpow_of_exponent_le hZ hb
  calc
    _ ≤ C * (Z ^ (beta - 11 / 16 - sigma) +
          Z ^ (beta - 11 / 16 - sigma)) :=
      mul_le_mul_of_nonneg_left (add_le_add h1 h2) hC
    _ = 2 * C * Z ^ (beta - 11 / 16 - sigma) := by ring

/-- CONSUME, don't reinvent, the original analytic principal estimate.
    hOriginal is the source bound from original OAI:
    ProbePrincipalNormalized.actual_ray_principal_comparison.
    The two exponent margins are fully independently checked. -/
theorem oai_original_principal_source_error_fits_high_row
    (error : ℂ) (beta sigma nu e ellMin Z C : ℝ)
    (hZ : 1 ≤ Z) (hC : 0 ≤ C)
    (hnu : sigma + nu ≤ 17 / 48000)
    (hell : sigma + e ≤ (7 / 8 : ℝ) * ellMin)
    (hOriginal :
      ‖error‖ ≤
        C * (Z ^ (beta - 11 / 16 - 17 / 48000 + nu) +
             Z ^ (beta - 11 / 16 + e - (7 / 8 : ℝ) * ellMin))) :
    ‖error‖ ≤ 2 * C * Z ^ (beta - 11 / 16 - sigma) :=
  hOriginal.trans
    (oai_original_principal_two_term_bound_to_sigma
      beta sigma nu e ellMin Z C hZ hC hnu hell)

end RHLean.Analysis

#print axioms RHLean.Analysis.oai_original_principal_rate_exponents_le
#print axioms RHLean.Analysis.oai_original_principal_two_term_bound_to_sigma
#print axioms RHLean.Analysis.oai_original_principal_source_error_fits_high_row
