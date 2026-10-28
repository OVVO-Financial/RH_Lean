import «research.OAI78_CORR4_OWNER_TAIL_PAID_20261028»
import «research.VF_919_OPENAI_434_UNCONDITIONAL_SQUARE_BLOCK_COVARIANCE_20261019»

/-!
# Actual OpenAI certified 7/8 -> original CORR-4 q² large-owner payment

This file belongs to the PINNED upstream-OAI Lean compilation lane.
The ordinary native research job does not import OpenAI's final detector.

Source input: the *unconditional certified OpenAI* global Mertens
covariance at every actual integer. The output is a genuine
q >= T² power-saving estimate, not a new global 7/8 improvement.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof
open RHLean.Analysis RHLean.Analysis.MertensExponent

/-- The imported unconditional OpenAI 7/8 theorem pays the literal
    reciprocal high-owner column uniformly at every root and every T.
    For T ~ R^c this saves a positive power of R with no PNT. -/
theorem openai434_paid_original_corr4_large_owner
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R T : ℕ, 56 ≤ R →
      (T : ℝ) * |oai78PaidLargeQReciprocal R T| ≤
        (1 / 4 : ℝ) * C *
          Real.rpow (R : ℝ) (7 / 4 + 2 * ε) := by
  have hseven : MertensGrowthAtMost ((7 : ℝ) / 8) :=
    vf919_sevenEighthsSignedCovariance_iff_mertensGrowth.mp
      openai434_actual_global_signed_covariance
  obtain ⟨C, hC, hM⟩ := hseven ε hε
  refine ⟨C, hC, ?_⟩
  intro R T hR
  have hβ : (3 / 4 : ℝ) ≤ 7 / 8 + ε := by linarith
  have hpaid := oai78Paid_large_owner_column_le_power
    R T hR (7 / 8 + ε) C hβ hC hM
  convert hpaid using 1
  congr 1
  ring

#print axioms openai434_paid_original_corr4_large_owner

end RHLean.Proof
