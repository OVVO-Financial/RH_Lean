import «research.OAI_SEVEN_EIGHTHS_WEIGHTED_COVARIANCE»
import RHLean.Proof.SquareRootLegalAncestryGramReduction

/-!
# Exact normalized root/smooth anti-alignment, separate from the raw pair sum

The root/smooth scalar in the original square-root ancestry source is NOT
Pearson correlation, and is NOT the global physical unweighted Green--Kubo
pair covariance. It is a two-population signed Gram ratio.

The empirical R=5561 value near -1 is NOT a uniform arithmetic theorem.
We formalize its exact identity and its universal [-1,1] normalization,
provided the diagonal is positive. The published 7/8 zero-free bound controls
the SQUARED RESIDUAL, but alone provides no lower bound on the Gram diagonal
and therefore no claim that the normalized ratio approaches -1.
-/

noncomputable section

namespace RHLean.Analysis.OAISevenEighthsRootSmooth

open RHLean.Proof

/-- Signed root/smooth normalized cross-Gram. It is not Pearson correlation. -/
def normalizedCrossGram (R : ℕ) : ℝ :=
  (2 * squareRootPrimeSmoothOffDiagonalGram R) /
    squareRootPrimeSmoothDiagonalGram R

/-- The general two-real-number cancellation normalization lies in [-1,1]. -/
theorem normalized_pair_bounds (u v : ℝ)
    (hD : 0 < u ^ 2 + v ^ 2) :
    -(1 : ℝ) ≤ (2 * u * v) / (u ^ 2 + v ^ 2) ∧
      (2 * u * v) / (u ^ 2 + v ^ 2) ≤ 1 := by
  constructor
  · apply (le_div_iff₀ hD).2
    nlinarith [sq_nonneg (u + v)]
  · apply (div_le_iff₀ hD).2
    nlinarith [sq_nonneg (u - v)]

/-- The exact residual fraction, no independence hypothesis. -/
theorem one_add_normalized_pair_eq_residual_div (u v : ℝ)
    (hD : 0 < u ^ 2 + v ^ 2) :
    1 + (2 * u * v) / (u ^ 2 + v ^ 2) =
      (u + v) ^ 2 / (u ^ 2 + v ^ 2) := by
  have hne : u ^ 2 + v ^ 2 ≠ 0 := ne_of_gt hD
  field_simp [hne]
  ring

/-- Exact source-specific [-1,1] bounds: the input is the entire two-population
signed scalar, not per-prime correlations or a normalized random process. -/
theorem normalizedCrossGram_bounds (R : ℕ)
    (hD : 0 < squareRootPrimeSmoothDiagonalGram R) :
    -(1 : ℝ) ≤ normalizedCrossGram R ∧ normalizedCrossGram R ≤ 1 := by
  simpa [normalizedCrossGram, squareRootPrimeSmoothOffDiagonalGram,
    squareRootPrimeSmoothDiagonalGram, mul_assoc] using
      normalized_pair_bounds (squareRootPrimeRootReal R)
        (squareRootSmoothMassReal R) hD

/-- The distance from -1 is EXACTLY the squared root/smooth residual divided
by the physical diagonal Gram. -/
theorem one_add_normalizedCrossGram_eq_residual_div (R : ℕ)
    (hD : 0 < squareRootPrimeSmoothDiagonalGram R) :
    1 + normalizedCrossGram R =
      (squareRootPrimeRootReal R + squareRootSmoothMassReal R) ^ 2 /
        squareRootPrimeSmoothDiagonalGram R := by
  simpa [normalizedCrossGram, squareRootPrimeSmoothOffDiagonalGram,
    squareRootPrimeSmoothDiagonalGram, mul_assoc] using
      one_add_normalized_pair_eq_residual_div
        (squareRootPrimeRootReal R) (squareRootSmoothMassReal R) hD

/-- Native Mertens source reconstruction: the residual in the correlation
denominator is M(R^2-1)-1, not M(R^2-1), with no omitted shift. -/
theorem one_add_normalizedCrossGram_eq_mertens_residual (R : ℕ)
    (hR : 2 ≤ R) (hD : 0 < squareRootPrimeSmoothDiagonalGram R) :
    1 + normalizedCrossGram R =
      ((((mertensSummatoryInt (squareRootEndpoint R) - 1 : ℤ) : ℝ)) ^ 2) /
        squareRootPrimeSmoothDiagonalGram R := by
  rw [one_add_normalizedCrossGram_eq_residual_div R hD,
    squareRootPrimeSmoothState_eq_mertensInt_sub_one R hR]

/-- Root/smooth cancellation of 99.9798% at a finite endpoint can be checked
numerically, but only the equality above is uniform in R. This exact
unsquared-to-squared statement has no positivity assumption on the diagonal. -/
theorem rootSmoothCrossGram_eq_shiftedMertensSq (R : ℕ) (hR : 2 ≤ R) :
    squareRootPrimeSmoothCrossRegionGram R =
      ‖RHLean.Analysis.mertensSummatory (squareRootEndpoint R) - 1‖ ^ 2 := by
  rw [squareRootPrimeSmoothCrossRegionGram_eq_shiftedSquarePrefixMertens_norm_sq
    R hR]
  unfold RHLean.Analysis.squarePrefixMertens
  rw [squarePrefixEndpoint_pred_eq_squareRootEndpoint R (by omega)]

end RHLean.Analysis.OAISevenEighthsRootSmooth

#print axioms RHLean.Analysis.OAISevenEighthsRootSmooth.normalized_pair_bounds
#print axioms RHLean.Analysis.OAISevenEighthsRootSmooth.one_add_normalized_pair_eq_residual_div
#print axioms RHLean.Analysis.OAISevenEighthsRootSmooth.normalizedCrossGram_bounds
#print axioms RHLean.Analysis.OAISevenEighthsRootSmooth.one_add_normalizedCrossGram_eq_mertens_residual
#print axioms RHLean.Analysis.OAISevenEighthsRootSmooth.rootSmoothCrossGram_eq_shiftedMertensSq
