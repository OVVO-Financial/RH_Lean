import «research.UNIVERSAL_ENVELOPE_LAWS»
import «research.UNIVERSAL_ENVELOPE_ZERO_LOG»
import «research.SQUARE_ENDPOINT_STEP_POLYLOG_STRENGTH»

/-!
# The squared historical-envelope dictionary and the finite-constant target

The square-root-history shape is often displayed as a squared numerator.
This file fixes that conversion, including the factor of two in every
epsilon loss.  A root exponent `p` corresponds exactly to zero boundary
`(p-1)/2`, for `p >= 2`.

The original finite amplification premise implies the critical squared
envelope.  It also retains its stronger, epsilon-free double-exponential
history iteration.  No converse from RH to finite amplification is asserted.
-/

noncomputable section

namespace RHLean.Analysis.UniversalEnvelope

open RHLean.Proof RHLean.Analysis.MertensExponent

/-- The literal squared numerator over the original strict history. -/
def SquaredEnvelopeBound (p : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℕ, 2 ≤ R →
    ‖mertensSummatory (squareRootEndpoint R) - 1‖ ^ 2 ≤
      C * (R : ℝ) ^ (p + ε) * squareRootHistoricalK R

/-- Squaring preserves the quantifiers after halving the positive loss. -/
theorem squaredEnvelope_iff_envelope (p : ℝ) :
    SquaredEnvelopeBound p ↔ EnvelopeBound 1 ((p - 2) / 2) := by
  constructor
  · intro h ε hε
    obtain ⟨C, hC, hbound⟩ := h (2 * ε) (by linarith)
    refine ⟨Real.sqrt C, Real.sqrt_nonneg C, ?_⟩
    intro R hR
    have hR0 : (0 : ℝ) < (R : ℝ) := by exact_mod_cast (show 0 < R by omega)
    have hK0 := squareRootHistoricalK_nonneg R
    have hp : ((R : ℝ) ^ (1 + (p - 2) / 2 + ε)) ^ (2 : ℕ) =
        (R : ℝ) ^ (p + 2 * ε) := by
      rw [← Real.rpow_mul_natCast hR0.le]
      congr 1
      ring
    have hs : (Real.sqrt C * (R : ℝ) ^ (1 + (p - 2) / 2 + ε) *
        Real.sqrt (squareRootHistoricalK R)) ^ 2 =
        C * (R : ℝ) ^ (p + 2 * ε) * squareRootHistoricalK R := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hC, Real.sq_sqrt hK0, hp]
    have hle : ‖mertensSummatory (squareRootEndpoint R) - 1‖ ≤
        Real.sqrt C * (R : ℝ) ^ (1 + (p - 2) / 2 + ε) * Real.sqrt (squareRootHistoricalK R) := by
      apply (sq_le_sq₀ (norm_nonneg _)
        (show 0 ≤ Real.sqrt C * (R : ℝ) ^ (1 + (p - 2) / 2 + ε) *
          Real.sqrt (squareRootHistoricalK R) by positivity)).mp
      rw [hs]
      exact hbound R hR
    simpa only [Real.sqrt_eq_rpow] using hle
  · intro h ε hε
    obtain ⟨C, hC, hbound⟩ := h (ε / 2) (by linarith)
    refine ⟨C ^ 2, sq_nonneg C, ?_⟩
    intro R hR
    have hR0 : (0 : ℝ) < (R : ℝ) := by exact_mod_cast (show 0 < R by omega)
    have hcenter : ‖mertensSummatory (squareRootEndpoint R) - 1‖ ≤
        C * (R : ℝ) ^ (1 + (p - 2) / 2 + ε / 2) * Real.sqrt (squareRootHistoricalK R) := by
      simpa only [Real.sqrt_eq_rpow] using hbound R hR
    have hs := (sq_le_sq₀ (norm_nonneg _)
      (show 0 ≤ C * (R : ℝ) ^ (1 + (p - 2) / 2 + ε / 2) *
        Real.sqrt (squareRootHistoricalK R) by positivity)).mpr hcenter
    have hp : ((R : ℝ) ^ (1 + (p - 2) / 2 + ε / 2)) ^ (2 : ℕ) =
        (R : ℝ) ^ (p + ε) := by
      rw [← Real.rpow_mul_natCast hR0.le]
      congr 1
      ring
    simpa only [mul_pow, Real.sq_sqrt (squareRootHistoricalK_nonneg R), hp] using hs

/-- The root-exponent gate in the original squared coordinates. -/
theorem squaredEnvelope_iff_rightmost_le {p : ℝ} (hp : 2 ≤ p) :
    SquaredEnvelopeBound p ↔ zetaRightmostRealPart ≤ (p - 1) / 2 := by
  have hboundary : (1 / 2 : ℝ) + ((p - 2) / 2) / (2 - 1) = (p - 1) / 2 := by
    ring
  rw [squaredEnvelope_iff_envelope p,
    envelopeBound_iff_rightmost_le (by norm_num : (0 : ℝ) ≤ 1)
      (by norm_num : (1 : ℝ) < 2) (by linarith : 0 ≤ (p - 2) / 2),
    hboundary]

/-- The squared critical envelope is exactly the zero-logarithmic statement. -/
theorem squaredEnvelope_two_iff_zeroLog :
    SquaredEnvelopeBound 2 ↔ SquareRootAmplificationZeroLogGrowthStatement := by
  have h : SquaredEnvelopeBound 2 ↔ MertensGrowthAtMost (1 / 2 : ℝ) := by
    rw [squaredEnvelope_iff_rightmost_le (by norm_num : (2 : ℝ) ≤ 2)]
    norm_num
    exact (growthAtMost_iff_rightmost_le (by norm_num : (0 : ℝ) ≤ 1 / 2)).symm
  exact h.trans zeroLog_iff_mertens_half.symm

/-- A finite amplification constant is a valid critical envelope for every
positive loss.  It is not identified with that weaker quantifier pattern. -/
theorem squaredEnvelope_two_of_finiteAmplification
    (hfinite : SquareRootMertensEndpointAmplificationStatement) :
    SquaredEnvelopeBound 2 := by
  obtain ⟨A, hA, hbound⟩ := hfinite
  intro ε hε
  refine ⟨A, hA, ?_⟩
  intro R hR
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast (show 1 ≤ R by omega)
  have hR0 : (0 : ℝ) < (R : ℝ) := by linarith
  have hnative := hbound R (squareRootHistoricalK R) hR (squareRootHistoricalK_envelope R)
  rw [← shiftedMertensEnergy_eq_intSquare, shiftedMertensEnergy] at hnative
  have hp : (R : ℝ) ^ (2 : ℕ) ≤ (R : ℝ) ^ (2 + ε) := by
    rw [← Real.rpow_natCast (R : ℝ) 2]
    apply Real.rpow_le_rpow_of_exponent_le hR1
    norm_num
    linarith
  exact hnative.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp hA) (squareRootHistoricalK_nonneg R))

/-- The epsilon-free amplification target implies the critical-zero claim. -/
theorem criticalZeros_of_finiteAmplification
    (hfinite : SquareRootMertensEndpointAmplificationStatement) :
    ∀ ρ : ℂ, NontrivialZetaZero ρ → ρ.re = (1 / 2 : ℝ) :=
  zeroLog_iff_criticalZeros.mp
    (squaredEnvelope_two_iff_zeroLog.mp (squaredEnvelope_two_of_finiteAmplification hfinite))

/-- Preserve the stronger finite-constant iteration in an exact discrete
form: one fixed multiplier for every double-exponential historical scale. -/
theorem historical_double_exponential_of_finiteAmplification
    (hfinite : SquareRootMertensEndpointAmplificationStatement) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ j : ℕ,
      squareRootHistoricalK (2 ^ 2 ^ j) ≤ B ^ j := by
  obtain ⟨B, hB, hhistory⟩ := lowerMertensCriticalEnvelope_doubleExponential_of_amplification hfinite
  refine ⟨B, hB, fun j => ?_⟩
  exact (squareRootHistoricalK_le_iff _ _).mpr (hhistory j)

end RHLean.Analysis.UniversalEnvelope

end
