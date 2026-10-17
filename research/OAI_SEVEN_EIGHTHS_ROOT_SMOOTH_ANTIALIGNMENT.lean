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

/-- The normalized surplus, multiplied by its ACTUAL diagonal, is exactly
the complete signed root/smooth Gram. This preserves every cross-channel term. -/
theorem normalized_surplus_mul_diagonal_eq_crossGram (R : ℕ)
    (hD : 0 < squareRootPrimeSmoothDiagonalGram R) :
    (1 + normalizedCrossGram R) * squareRootPrimeSmoothDiagonalGram R =
      squareRootPrimeSmoothCrossRegionGram R := by
  rw [one_add_normalizedCrossGram_eq_residual_div R hD,
    squareRootPrimeSmoothCrossRegionGram_eq_residual_sq]
  field_simp [hD.ne']

/-- OAI 7/8 supplies the SQUARED shifted Mertens numerator at a real
power exponent 7/4+η in the physical integer endpoint x=R^2-1. It does
not supply a comparable lower bound for the independent denominator. -/
theorem rootSmoothCrossGram_upper_of_sevenEighths
    (hZF : RHLean.Analysis.OAISevenEighthsCovariance.SevenEighthsZeroFree)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℕ, 2 ≤ R →
      squareRootPrimeSmoothCrossRegionGram R ≤
        C * Real.rpow
          (((squareRootEndpoint R + 1 : ℕ) : ℝ)) ((7 : ℝ) / 4 + η) := by
  have hδ : 0 < η / 2 := by linarith
  obtain ⟨K, hK, hBound⟩ :
      RHLean.Analysis.MertensExponent.MertensPowerBound
        ((7 : ℝ) / 8 + η / 2) :=
    (RHLean.Analysis.OAISevenEighthsCovariance.growthAtMost_sevenEighths_of_zeroFree
      hZF) (η / 2) hδ
  let C : ℝ := 2 * K ^ 2 + 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro R hR
  have h4 : 4 ≤ R ^ 2 := by
    simpa [pow_two] using (Nat.mul_le_mul hR hR)
  have hx : 1 ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    omega
  let x : ℕ := squareRootEndpoint R
  have hbase : 0 < (((x + 1 : ℕ) : ℝ)) := by positivity
  have hbaseOne : (1 : ℝ) ≤ (((x + 1 : ℕ) : ℝ)) := by
    exact_mod_cast (by omega : 1 ≤ x + 1)
  have hxa : (x : ℝ) ≤ (((x + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.le_succ x
  have ha : 0 ≤ (7 : ℝ) / 8 + η / 2 := by linarith
  have hpowMono :
      Real.rpow (x : ℝ) ((7 : ℝ) / 8 + η / 2) ≤
        Real.rpow (((x + 1 : ℕ) : ℝ)) ((7 : ℝ) / 8 + η / 2) :=
    Real.rpow_le_rpow (by positivity) hxa ha
  have hM :
      ‖RHLean.Analysis.mertensSummatory x‖ ≤
        K * Real.rpow (((x + 1 : ℕ) : ℝ)) ((7 : ℝ) / 8 + η / 2) :=
    (hBound x hx).trans (mul_le_mul_of_nonneg_left hpowMono hK)
  have htri :
      ‖RHLean.Analysis.mertensSummatory x - (1 : ℂ)‖ ≤
        ‖RHLean.Analysis.mertensSummatory x‖ + 1 := by
    simpa using
      (norm_sub_le (RHLean.Analysis.mertensSummatory x) (1 : ℂ))
  have hshift :
      ‖RHLean.Analysis.mertensSummatory x - (1 : ℂ)‖ ≤
        K * Real.rpow (((x + 1 : ℕ) : ℝ)) ((7 : ℝ) / 8 + η / 2) + 1 :=
    htri.trans (add_le_add_right hM 1)
  have hpowNonneg :
      0 ≤ Real.rpow (((x + 1 : ℕ) : ℝ)) ((7 : ℝ) / 8 + η / 2) :=
    Real.rpow_nonneg hbase.le _
  have hpos :
      0 ≤ K * Real.rpow (((x + 1 : ℕ) : ℝ)) ((7 : ℝ) / 8 + η / 2) + 1 :=
    add_nonneg (mul_nonneg hK hpowNonneg) zero_le_one
  have hsq :
      ‖RHLean.Analysis.mertensSummatory x - (1 : ℂ)‖ ^ 2 ≤
        (K * Real.rpow (((x + 1 : ℕ) : ℝ))
          ((7 : ℝ) / 8 + η / 2) + 1) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hpos).2 hshift
  have htwosq :
      (K * Real.rpow (((x + 1 : ℕ) : ℝ))
          ((7 : ℝ) / 8 + η / 2) + 1) ^ 2 ≤
        2 * (K * Real.rpow (((x + 1 : ℕ) : ℝ))
          ((7 : ℝ) / 8 + η / 2)) ^ 2 + 2 := by
    nlinarith [sq_nonneg
      (K * Real.rpow (((x + 1 : ℕ) : ℝ))
        ((7 : ℝ) / 8 + η / 2) - 1)]
  have hadd :
      Real.rpow (((x + 1 : ℕ) : ℝ))
          (((7 : ℝ) / 8 + η / 2) + ((7 : ℝ) / 8 + η / 2)) =
        Real.rpow (((x + 1 : ℕ) : ℝ)) ((7 : ℝ) / 8 + η / 2) *
          Real.rpow (((x + 1 : ℕ) : ℝ)) ((7 : ℝ) / 8 + η / 2) :=
    Real.rpow_add hbase _ _
  have hpow :
      (Real.rpow (((x + 1 : ℕ) : ℝ)) ((7 : ℝ) / 8 + η / 2)) ^ 2 =
        Real.rpow (((x + 1 : ℕ) : ℝ)) ((7 : ℝ) / 4 + η) := by
    calc
      (Real.rpow (((x + 1 : ℕ) : ℝ)) ((7 : ℝ) / 8 + η / 2)) ^ 2 =
          Real.rpow (((x + 1 : ℕ) : ℝ)) ((7 : ℝ) / 8 + η / 2) *
            Real.rpow (((x + 1 : ℕ) : ℝ)) ((7 : ℝ) / 8 + η / 2) := by ring
      _ = Real.rpow (((x + 1 : ℕ) : ℝ))
          (((7 : ℝ) / 8 + η / 2) + ((7 : ℝ) / 8 + η / 2)) := hadd.symm
      _ = Real.rpow (((x + 1 : ℕ) : ℝ)) ((7 : ℝ) / 4 + η) := by
        congr 1
        ring
  have hlarge :
      1 ≤ Real.rpow (((x + 1 : ℕ) : ℝ)) ((7 : ℝ) / 4 + η) :=
    Real.one_le_rpow hbaseOne (by linarith)
  have hident :
      squareRootPrimeSmoothCrossRegionGram R =
        ‖RHLean.Analysis.mertensSummatory x - 1‖ ^ 2 := by
    simpa [x] using rootSmoothCrossGram_eq_shiftedMertensSq R hR
  rw [hident]
  calc
    ‖RHLean.Analysis.mertensSummatory x - 1‖ ^ 2 ≤
        (K * Real.rpow (((x + 1 : ℕ) : ℝ))
          ((7 : ℝ) / 8 + η / 2) + 1) ^ 2 := hsq
    _ ≤ 2 * (K * Real.rpow (((x + 1 : ℕ) : ℝ))
        ((7 : ℝ) / 8 + η / 2)) ^ 2 + 2 := htwosq
    _ = 2 * K ^ 2 *
          Real.rpow (((x + 1 : ℕ) : ℝ)) ((7 : ℝ) / 4 + η) + 2 := by
      rw [mul_pow, hpow]
      ring
    _ ≤ C * Real.rpow (((x + 1 : ℕ) : ℝ)) ((7 : ℝ) / 4 + η) := by
      dsimp [C]
      have htwo :
          (2 : ℝ) ≤ 2 * Real.rpow
            (((x + 1 : ℕ) : ℝ)) ((7 : ℝ) / 4 + η) := by
        linarith [hlarge]
      calc
        2 * K ^ 2 * Real.rpow
              (((x + 1 : ℕ) : ℝ)) ((7 : ℝ) / 4 + η) + 2 ≤
            2 * K ^ 2 * Real.rpow
              (((x + 1 : ℕ) : ℝ)) ((7 : ℝ) / 4 + η) +
              2 * Real.rpow
                (((x + 1 : ℕ) : ℝ)) ((7 : ℝ) / 4 + η) :=
          add_le_add_left htwo _
        _ = (2 * K ^ 2 + 2) *
            Real.rpow (((x + 1 : ℕ) : ℝ)) ((7 : ℝ) / 4 + η) := by ring

/-- Precise OAI conclusion for the normalized correlation: OAI pays the
SQUARED residual times the diagonal, not the normalized surplus itself.
No near-minus-one limit follows without a new diagonal lower bound. -/
theorem normalized_surplus_bound_of_sevenEighths
    (hZF : RHLean.Analysis.OAISevenEighthsCovariance.SevenEighthsZeroFree)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℕ, 2 ≤ R →
      0 < squareRootPrimeSmoothDiagonalGram R →
      (1 + normalizedCrossGram R) * squareRootPrimeSmoothDiagonalGram R ≤
        C * Real.rpow
          (((squareRootEndpoint R + 1 : ℕ) : ℝ)) ((7 : ℝ) / 4 + η) := by
  obtain ⟨C, hC, hbound⟩ :=
    rootSmoothCrossGram_upper_of_sevenEighths hZF hη
  refine ⟨C, hC, ?_⟩
  intro R hR hD
  rw [normalized_surplus_mul_diagonal_eq_crossGram R hD]
  exact hbound R hR

end RHLean.Analysis.OAISevenEighthsRootSmooth

#print axioms RHLean.Analysis.OAISevenEighthsRootSmooth.normalized_pair_bounds
#print axioms RHLean.Analysis.OAISevenEighthsRootSmooth.one_add_normalized_pair_eq_residual_div
#print axioms RHLean.Analysis.OAISevenEighthsRootSmooth.normalizedCrossGram_bounds
#print axioms RHLean.Analysis.OAISevenEighthsRootSmooth.one_add_normalizedCrossGram_eq_mertens_residual
#print axioms RHLean.Analysis.OAISevenEighthsRootSmooth.rootSmoothCrossGram_eq_shiftedMertensSq
#print axioms RHLean.Analysis.OAISevenEighthsRootSmooth.normalized_surplus_mul_diagonal_eq_crossGram
#print axioms RHLean.Analysis.OAISevenEighthsRootSmooth.rootSmoothCrossGram_upper_of_sevenEighths
#print axioms RHLean.Analysis.OAISevenEighthsRootSmooth.normalized_surplus_bound_of_sevenEighths
