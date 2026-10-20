import OAI.NumberTheory.DirichletL.Detector.FinalAssemblyUnconditional
import «research.VF_919_SEVEN_EIGHTHS_SIGNED_COVARIANCE_20261019»
import «research.VF_919_OAI_GLOBAL_SQUARE_BLOCK_ALL_PAIR_COVARIANCE_20261019»
import «research.VF_919_OAI_GENUINE_IDEAL_ORDERED_PHYSICAL_PAIRS_20261019»

/-!
# Actual OpenAI certified 7/8 proof in ORIGINAL RHLean square-block covariance

Imports actual original OpenAI final certificate:
terminal_certificate -> detector_certified_bands -> zeta_of_certified.

No analytic estimate is assumed, and all bounds are quantified over every X.
The native signed Mobius positive-lag pairs and full cross-square-block gram
are the existing RHLean objects, not a replacement model.

The original OAI compensated theta source is a different physical function
from the sharp Mobius cutoff. The unconditional conclusion imported here is
a valid derivation of the original RHLean covariance bound, not a claim that
the intermediate sharp moment equals an OAI smooth theta moment.
-/

noncomputable section

namespace RHLean.Analysis

/-- OpenAI's original certified zero detector, not an assumed hypothesis. -/
theorem openai_original_zeta_seven_eighths
    (s : ℂ) (hs : (7 : ℝ) / 8 < s.re) :
    riemannZeta s ≠ 0 :=
  OAI.SevenEighths.ProbeFinalAssemblyUnconditional.zeta_nonzero s hs

/-- True signed zero-target covariance at ALL positive integer X.
    Its analytic source is the entire imported OpenAI certification. -/
theorem openai_original_signed_covariance_seven_eighths :
    VF919SevenEighthsSignedCovarianceBound :=
  vf919_sevenEighthsSignedCovariance_of_zetaNonzero
    (fun s hs => openai_original_zeta_seven_eighths s hs)

/-- Every original physical off-diagonal pair remains present. -/
theorem openai_original_signed_pair_upper_seven_eighths
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℕ, 1 ≤ x →
      2 * realMertensPositiveLagPairSum (x + 1) ≤
        (C * Real.rpow (x : ℝ) ((7 : ℝ) / 8 + ε)) ^ 2 -
          realMertensDiagonal (x + 1) :=
  vf919_sevenEighthsSignedPair_upper_of_zetaNonzero
    (fun s hs => openai_original_zeta_seven_eighths s hs) ε hε

/-- Same UNCONDITIONAL 7/8 bound on the full signed source gram of
    ALL square shells below K, including cross-shell covariance. -/
theorem openai_original_global_square_block_gram_seven_eighths
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K : ℕ, 2 ≤ K →
      (vf919OAIGlobalSquareBlockFullGram K).re ≤
        (C * Real.rpow (((K ^ 2 - 1 : ℕ) : ℝ))
          ((7 : ℝ) / 8 + ε)) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ :=
    openai_original_signed_covariance_seven_eighths ε hε
  refine ⟨C, hC, ?_⟩
  intro K hK
  have hK2 : 2 ≤ K ^ 2 := by nlinarith
  have hX : 1 ≤ K ^ 2 - 1 := by omega
  have hsucc : (K ^ 2 - 1 : ℕ) + 1 = K ^ 2 := by omega
  have hc := hbound (K ^ 2 - 1) hX
  rw [hsucc] at hc
  have hGram := vf919OAI_original_global_signed_covariance_eq_full_blockNormGram K
  have hRe : (vf919OAIGlobalSquareBlockFullGram K).re =
      realMertensDiagonal (K ^ 2) +
        2 * realMertensPositiveLagPairSum (K ^ 2) := by
    rw [← hGram]
    simp
  rw [hRe]
  exact hc

/-- Exact strict original physical site pair, with both ideal norm fibers. -/
theorem openai_original_strict_physical_pair_equality
    (F : ℕ → ℂ)
    (hF : ∀ m, F m = vf919EisensteinNormCoefficients m)
    (R : ℕ) :
    (vf919SquareShellCovariance R : ℂ) =
      vf919OAIOrderedPhysicalIdealFiberCovariance F R :=
  vf919OAI_original_ordered_covariance_eq_any_real_ideal_fiber F hF R

#print axioms openai_original_zeta_seven_eighths
#print axioms openai_original_signed_covariance_seven_eighths
#print axioms openai_original_signed_pair_upper_seven_eighths
#print axioms openai_original_global_square_block_gram_seven_eighths
#print axioms openai_original_strict_physical_pair_equality

end RHLean.Analysis
