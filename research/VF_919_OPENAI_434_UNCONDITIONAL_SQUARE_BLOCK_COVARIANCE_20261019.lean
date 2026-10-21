import «research.VF_919_COMMON_PROBE_SEVEN_EIGHTHS_20261020»
import «research.VF_919_SEVEN_EIGHTHS_SIGNED_COVARIANCE_20261019»
import «research.VF_919_SEVEN_EIGHTHS_SQUARE_SHELL_BRIDGE_20261019»

/-!
# Actual seven-eighths in RH_Lean's original Mobius sequence and square shells

The imported local common-probe module constructs the intermediate analytic
certificate, assembles LOW and HIGH for one source, and discharges the beta-gap
by the Mellin contradiction. It reuses the pinned OpenAI intermediate analytic
lemmas, but does not import or call the upstream terminal nonvanishing theorem.

This file then uses RH_Lean's proved Mertens converse and exact physical
Green--Kubo identities. This is the requested FIRST-stage seven-eighths result.
A direct sharp covariance estimate avoiding that analytic intermediate is a
separate later task; it is not claimed here.

Existing exported names are preserved for downstream consumers.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

/-- The locally assembled common-probe argument supplies nonvanishing,
not an imported terminal theorem or an unproved hZ hypothesis. -/
theorem openai434_actual_zeta_nonzero
    (s : ℂ) (hs : (7 : ℝ) / 8 < s.re) :
    riemannZeta s ≠ 0 :=
  VF919SevenEighths.zeta_nonzero s hs

/-- Original rational Mobius signed covariance at every integer. The
analytic intermediate is explicit and proved, not suppressed. -/
theorem openai434_actual_global_signed_covariance :
    VF919SevenEighthsSignedCovarianceBound :=
  vf919_sevenEighthsSignedCovariance_of_zetaNonzero
    (fun s hs => openai434_actual_zeta_nonzero s hs)

/-- In particular, for every positive epsilon the genuine Mertens function
has a uniform power bound of exponent 7/8 + epsilon. -/
theorem commonProbe_actual_mertens_growth :
    MertensExponent.MertensGrowthAtMost ((7 : ℝ) / 8) :=
  vf919_sevenEighthsSignedCovariance_iff_mertensGrowth.mp
    openai434_actual_global_signed_covariance

/-- Keep the exact squarefree diagonal and all signed pairs. -/
theorem openai434_actual_global_signed_pairs
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 1 ≤ X →
      2 * realMertensPositiveLagPairSum (X + 1) ≤
        (C * Real.rpow (X : ℝ) ((7 : ℝ) / 8 + ε)) ^ 2 -
          realMertensDiagonal (X + 1) :=
  vf919_sevenEighthsSignedPair_upper_of_zetaNonzero
    (fun s hs => openai434_actual_zeta_nonzero s hs) ε hε

/-- All complete physical square shells, including their cross-shell
terms inside the squared cumulative signed sum. -/
theorem openai434_actual_all_square_blocks_seven_eighths
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K : ℕ, 2 ≤ K →
      (∑ R ∈ Finset.range K, vf919SquareShellSum R) ^ 2 ≤
        (C * Real.rpow (((K ^ 2 - 1 : ℕ) : ℝ))
          ((7 : ℝ) / 8 + ε)) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ :=
    openai434_actual_global_signed_covariance ε hε
  refine ⟨C, hC, ?_⟩
  intro K hK
  have hKsq : 2 ≤ K ^ 2 := by nlinarith
  have hX : 1 ≤ K ^ 2 - 1 := by omega
  have hsucc : (K ^ 2 - 1 : ℕ) + 1 = K ^ 2 := by omega
  have hb := hbound (K ^ 2 - 1) hX
  rw [hsucc] at hb
  calc
    (∑ R ∈ Finset.range K, vf919SquareShellSum R) ^ 2 =
        realMertensLength (K ^ 2) ^ 2 := by
          rw [vf919SquareShell_telescope]
    _ = realMertensDiagonal (K ^ 2) +
          2 * realMertensPositiveLagPairSum (K ^ 2) :=
            realMertensLength_sq_eq_diagonal_add_two_mul_positiveLagPairSum _
    _ ≤ (C * Real.rpow (((K ^ 2 - 1 : ℕ) : ℝ))
          ((7 : ℝ) / 8 + ε)) ^ 2 := hb

/-- Exact original full pair covariance at every complete square endpoint. -/
theorem openai434_actual_all_square_block_covariance
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K : ℕ, 2 ≤ K →
      realMertensDiagonal (K ^ 2) +
        2 * realMertensPositiveLagPairSum (K ^ 2) ≤
          (C * Real.rpow (((K ^ 2 - 1 : ℕ) : ℝ))
            ((7 : ℝ) / 8 + ε)) ^ 2 := by
  obtain ⟨C, hC, hb⟩ :=
    openai434_actual_global_signed_covariance ε hε
  refine ⟨C, hC, ?_⟩
  intro K hK
  have hsq : 2 ≤ K ^ 2 := by nlinarith
  have hX : 1 ≤ K ^ 2 - 1 := by omega
  have hsucc : (K ^ 2 - 1 : ℕ) + 1 = K ^ 2 := by omega
  have h := hb (K ^ 2 - 1) hX
  rwa [hsucc] at h

#print axioms openai434_actual_zeta_nonzero
#print axioms openai434_actual_global_signed_covariance
#print axioms commonProbe_actual_mertens_growth
#print axioms openai434_actual_global_signed_pairs
#print axioms openai434_actual_all_square_blocks_seven_eighths
#print axioms openai434_actual_all_square_block_covariance

end RHLean.Analysis
