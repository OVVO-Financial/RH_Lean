import OAI.NumberTheory.DirichletL.Detector.FinalAssemblyUnconditional
import «research.VF_919_SEVEN_EIGHTHS_SIGNED_COVARIANCE_20261019»
import «research.VF_919_SEVEN_EIGHTHS_SQUARE_SHELL_BRIDGE_20261019»

/-!
# Unconditional actual OpenAI certified 7/8 in RH_Lean's ORIGINAL square shells

This file imports the COMPLETE original OpenAI Lean 4.34.1 analytic
certificate. It does NOT introduce a new moment estimate, a zero-free
assumption, an ideal-fibre hypothesis, or a random-sign approximation.

1. OpenAI terminal_certificate -> detector_certified_bands -> zeta_nonzero.
2. RH_Lean's separately proved zeta-strip / Mertens converse.
3. RH_Lean's ORIGINAL global signed zero-target Green-Kubo covariance.
4. RH_Lean's ORIGINAL square blocks, telescoped exactly at every K^2.

This is a fully unconditional 7/8 theorem *for the exact original
Möbius pair covariance* provided the original imported OpenAI
certificate has only standard kernel axioms. It does NOT claim that an
arbitrary smooth OAI theta probe equals a sharp single-block indicator.
No new unproved analytic inequality is needed for THIS theorem.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

/-- The entire original, UNCONDITIONAL OpenAI proof DAG discharges
    the native 7/8 zero-free proposition. The analytic proof is imported,
    not re-postulated as hZ or hMoment. -/
theorem openai434_actual_zeta_nonzero
    (s : ℂ) (hs : (7 : ℝ) / 8 < s.re) :
    riemannZeta s ≠ 0 :=
  OAI.SevenEighths.ProbeFinalAssemblyUnconditional.zeta_nonzero s hs

/-- This is the ORIGINAL RHLean physical Mertens positive-lag
    signed covariance bound, at EVERY integer X and EVERY epsilon,
    obtained unconditionally from the genuine OpenAI analytic proof.
    No smooth-to-sharp assumption or alternative carrier. -/
theorem openai434_actual_global_signed_covariance :
    VF919SevenEighthsSignedCovarianceBound :=
  vf919_sevenEighthsSignedCovariance_of_zetaNonzero
    (fun s hs => openai434_actual_zeta_nonzero s hs)

/-- The original signed positive-lag covariance is paid with its
    EXACT squarefree diagonal; no K_X <= X substitution. -/
theorem openai434_actual_global_signed_pairs
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 1 ≤ X →
      2 * realMertensPositiveLagPairSum (X + 1) ≤
        (C * Real.rpow (X : ℝ) ((7 : ℝ) / 8 + ε)) ^ 2 -
          realMertensDiagonal (X + 1) :=
  vf919_sevenEighthsSignedPair_upper_of_zetaNonzero
    (fun s hs => openai434_actual_zeta_nonzero s hs) ε hε

/-- A direct complete-block version: the ACTUAL sum of ALL physical
    square-block Möbius signs r=0,...,K-1 obeys the same certified
    seven-eighths Mertens exponent. In particular all between-block
    signed covariances remain inside the LHS square. -/
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

/-- At every complete square endpoint, the ORIGINAL full Green--Kubo
    diagonal plus all strictly ordered physical pairs, including
    different square blocks, has the genuine unconditional 7/8 bound. -/
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
#print axioms openai434_actual_global_signed_pairs
#print axioms openai434_actual_all_square_blocks_seven_eighths
#print axioms openai434_actual_all_square_block_covariance

end RHLean.Analysis
