import «research.VF_919_OAI_SQUARE_BLOCK_ONE_SOURCE_FULL_NORM_GRAM_20261019»

/-!
# GLOBAL actual signed Green--Kubo covariance: ALL square-block cross terms

The real target is not merely within one block! At square endpoints
  M(K^2-1) = sum_{0<=R<K} S_R.
Consequently the FULL global original NNS zero-target energy is the
complex Gram of ALL pairs of distinct/identical square blocks:
  K_global + 2*C_global
     = sum_{R<K}sum_{T<K} S_R * S_T.

Each S_R with R>=4 is identified EXACTLY with the principal
quadratic/Eisenstein 36-periodic norm source and its honest half-open
physical boundary from the preceding module. The first four roots use
their original physical Mobius square-shell values (no fabricated
Euler exclusions outside the original prefix theorem's X>=12 domain).

There is NO missing between-block covariance, parent/shell cross bill,
squarefree zero, original initial prefix, or arbitrary random character
in this theorem. This is still an exact arithmetic source identity.
The nontrivial uniform signed quartic/moment estimate on the SAME
ideal-labelled analytic source remains a separate proof obligation.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

/-- One exact source per physical square block. Early finite blocks are
    literal native Mobius; ALL R>=4 have the full 36-periodic norm source. -/
def vf919OAIGlobalOriginalBlockSource (R : ℕ) : ℂ :=
  if R < 4 then (vf919SquareShellSum R : ℂ)
  else vf919OAIExactSquareNormSource R

/-- Every source equals its original full physical square-shell sum. -/
theorem vf919OAIGlobalOriginalBlockSource_eq_trueShell (R : ℕ) :
    vf919OAIGlobalOriginalBlockSource R =
      (vf919SquareShellSum R : ℂ) := by
  by_cases h : R < 4
  · simp [vf919OAIGlobalOriginalBlockSource, h]
  · simpa [vf919OAIGlobalOriginalBlockSource, h] using
      (vf919OAIExactSquareNormSource_eq_originalSquareShell
        R (Nat.le_of_not_gt h))

/-- NO prefix condition: every complete shell from zero through K-1,
    including the original 0/1/2/3 lower-prefix contribution, sums to
    the native all-integer Mobius prefix immediately before K^2. -/
def vf919OAIGlobalSquareBlockSource (K : ℕ) : ℂ :=
  ∑ R ∈ Finset.range K, vf919OAIGlobalOriginalBlockSource R

theorem vf919OAIGlobalSquareBlockSource_eq_trueMertens (K : ℕ) :
    vf919OAIGlobalSquareBlockSource K =
      (realMertensLength (K ^ 2) : ℂ) := by
  have h := vf919SquareShell_telescope K
  have hc := congrArg (fun x : ℝ => (x : ℂ)) h
  push_cast at hc
  unfold vf919OAIGlobalSquareBlockSource
  calc
    (∑ R ∈ Finset.range K, vf919OAIGlobalOriginalBlockSource R) =
      ∑ R ∈ Finset.range K, (vf919SquareShellSum R : ℂ) := by
        apply Finset.sum_congr rfl
        intro R _hR
        exact vf919OAIGlobalOriginalBlockSource_eq_trueShell R
    _ = (realMertensLength (K ^ 2) : ℂ) := hc

/-- Full complex double source including EVERY ordered pair of square
    blocks, WITH all r=s within-block and r≠s cross-block payments. -/
def vf919OAIGlobalSquareBlockFullGram (K : ℕ) : ℂ :=
  ∑ R ∈ Finset.range K,
    ∑ T ∈ Finset.range K,
      vf919OAIGlobalOriginalBlockSource R *
        vf919OAIGlobalOriginalBlockSource T

theorem vf919OAIGlobalSquareBlockFullGram_eq_source_sq (K : ℕ) :
    vf919OAIGlobalSquareBlockFullGram K =
      (vf919OAIGlobalSquareBlockSource K) ^ 2 := by
  unfold vf919OAIGlobalSquareBlockFullGram
  calc
    (∑ R ∈ Finset.range K,
        ∑ T ∈ Finset.range K,
          vf919OAIGlobalOriginalBlockSource R *
            vf919OAIGlobalOriginalBlockSource T) =
      ∑ R ∈ Finset.range K,
        vf919OAIGlobalOriginalBlockSource R *
          (∑ T ∈ Finset.range K,
            vf919OAIGlobalOriginalBlockSource T) := by
              apply Finset.sum_congr rfl
              intro R _hR
              rw [Finset.mul_sum]
    _ = (vf919OAIGlobalSquareBlockSource K) ^ 2 := by
          rw [← Finset.sum_mul]
          simp [vf919OAIGlobalSquareBlockSource, pow_two]

/-- THE ORIGINAL GLOBAL NNS zero-target signed covariance is the complete
    square-block norm-source Gram. In particular the interblock pair
    contribution is present, not replaced by a sum of block energies.
    Holds at EVERY square endpoint without any analytic hypothesis. -/
theorem vf919OAI_original_global_signed_covariance_eq_full_blockNormGram
    (K : ℕ) :
    (realMertensDiagonal (K ^ 2) : ℂ) +
        2 * (realMertensPositiveLagPairSum (K ^ 2) : ℂ) =
      vf919OAIGlobalSquareBlockFullGram K := by
  have henergy :=
    realMertensLength_sq_eq_diagonal_add_two_mul_positiveLagPairSum
      (K ^ 2)
  have hc := congrArg (fun x : ℝ => (x : ℂ)) henergy
  push_cast at hc
  have hsource := vf919OAIGlobalSquareBlockSource_eq_trueMertens K
  have hgram := vf919OAIGlobalSquareBlockFullGram_eq_source_sq K
  rw [← hsource, ← hgram] at hc
  exact hc.symm

/-- Explicit exact source formula in the original complex Mertens
    summatory function with the correct final integer K^2-1. -/
theorem vf919OAI_original_global_Mertens_eq_all_square_sources
    (K : ℕ) (hK : 1 ≤ K) :
    mertensSummatory (K ^ 2 - 1) =
      vf919OAIGlobalSquareBlockSource K := by
  have hs :=
    realMertensLength_cast_eq_mertensSummatory (K ^ 2 - 1)
  have hK2 : (K ^ 2 - 1) + 1 = K ^ 2 := by
    have hh : 0 < K ^ 2 := by nlinarith
    omega
  rw [hK2] at hs
  rw [vf919OAIGlobalSquareBlockSource_eq_trueMertens]
  exact hs.symm

#print axioms vf919OAIGlobalOriginalBlockSource_eq_trueShell
#print axioms vf919OAIGlobalSquareBlockSource_eq_trueMertens
#print axioms vf919OAIGlobalSquareBlockFullGram_eq_source_sq
#print axioms vf919OAI_original_global_signed_covariance_eq_full_blockNormGram
#print axioms vf919OAI_original_global_Mertens_eq_all_square_sources

end RHLean.Analysis
