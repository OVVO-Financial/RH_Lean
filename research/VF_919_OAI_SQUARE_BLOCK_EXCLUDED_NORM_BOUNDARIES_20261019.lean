import «research.VF_919_OAI_SQUARE_BLOCK_FOUR_INDEX_COVARIANCE_20261019»
import RHLean.Analysis.MobiusRenewalTelescope

/-!
# OAI principal norm coefficient -> EXACT square-block covariance

This is the ORIGINAL completed sharp square shell at EVERY R >= 4:
    S_R = M((R+1)^2-1) - M(R^2-1).

Import the already-proved (not hypothesized) norm/factor identity
  vf919Mertens_eq_excludedNorm_periodicKernel
which includes:
  * true rational mu(n) and actual 1,3,4,12 excluded Euler factors;
  * FULL Eisenstein norm coefficient, with its split prime multiplicities;
  * periodic 36 quotient-floor weight Q36(floor(X/m));
  * endpoint X inclusive, so R^2 is INCLUDED and (R+1)^2 excluded.

The ENDPOINT DIFFERENCE is taken before its Hermitian square. Consequently
all upper*lower cross terms survive, exactly as in the original
vf919SquareShellCovariance and its four-index quadratic Hecke expansion.

This is the full principal-norm, physical source-level identity. It does
not equate this floor weight to OAI's cubic theta completed physical
probe, nor import any analytic sextic-character moment bound.
-/

noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHLean.Analysis

def vf919OAIhighSquareEndpoint (R : ℕ) : ℕ := (R + 1) ^ 2 - 1
def vf919OAIlowSquareEndpoint (R : ℕ) : ℕ := R ^ 2 - 1

/-- Full native excluded-(2,3) periodic coefficient at sharp endpoint X. -/
def vf919OAIExcludedNormSharpPrefix (X : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 X,
    vf919ExcludedNormCoefficients m *
      (vf919SharpQuotientKernel36 (X / m) : ℂ)

/-- The 36-periodic coefficient expansion IS the true complex Mertens
    prefix whenever the original excluded-Euler formula is valid. -/
theorem vf919OAIExcludedNormSharpPrefix_eq_actualMertens (X : ℕ)
    (hX : 12 ≤ X) :
    vf919OAIExcludedNormSharpPrefix X = mertensSummatory X := by
  unfold vf919OAIExcludedNormSharpPrefix
  rw [mertensSummatory_eq_sum_Icc]
  exact (vf919Mertens_eq_excludedNorm_periodicKernel X hX).symm

theorem vf919OAIhighSquareEndpoint_succ (R : ℕ) (hR : 4 ≤ R) :
    vf919OAIhighSquareEndpoint R + 1 = (R + 1) ^ 2 := by
  unfold vf919OAIhighSquareEndpoint
  have h : 0 < (R + 1) ^ 2 := by nlinarith
  omega

theorem vf919OAIlowSquareEndpoint_succ (R : ℕ) (hR : 4 ≤ R) :
    vf919OAIlowSquareEndpoint R + 1 = R ^ 2 := by
  unfold vf919OAIlowSquareEndpoint
  have h : 0 < R ^ 2 := by nlinarith
  omega

/-- The FULL original Mobius square block equals one exact upper
    excluded-norm quotient sum MINUS one lower excluded-norm quotient
    sum. This transports all norm/multiple and floor boundary terms. -/
theorem vf919SquareShellSum_eq_OAI_excludedNorm_high_sub_low
    (R : ℕ) (hR : 4 ≤ R) :
    (vf919SquareShellSum R : ℂ) =
      vf919OAIExcludedNormSharpPrefix (vf919OAIhighSquareEndpoint R) -
        vf919OAIExcludedNormSharpPrefix (vf919OAIlowSquareEndpoint R) := by
  have hhi : 12 ≤ vf919OAIhighSquareEndpoint R := by
    unfold vf919OAIhighSquareEndpoint
    nlinarith
  have hlo : 12 ≤ vf919OAIlowSquareEndpoint R := by
    unfold vf919OAIlowSquareEndpoint
    nlinarith
  have hupper := realMertensLength_cast_eq_mertensSummatory
    (vf919OAIhighSquareEndpoint R)
  have hlower := realMertensLength_cast_eq_mertensSummatory
    (vf919OAIlowSquareEndpoint R)
  rw [vf919OAIhighSquareEndpoint_succ R hR] at hupper
  rw [vf919OAIlowSquareEndpoint_succ R hR] at hlower
  calc
    (vf919SquareShellSum R : ℂ) =
        (realMertensLength ((R + 1) ^ 2) : ℂ) -
          (realMertensLength (R ^ 2) : ℂ) := by
            simp [vf919SquareShellSum]
    _ = mertensSummatory (vf919OAIhighSquareEndpoint R) -
          mertensSummatory (vf919OAIlowSquareEndpoint R) := by
            rw [hupper, hlower]
    _ = vf919OAIExcludedNormSharpPrefix
          (vf919OAIhighSquareEndpoint R) -
        vf919OAIExcludedNormSharpPrefix
          (vf919OAIlowSquareEndpoint R) := by
            rw [vf919OAIExcludedNormSharpPrefix_eq_actualMertens
              _ hhi, vf919OAIExcludedNormSharpPrefix_eq_actualMertens
              _ hlo]

/-- The genuine signed square-block covariance, expanded at BOTH Hecke
    divisor endpoints, plus the original squarefree diagonal, equals
    the square of the exact high-minus-low periodic norm/character sum. -/
theorem vf919SquareShell_original_covariance_eq_OAI_norm_doubleBoundary
    (R : ℕ) (hR : 4 ≤ R) :
    (vf919SquareShellDiagonal R : ℂ) +
        2 * vf919SquareShellFourIndexHeckeCovariance R =
      (vf919OAIExcludedNormSharpPrefix (vf919OAIhighSquareEndpoint R)) ^ 2 +
      (vf919OAIExcludedNormSharpPrefix (vf919OAIlowSquareEndpoint R)) ^ 2 -
      2 * vf919OAIExcludedNormSharpPrefix (vf919OAIhighSquareEndpoint R) *
        vf919OAIExcludedNormSharpPrefix (vf919OAIlowSquareEndpoint R) := by
  have henergy := vf919SquareShell_signedGreenKubo R
  have hcov :=
    vf919SquareShell_actual_signed_covariance_eq_fourIndexHecke R
  have hs :=
    vf919SquareShellSum_eq_OAI_excludedNorm_high_sub_low R hR
  have hcomplex := congrArg (fun x : ℝ => (x : ℂ)) henergy
  push_cast at hcomplex
  rw [hcov] at hcomplex
  rw [hs] at hcomplex
  calc
    (vf919SquareShellDiagonal R : ℂ) +
        2 * vf919SquareShellFourIndexHeckeCovariance R =
      (vf919OAIExcludedNormSharpPrefix
          (vf919OAIhighSquareEndpoint R) -
        vf919OAIExcludedNormSharpPrefix
          (vf919OAIlowSquareEndpoint R)) ^ 2 := hcomplex.symm
    _ = _ := by ring

#print axioms vf919OAIExcludedNormSharpPrefix_eq_actualMertens
#print axioms vf919SquareShellSum_eq_OAI_excludedNorm_high_sub_low
#print axioms vf919SquareShell_original_covariance_eq_OAI_norm_doubleBoundary

end RHLean.Analysis
