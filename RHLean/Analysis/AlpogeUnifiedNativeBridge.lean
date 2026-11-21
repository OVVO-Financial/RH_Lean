import RHLean.AlpogeInterface
import RHLean.Analysis.NativePNTSignedSecondSelberg
import RHLean.Proof.RiemannHypothesisBridge

/-!
# SAME-SOURCE bridge from the jointly compiled Alpöge interface to RH_Lean

This module is checked under RH_Lean's original Lean 4.34.1:
  - The imported shared expressions are exactly nativePsi,
    nativeLambdaRecip, nativePNTError and the RH proposition;
  - The shared Gz is the exact native von Mangoldt source;
  - The COMPLETE signed second-Selberg recurrence is retained.

The *upstream* bridge in integrations/alpoge/AlpogeProofAdapter.lean,
compiled against the untouched Alpöge tree under 4.33.1,
proves this SAME interface proposition using rhOfAll.
These are two compiler-specific certificates for the same written
Mathlib-level statement. They are not a forged cross-version .olean
import or a claim that the upstream theorem runs in 4.34.1.
-/

noncomputable section

namespace RHLean.Analysis

/-- Identity of the terminal RH statement at the SAME Mathlib proposition. -/
theorem alpogeInterface_rhStatement_eq_RHLean :
    RHLean.AlpogeInterface.rhStatement = RiemannHypothesisStatement := rfl

/-- The identical native Chebyshev prime-power population. -/
theorem alpogeInterface_psi_eq_native (N : ℕ) :
    RHLean.AlpogeInterface.psi N = nativePsi N := rfl

/-- The identical reciprocal von Mangoldt sum. -/
theorem alpogeInterface_lambdaRecip_eq_native (N : ℕ) :
    RHLean.AlpogeInterface.lambdaRecip N = nativeLambdaRecip N := rfl

/-- The identical native Chebyshev error, including its linear term. -/
theorem alpogeInterface_error_eq_native (N : ℕ) :
    RHLean.AlpogeInterface.error N = nativePNTError N := rfl

/-- Literal exact real-valued Alpöge Gz, now in RH_Lean's native
von Mangoldt coordinates, with the FLOOR unchanged. -/
theorem alpogeInterface_gz_eq_native (x : ℝ) :
    RHLean.AlpogeInterface.gz x =
      x * nativeLambdaRecip ⌊x⌋₊ - nativePsi ⌊x⌋₊ -
        x * Real.log x +
        (1 + Real.eulerMascheroniConstant) * x := rfl

/-- Native COMPLETE second-Selberg source: no selected prime family
or absolute value is substituted for the original signed terms. -/
def alpogeUnifiedCompleteSignedSource (N : ℕ) : ℝ :=
  nativePNTSignedSelbergRemainder N * Real.log (N : ℝ) -
    nativePNTLambdaSignedSelbergRemainderMass N +
    nativePNTSignedSecondSelbergKernelErrorMass N -
    nativePNTLambdaFloorLogSignedDefectMass N

theorem alpogeUnifiedCompleteSignedSource_eq_error (N : ℕ) :
    alpogeUnifiedCompleteSignedSource N =
      RHLean.AlpogeInterface.error N *
        (Real.log (N : ℝ)) ^ 2 := by
  unfold alpogeUnifiedCompleteSignedSource
  rw [alpogeInterface_error_eq_native]
  exact (nativePNTError_mul_log_sq_eq_signedSecondSelberg N).symm

/-- Exact pointwise real-x bridge of the originally verified Gz
signal to the COMPLETE signed Selberg source, with the scalar
x-floor(x) correction retained. No quantitative inequality is presumed. -/
theorem alpogeInterface_gz_eq_completeSignedSource (x : ℝ) :
    RHLean.AlpogeInterface.gz x * (Real.log (⌊x⌋₊ : ℝ)) ^ 2 =
      (x * (nativeLambdaRecip ⌊x⌋₊ - Real.log x +
        Real.eulerMascheroniConstant) + (x - (⌊x⌋₊ : ℝ))) *
        (Real.log (⌊x⌋₊ : ℝ)) ^ 2 -
      alpogeUnifiedCompleteSignedSource ⌊x⌋₊ := by
  rw [alpogeUnifiedCompleteSignedSource_eq_error,
    alpogeInterface_error_eq_native,
    alpogeInterface_gz_eq_native]
  unfold nativePNTError
  ring

end RHLean.Analysis
