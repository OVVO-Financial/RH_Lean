import Mathlib
import RHLean.Analysis.AlpogeNNSBandSchur
import RHLean.Analysis.NativePNTSignedSecondSelberg

/-!
# Native full signed Selberg recurrence: NNS/Schur principal overshoot

The existing source-specific research theorem
  research/ALPOGE_SIGNED_SELBERG_INTEGRAL_SCHUR_20261120.lean
proves the actual prime-square plus distinct-semiprime near-root band
is D*(2I-J)*D, with ell_i=log p_i, p_i in [3R/4,R).
The chosen band is NOT the entire Selberg kernel.

Here C is defined as the COMPLETE original signed second-Selberg
recurrence with that source band algebraically subtracted. It keeps
the first-remainder, Lambda convolution, every other K2 row,
and the signed floor defect. No positivity is postulated for C.

The NNS target-invariant Schur covariance of the selected band has
an unconditionally paid positive correction. For each finite band,
the only remaining one-sided cost is the principal-mode overshoot
of this full complement. The root cutoff X=R^2-1 is exact.

NO complete-source overshoot estimate is asserted; this does NOT prove
RH. The underlying actual-source identification resides in research,
not as an illicit import of an externally proved theorem.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

/-- Full native signed Selberg right-hand side with one precisely
defined 2I-J prime-band charge removed; everything else is retained. -/
def alpogeNNSCompleteSelbergComplement
    (R m : ℕ) (ell : Fin m → ℝ) : ℝ :=
  nativePNTSignedSelbergRemainder (R ^ 2 - 1) *
      Real.log (((R ^ 2 - 1 : ℕ) : ℝ)) -
    nativePNTLambdaSignedSelbergRemainderMass (R ^ 2 - 1) +
    (nativePNTSignedSecondSelbergKernelErrorMass (R ^ 2 - 1) -
      alpogeNNSBandCharge m ell) -
    nativePNTLambdaFloorLogSignedDefectMass (R ^ 2 - 1)

/-- The complete original-source equality at the exact upper square
endpoint. There is NO missing K2, square, cofactor, or floor term. -/
theorem alpogeNNSError_log_sq_eq_completeComplement_add_band
    (R m : ℕ) (ell : Fin m → ℝ) :
    nativePNTError (R ^ 2 - 1) *
        (Real.log (((R ^ 2 - 1 : ℕ) : ℝ))) ^ 2 =
      alpogeNNSCompleteSelbergComplement R m ell +
        alpogeNNSBandCharge m ell := by
  rw [nativePNTError_mul_log_sq_eq_signedSecondSelberg]
  unfold alpogeNNSCompleteSelbergComplement
  ring

/-- The new one-sided full-source inequality, with EVERY positive
centered NNS covariance payment explicitly discharged. The first
max includes the actual Chebyshev error, not a model sequence.
The remaining max contains the complete signed physical complement
minus the explicit negative principal Gram mode. -/
theorem alpogeNNSCompleteSelberg_oneSided_le_principalOvershoot
    (R m : ℕ) (ell : Fin m → ℝ) (a b : ℝ)
    (hband : ∀ i : Fin m, a ≤ ell i ∧ ell i ≤ b) :
    max ((m : ℝ) * (nativePNTError (R ^ 2 - 1) *
       (Real.log (((R ^ 2 - 1 : ℕ) : ℝ))) ^ 2)) 0 ≤
      max ((m : ℝ) * alpogeNNSCompleteSelbergComplement R m ell -
        ((m : ℝ) - 2) * (∑ i : Fin m, ell i) ^ 2) 0 +
        ((m : ℝ) ^ 2 / 2) * (b - a) ^ 2 := by
  rw [alpogeNNSError_log_sq_eq_completeComplement_add_band]
  exact alpogeNNSBandOneSidedCharge_le_principal_overshoot
    m ell (alpogeNNSCompleteSelbergComplement R m ell) a b hband

end RHLean.Analysis
