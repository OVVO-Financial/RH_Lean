import Mathlib
import RHLean.Analysis.AlpogeNegativeSelbergSemivariance

/-!
# The explicit premise-free endpoint for the native negative LPM2

`AlpogeNativeSquareNegativeLPM2Endpoint` is the target statement

  ∀ ε > 0, ∃ C ≥ 0, ∀ H ≥ 2,  Q₋(H) ≤ C · H^(3+ε),

where `Q₋(H) = alpogeNativeSquareNegativeLPM2 H`. By
`alpogeFullMatchedSquareNegativeLPM2_eq_native` (for `H ≥ 2`), the same `Q₋(H)`
is the normalized negative semivariance `∑ (B_R - C_R)₊² / log⁴ X_R` of the
complete signed second-Selberg source.

**This file does not prove the endpoint.** It records the target as a `Prop`,
together with the only currently proved route to it, through the explicit
pointwise supplier `NativeSquareDyadicChebyshevBound`. A completed endpoint must
be a theorem of exactly this statement whose dependency closure contains no
`NativeSquareDyadicChebyshevBound` premise. Two routes qualify: a checked RH ⇒ ψ
chain from the verified RH theorem, or an independently proved geometric LPM2
estimate.

The finite identities, the finite moment inequality and the conditional
transfer in `AlpogeNegativeSelbergSemivariance` are left unchanged.
-/

namespace RHLean.Analysis

/-- The premise-free critical endpoint for the native negative LPM2.
A target statement only: it is not proved in RH_Lean. -/
def AlpogeNativeSquareNegativeLPM2Endpoint : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ H : ℕ, 2 ≤ H →
        alpogeNativeSquareNegativeLPM2 H ≤ C * (H : ℝ) ^ (3 + ε)

/-- The currently proved route to the endpoint, through the explicit pointwise
square-root Chebyshev supplier (which remains an open premise). -/
theorem alpogeNativeSquareNegativeLPM2Endpoint_of_dyadicChebyshev
    (h : NativeSquareDyadicChebyshevBound) :
    AlpogeNativeSquareNegativeLPM2Endpoint :=
  alpogeNativeSquareNegativeLPM2_of_dyadicChebyshev h

-- Kernel axiom audit of the native LPM2 chain (recorded in the hosted build log).
#print axioms RHLean.Analysis.alpogeFullMatchedSecondSelberg_eq_nativeError
#print axioms RHLean.Analysis.alpogeNegativePart_mul_nonneg
#print axioms RHLean.Analysis.alpogeFullMatchedSecondSelberg_negativePart
#print axioms RHLean.Analysis.alpogeFullMatchedSquareNegativeLPM2_eq_native
#print axioms RHLean.Analysis.alpogeNativeSquareNegativeLPM2_le_uniform
#print axioms RHLean.Analysis.alpogeNativeSquareNegativeLPM2_of_dyadicChebyshev
#print axioms RHLean.Analysis.alpogeNativeSquareNegativeLPM2Endpoint_of_dyadicChebyshev

end RHLean.Analysis
