import Mathlib
import «research.GLOBAL_RETURNED_CORE_STOKES_ENDPOINT_AMPLITUDE_IDENTIFICATION»
import «research.CANONICAL_ROUGH_GLOBAL_BOUNDS»

/-!
# Exact all-endpoint Mertens ledger for the final Stokes boundary

No Fourier estimate appears here.

The canonical rough correlation is already exactly the Mertens interval
`M(R-1) - M(X_R)`.  The reciprocal daughter column is exactly the weighted sum
of the literal q^2 daughter prefixes `M(Y_q)/q`.  Hence the endpoint gap seen by
the final Stokes boundary is one explicit linear combination of named Mertens
endpoints:

  M(R-1) - M(X_R) - sum_q M(Y_q)/q.

This is the endpoint object any later completed-period/conductor frame must
represent exactly.  No prime-sine surrogate is introduced.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Literal reciprocal daughter Mertens column written directly in the complex
Mertens prefix currency. -/
def lowOwnerReciprocalMertensEndpointSum (R : ℕ) : ℂ :=
  ∑ q ∈ canonicalRoughLowQ2Owners R,
    (1 / (q : ℂ)) * mertensSummatory (rawQ2ChildCutoff R q)

/-- The existing reciprocal daughter column is exactly the preceding endpoint
sum. -/
theorem lowOwnerReciprocalMertensColumn_eq_endpointSum (R : ℕ) :
    lowOwnerReciprocalMertensColumn R =
      lowOwnerReciprocalMertensEndpointSum R := by
  unfold lowOwnerReciprocalMertensColumn
    lowOwnerReciprocalMertensEndpointSum
    lowOwnerRawMertensAmplitude
  apply Finset.sum_congr rfl
  intro q _hq
  rw [mertensSummatoryInt_cast]

/-- Exact linear endpoint gap underlying the final signed Stokes boundary. -/
def lowOwnerStokesAllEndpointMertensGap (R : ℕ) : ℂ :=
  mertensSummatory (R - 1) -
    mertensSummatory (squareRootEndpoint R) -
      lowOwnerReciprocalMertensEndpointSum R

/-- The physical AMP endpoint gap is literally the all-endpoint Mertens ledger. -/
theorem squareRootCorrelation_sub_reciprocalColumn_eq_allEndpointMertensGap
    {R : ℕ} (hR : 2 ≤ R) :
    squareRootCanonicalRoughCorrelation R -
        lowOwnerReciprocalMertensColumn R =
      lowOwnerStokesAllEndpointMertensGap R := by
  rw [squareRootCanonicalRoughCorrelation_eq_mertens_pred_sub_endpoint R hR,
    lowOwnerReciprocalMertensColumn_eq_endpointSum]
  rfl

/-- **Exact all-endpoint form of the final Stokes boundary.**

The final physical Stokes ledger is the squared norm of one explicit endpoint
Mertens combination, minus the elementary diagonal already isolated by the
one-amplitude Gram identity. -/
theorem lowOwnerCanonicalSignedStokesFinalBoundary_eq_allEndpointMertensGapNormSq_sub_diagonal
    {R : ℕ} (hR : 56 ≤ R) :
    lowOwnerCanonicalSignedStokesFinalBoundary R =
      ‖lowOwnerStokesAllEndpointMertensGap R‖ ^ 2 -
        lowOwnerZeroFrequencyMobiusDiagonal R := by
  rw [lowOwnerCanonicalSignedStokesFinalBoundary_eq_endpointGapNormSq_sub_diagonal hR,
    squareRootCorrelation_sub_reciprocalColumn_eq_allEndpointMertensGap
      (R := R) (by omega)]

end RHLean.Proof
