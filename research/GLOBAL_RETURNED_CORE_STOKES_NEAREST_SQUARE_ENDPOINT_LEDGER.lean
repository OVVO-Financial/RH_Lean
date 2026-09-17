import Mathlib
import «research.GLOBAL_RETURNED_CORE_STOKES_ALL_ENDPOINT_MERTENS_LEDGER»
import «research.LOW_OWNER_Q2_NEAREST_SQUARE_ENDPOINT»

/-!
# Exact nearest-square endpoint ledger for the final Stokes boundary

This file remains entirely algebraic.

The all-endpoint Stokes gap contains the literal reciprocal q^2 daughter column.
The existing nearest-square theorem decomposes that column *before squaring* as

  completed-square endpoint column + oriented midpoint shell.

Substituting that exact equality into the already-identified Stokes endpoint
gap gives one joint completed-square/root endpoint gap minus the signed shell.
No shell norm, frame bound, triangle inequality, or conductor estimate is used.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- The endpoint gap after every literal q^2 daughter has been moved to its
canonical nearest completed-square endpoint, but before paying the oriented
midpoint shell. -/
def lowOwnerStokesCompletedSquareEndpointGap (R : ℕ) : ℂ :=
  mertensSummatory (R - 1) -
    mertensSummatory (squareRootEndpoint R) -
      lowOwnerNearestSquareReciprocalColumn R

/-- **Exact pre-square nearest-endpoint splice.** -/
theorem lowOwnerStokesAllEndpointMertensGap_eq_completedSquareGap_sub_shell
    (R : ℕ) :
    lowOwnerStokesAllEndpointMertensGap R =
      lowOwnerStokesCompletedSquareEndpointGap R -
        lowOwnerNearestSquareReciprocalShell R := by
  unfold lowOwnerStokesAllEndpointMertensGap
    lowOwnerStokesCompletedSquareEndpointGap
  rw [← lowOwnerReciprocalMertensColumn_eq_endpointSum,
    lowOwnerReciprocalMertensColumn_eq_nearestSquare_add_shell]
  ring

/-- **Final Stokes boundary in nearest-square endpoint currency.**

The only terms inside the norm are now the root endpoint pair, the reciprocal
completed-square daughter column, and the exact signed midpoint shell. -/
theorem lowOwnerCanonicalSignedStokesFinalBoundary_eq_completedSquareGap_sub_shell_normSq_sub_diagonal
    {R : ℕ} (hR : 56 ≤ R) :
    lowOwnerCanonicalSignedStokesFinalBoundary R =
      ‖lowOwnerStokesCompletedSquareEndpointGap R -
          lowOwnerNearestSquareReciprocalShell R‖ ^ 2 -
        lowOwnerZeroFrequencyMobiusDiagonal R := by
  rw [lowOwnerCanonicalSignedStokesFinalBoundary_eq_allEndpointMertensGapNormSq_sub_diagonal hR,
    lowOwnerStokesAllEndpointMertensGap_eq_completedSquareGap_sub_shell]

end RHLean.Proof
