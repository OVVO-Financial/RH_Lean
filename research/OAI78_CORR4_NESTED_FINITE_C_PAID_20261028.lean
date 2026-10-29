import Mathlib
import «research.CORR4_MIXED_TAIL_RECORD_PLATEAU_20261026»
import «research.LOW_OWNER_Q2_NEAREST_SQUARE_ENDPOINT_ENERGY»
import «research.EULER_SELF_DUAL_ENDPOINT_GATE_20261027»

/-!
# Original CORR-4 daughters in nested finite-C square-root coordinates

The physical q² daughter remains at the literal cutoff floor((R²-1)/q²).
Its nearest square endpoint is selected by the already certified midpoint
theorem. The signed shell is retained exactly, not discarded.

This file proves an identity on the original CORR-4 amplitude, not a
new finite-C estimate or an improvement of the Mertens exponent.
-/

noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHLean.Proof
open RHLean.Analysis RHLean.Arithmetic
attribute [local instance] Classical.propDecidable

/-- Original finite-C Euler numerator at a genuine completed-square root.
    The formula makes sense at all roots, without extra hypotheses. -/
def oai78NestedFiniteC (r : ℕ) : ℂ :=
  2 * mertensSummatory (r - 1) - mertensSummatory (squareRootEndpoint r)

/-- The nearest completed-square root associated with an ORIGINAL q² daughter. -/
def oai78NestedDaughterRoot (R q : ℕ) : ℕ :=
  q2NearestSquareRoot (rawQ2ChildCutoff R q)

/-- The weighted historical part of the nested finite-C decomposition. -/
def oai78NestedHistoricalColumn (R : ℕ) : ℂ :=
  ∑ q ∈ canonicalRoughLowQ2Owners R,
    (1 / (q : ℂ)) * mertensSummatory (oai78NestedDaughterRoot R q - 1)

/-- The weighted nested finite-C column, with the original reciprocal q weight. -/
def oai78NestedFiniteCColumn (R : ℕ) : ℂ :=
  ∑ q ∈ canonicalRoughLowQ2Owners R,
    (1 / (q : ℂ)) * oai78NestedFiniteC (oai78NestedDaughterRoot R q)

/-- Every literal q² daughter has the exact finite-C plus historical decomposition
    at its nearest completed-square root. -/
theorem oai78_nearest_daughter_eq_two_history_sub_finiteC (R q : ℕ) :
    lowOwnerNearestSquareMertensAmplitude R q =
      2 * mertensSummatory (oai78NestedDaughterRoot R q - 1) -
        oai78NestedFiniteC (oai78NestedDaughterRoot R q) := by
  unfold lowOwnerNearestSquareMertensAmplitude oai78NestedDaughterRoot
  rw [q2NearestSquareEndpoint_eq_rootEndpoint, mertensSummatoryInt_cast]
  unfold oai78NestedFiniteC
  ring

/-- Source-preserving reciprocal daughter transfer: all original prime
    labels and weights are kept, with no independent covariance hypothesis. -/
theorem oai78_nearest_column_eq_history_sub_nested_finiteC (R : ℕ) :
    lowOwnerNearestSquareReciprocalColumn R =
      2 * oai78NestedHistoricalColumn R - oai78NestedFiniteCColumn R := by
  unfold lowOwnerNearestSquareReciprocalColumn
    oai78NestedHistoricalColumn oai78NestedFiniteCColumn
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q _hq
  rw [oai78_nearest_daughter_eq_two_history_sub_finiteC]
  ring

/-- The same signed finite-C numerator at the ORIGINAL parent root. -/
theorem oai78_parent_finiteC_eq_rough_sub_history
    (R : ℕ) (hR : 2 ≤ R) :
    oai78NestedFiniteC R =
      squareRootCanonicalRoughCorrelation R + mertensSummatory (R - 1) := by
  unfold oai78NestedFiniteC
  rw [squareRootCanonicalRoughCorrelation_eq_mertens_pred_sub_endpoint R hR]
  ring

/-- Exact paid-boundary bridge. The three correction terms are
    (i) the parent historical Mertens value,
    (ii) the original 1/q historical daughter column,
    (iii) the ALREADY PROVED nearest-square signed shell.
    Nothing is dropped or bounded by an RH-equivalent hypothesis. -/
theorem oai78_corr4_physical_eq_nested_finiteC_add_boundary
    (R : ℕ) (hR : 56 ≤ R) :
    lowOwnerPhysicalAmplitudeRemainder R 0 =
      oai78NestedFiniteC R + oai78NestedFiniteCColumn R -
      mertensSummatory (R - 1) -
      2 * oai78NestedHistoricalColumn R -
      lowOwnerNearestSquareReciprocalShell R := by
  have hC :=
    squareRootCanonicalRoughCorrelation_eq_criticalSynthesis_add_physicalRemainder
      R hR 0
  rw [lowOwnerCriticalMertensSynthesis_zero_eq_reciprocalColumn R,
    lowOwnerReciprocalMertensColumn_eq_nearestSquare_add_shell R,
    oai78_nearest_column_eq_history_sub_nested_finiteC R] at hC
  have hP := oai78_parent_finiteC_eq_rough_sub_history R (by omega)
  rw [hP]
  linear_combination -hC

/-- The exact bridge immediately bounds the error by the three original,
    separately auditable historical and midpoint-shell quantities.
    A quantitative bound on these is NOT silently assumed. -/
theorem oai78_corr4_nested_finiteC_error_triangle
    (R : ℕ) (hR : 56 ≤ R) :
    ‖lowOwnerPhysicalAmplitudeRemainder R 0 -
       (oai78NestedFiniteC R + oai78NestedFiniteCColumn R)‖ ≤
      ‖mertensSummatory (R - 1)‖ +
      2 * ‖oai78NestedHistoricalColumn R‖ +
      ‖lowOwnerNearestSquareReciprocalShell R‖ := by
  rw [oai78_corr4_physical_eq_nested_finiteC_add_boundary R hR]
  have hmain :
    oai78NestedFiniteC R + oai78NestedFiniteCColumn R -
      mertensSummatory (R - 1) -
      2 * oai78NestedHistoricalColumn R -
      lowOwnerNearestSquareReciprocalShell R -
      (oai78NestedFiniteC R + oai78NestedFiniteCColumn R) =
      (-mertensSummatory (R - 1)) +
      (-(2 * oai78NestedHistoricalColumn R)) -
      lowOwnerNearestSquareReciprocalShell R := by ring
  rw [hmain]
  calc
    ‖(-mertensSummatory (R - 1)) +
      (-(2 * oai78NestedHistoricalColumn R)) -
      lowOwnerNearestSquareReciprocalShell R‖ ≤
      ‖(-mertensSummatory (R - 1)) +
          (-(2 * oai78NestedHistoricalColumn R))‖ +
      ‖lowOwnerNearestSquareReciprocalShell R‖ := norm_sub_le _ _
    _ ≤ ‖mertensSummatory (R - 1)‖ +
      ‖2 * oai78NestedHistoricalColumn R‖ +
      ‖lowOwnerNearestSquareReciprocalShell R‖ := by
        have h := norm_add_le (-mertensSummatory (R - 1))
          (-(2 * oai78NestedHistoricalColumn R))
        simp only [norm_neg] at h
        linarith
    _ = _ := by simp

#print axioms oai78_nearest_daughter_eq_two_history_sub_finiteC
#print axioms oai78_nearest_column_eq_history_sub_nested_finiteC
#print axioms oai78_corr4_physical_eq_nested_finiteC_add_boundary
#print axioms oai78_corr4_nested_finiteC_error_triangle

end RHLean.Proof
