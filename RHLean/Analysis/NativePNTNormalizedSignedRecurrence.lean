import Mathlib
import RHLean.Analysis.NativePNTErdosContraction

/-!
# Scale-free normalized signed Selberg recurrence

The affine-envelope proof globalizes a tail bound by inserting an additive
intercept.  That is convenient for proving the qualitative PNT, but it hides
the physical scale at which a small normalized error becomes valid.

This module instead divides the exact signed first Selberg recurrence by the
current endpoint.  The resulting remainder is an absolute constant, not a
term growing like `N` or `N * log N`.  This is the normalization needed for a
quantitative modulus attack and for later square-stage or wheel-frontier
smoothing.

No new analytic premise is introduced here.
-/

noncomputable section

open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

/-- Normalized Chebyshev error `E(N) / N`.  The value at zero is harmless and
is never used by the positive-endpoint theorems below. -/
def nativePNTNormalizedError (N : ℕ) : ℝ :=
  nativePNTError N / (N : ℝ)

/-- The signed reciprocal-floor Selberg transform after division by the
current endpoint `N`. -/
def nativePNTNormalizedFloorSelbergMass (N : ℕ) : ℝ :=
  (∑ d ∈ Finset.Icc 1 N, Λ d * nativePNTError (N / d)) / (N : ℝ)

/-- Explicit scale-free constant inherited from the signed first Selberg
recurrence. -/
def nativePNTNormalizedSelbergConstant : ℝ :=
  3 * (Real.log 4 + 2) + 173

/-- On positive endpoints, normalized error is exactly `psi(N) / N - 1`. -/
theorem nativePNTNormalizedError_eq_psi_div_sub_one
    (N : ℕ) (hN : 1 ≤ N) :
    nativePNTNormalizedError N = nativePsi N / (N : ℝ) - 1 := by
  have hNne : (N : ℝ) ≠ 0 := by
    exact_mod_cast (show N ≠ 0 by omega)
  unfold nativePNTNormalizedError nativePNTError
  field_simp [hNne]

/-- The elementary Chebyshev estimate gives a uniform bound for the normalized
error.  This is used later to control the tiny floor-to-reciprocal correction
without introducing an affine intercept. -/
theorem nativePNTNormalizedError_abs_le_const
    (N : ℕ) (hN : 1 ≤ N) :
    |nativePNTNormalizedError N| ≤ Real.log 4 + 3 := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have h := nativePNTError_abs_le_const_mul N
  unfold nativePNTNormalizedError
  rw [abs_div, abs_of_pos hNpos]
  apply (div_le_iff₀ hNpos).2
  simpa [mul_assoc] using h

/-- **Scale-free normalized signed Selberg recurrence.**

For every `N >= 3`,

`| e(N) log N + N^(-1) * sum_{d<=N} Lambda(d) E(floor(N/d)) | <= C`,

where `e(N) = E(N)/N` and `C` is an absolute explicit constant.  The crucial
point is that the right side no longer grows with `N`: the linear signed
Selberg remainder disappears after normalization rather than being propagated
as an affine intercept. -/
theorem nativePNTNormalized_signed_first_recurrence_abs_le
    (N : ℕ) (hN : 3 ≤ N) :
    |nativePNTNormalizedError N * Real.log (N : ℝ) +
        nativePNTNormalizedFloorSelbergMass N| ≤
      nativePNTNormalizedSelbergConstant := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have hsigned := nativePNTError_signed_log_sum_abs_le N hN
  have hrearrange :
      nativePNTNormalizedError N * Real.log (N : ℝ) +
          nativePNTNormalizedFloorSelbergMass N =
        (nativePNTError N * Real.log (N : ℝ) +
          ∑ d ∈ Finset.Icc 1 N,
            Λ d * nativePNTError (N / d)) / (N : ℝ) := by
    unfold nativePNTNormalizedError nativePNTNormalizedFloorSelbergMass
    ring
  rw [hrearrange, abs_div, abs_of_pos hNpos]
  apply (div_le_iff₀ hNpos).2
  simpa [nativePNTNormalizedSelbergConstant] using hsigned

end RHLean.Analysis
