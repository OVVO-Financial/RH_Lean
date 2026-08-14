import Mathlib
import RHLean.Analysis.NativePNTLogSums
import RHLean.Analysis.NativePNTEvolvingTailState

/-!
# Structural obstruction for the absolute evolving-tail state

The current evolving-tail state self-composes a nonnegative one-log remainder
profile.  Its canonical first remainder contains the absolute factorial defect
centered at `N log N`, hence carries a linear floor.  Self-composition then
multiplies that floor by `log N`.

This file records the obstruction before any further arithmetic attack.  The
important point is stronger than a lower bound on the second remainder alone:
after the exact tail/small reciprocal partition is used, the non-remainder
terms in `nativePNTEvolvingTailCost` can cancel at most
`alpha * N * log(N)^2`.  Therefore the full current positive-cost state keeps
an `N log N` floor throughout polynomial scales.
-/

noncomputable section

open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

/-- The canonical first absolute remainder contains a linear factorial floor.
The sharp centering `log(N!) = N log N - N + 1 + O(log N)` makes the loss
explicit. -/
theorem nativePNTFirstRemainder_ge_linear_sub_log
    (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) - 1 - Real.log (N : ℝ) ≤ nativePNTFirstRemainder N := by
  have hfac := nativeLogFactorial_sub_main_abs_le N hN
  have hfacUpper :
      Real.log ((Nat.factorial N : ℕ) : ℝ) -
          ((N : ℝ) * Real.log (N : ℝ) - (N : ℝ) + 1) ≤
        Real.log (N : ℝ) :=
    (abs_le.mp hfac).2
  have hneg :
      (N : ℝ) - 1 - Real.log (N : ℝ) ≤
        -(Real.log ((Nat.factorial N : ℕ) : ℝ) -
          (N : ℝ) * Real.log (N : ℝ)) := by
    linarith
  calc
    (N : ℝ) - 1 - Real.log (N : ℝ) ≤
        -(Real.log ((Nat.factorial N : ℕ) : ℝ) -
          (N : ℝ) * Real.log (N : ℝ)) := hneg
    _ ≤ |Real.log ((Nat.factorial N : ℕ) : ℝ) -
          (N : ℝ) * Real.log (N : ℝ)| := neg_le_abs _
    _ ≤ |nativeSelbergPair N - 2 * (N : ℝ) * Real.log (N : ℝ)| +
          |Real.log ((Nat.factorial N : ℕ) : ℝ) -
            (N : ℝ) * Real.log (N : ℝ)| :=
      le_add_of_nonneg_left (abs_nonneg _)
    _ = nativePNTFirstRemainder N := by
      rfl

/-- The canonical first remainder is nonnegative at every endpoint. -/
theorem nativePNTFirstRemainder_nonneg (N : ℕ) :
    0 ≤ nativePNTFirstRemainder N := by
  unfold nativePNTFirstRemainder
  positivity

/-- The first von-Mangoldt absolute error mass is nonnegative. -/
theorem nativeLambdaErrorMass_nonneg (N : ℕ) :
    0 ≤ nativeLambdaErrorMass N := by
  unfold nativeLambdaErrorMass
  apply Finset.sum_nonneg
  intro d _hd
  exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (abs_nonneg _)

/-- Pushing the canonical first remainder through reciprocal von-Mangoldt
fibres preserves nonnegativity. -/
theorem nativeLambdaRemainderMass_first_nonneg (N : ℕ) :
    0 ≤ nativeLambdaRemainderMass nativePNTFirstRemainder N := by
  unfold nativeLambdaRemainderMass
  apply Finset.sum_nonneg
  intro d _hd
  exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (nativePNTFirstRemainder_nonneg (N / d))

/-- The canonical second remainder contains the endpoint first remainder times
`log N` as an explicit summand. -/
theorem nativePNTSecondRemainder_ge_first_mul_log (N : ℕ) :
    nativePNTFirstRemainder N * Real.log (N : ℝ) ≤
      nativePNTSecondRemainder N := by
  have hE := nativeLambdaErrorMass_nonneg N
  have hR := nativeLambdaRemainderMass_first_nonneg N
  simp only [nativePNTSecondRemainder, nativePNTSecondRemainderFrom]
  linarith

/-- Consequently the second absolute remainder has an explicit `N log N`
scale floor. -/
theorem nativePNTSecondRemainder_ge_linear_log_floor
    (N : ℕ) (hN : 1 ≤ N) :
    ((N : ℝ) - 1 - Real.log (N : ℝ)) * Real.log (N : ℝ) ≤
      nativePNTSecondRemainder N := by
  have hfirst := nativePNTFirstRemainder_ge_linear_sub_log N hN
  have hlog0 : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN)
  have hmul := mul_le_mul_of_nonneg_right hfirst hlog0
  exact hmul.trans (nativePNTSecondRemainder_ge_first_mul_log N)

/-- Reciprocal `Lambda_2` mass on the contracted tail is nonnegative. -/
theorem nativeLambdaTwoTailRecipMass_nonneg (N M : ℕ) :
    0 ≤ nativeLambdaTwoTailRecipMass N M := by
  unfold nativeLambdaTwoTailRecipMass
  apply Finset.sum_nonneg
  intro n hn
  have hn' :
      n ∈ (Finset.Icc 1 N).filter (fun n => M ≤ N / n) := by
    simpa [nativePNTSquarePrefixTailFiberSet] using hn
  have hnI : n ∈ Finset.Icc 1 N := (Finset.mem_filter.mp hn').1
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hnI).1
  exact div_nonneg (nativeLambdaTwo_nonneg n hn1) (by positivity)

/-- The exact small-quotient error mass is nonnegative before the tail-slope
subtraction is applied. -/
theorem nativeLambdaTwoSmallQuotientErrorMass_nonneg (N M : ℕ) :
    0 ≤ nativeLambdaTwoSmallQuotientErrorMass N M := by
  unfold nativeLambdaTwoSmallQuotientErrorMass
  apply Finset.sum_nonneg
  intro n hn
  have hn' :
      n ∈ (Finset.Icc 1 N).filter (fun n => N / n < M) := by
    simpa [nativePNTSquarePrefixSmallQuotientFiberSet] using hn
  have hnI : n ∈ Finset.Icc 1 N := (Finset.mem_filter.mp hn').1
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hnI).1
  exact mul_nonneg (nativeLambdaTwo_nonneg n hn1) (abs_nonneg _)

/-- **Full structural obstruction.**  In the canonical positive remainder
state, the exact tail/small partition cancels the small reciprocal mass between
the kernel defect and small-quotient excess.  What can remain negative outside
the second remainder is therefore only `alpha * N * log(N)^2`.

This is the useful obstruction theorem: it applies to the whole evolving cost,
not merely to one of its summands. -/
theorem nativePNTEvolvingTailCost_ge_canonical_obstruction
    (N M : ℕ) (alpha : ℝ)
    (hN : 1 ≤ N) (halpha : 0 ≤ alpha) :
    ((N : ℝ) - 1 - Real.log (N : ℝ)) * Real.log (N : ℝ) -
        alpha * (N : ℝ) * (Real.log (N : ℝ)) ^ 2 ≤
      nativePNTEvolvingTailCost nativePNTFirstRemainder N M alpha := by
  have hsecond := nativePNTSecondRemainder_ge_linear_log_floor N hN
  have hsecond' :
      ((N : ℝ) - 1 - Real.log (N : ℝ)) * Real.log (N : ℝ) ≤
        nativePNTSecondRemainderFrom nativePNTFirstRemainder N := by
    simpa [nativePNTSecondRemainder] using hsecond
  have htail := nativeLambdaTwoTailRecipMass_nonneg N M
  have hsmall := nativeLambdaTwoSmallQuotientErrorMass_nonneg N M
  have halphaN : 0 ≤ alpha * (N : ℝ) :=
    mul_nonneg halpha (by positivity)
  have htailTerm :
      0 ≤ alpha * (N : ℝ) * nativeLambdaTwoTailRecipMass N M :=
    mul_nonneg halphaN htail
  have hsplit := nativeLambdaTwoTailRecipMass_add_small_eq N M
  unfold nativePNTEvolvingTailCost nativePNTSmallQuotientExcess
    nativeLambdaTwoRecipDefect
  rw [← hsplit]
  nlinarith

/-- A convenient positive form of the obstruction.  Once `N` is beyond its
logarithmic lower-order terms and `alpha * log N` is small, the current
positive-cost state is bounded below by a fixed fraction of `N log N`. -/
theorem nativePNTEvolvingTailCost_ge_quarter_linear_log
    (N M : ℕ) (alpha : ℝ)
    (hN : 1 ≤ N) (halpha : 0 ≤ alpha)
    (hsize : 2 * (1 + Real.log (N : ℝ)) ≤ (N : ℝ))
    (hscale : 4 * alpha * Real.log (N : ℝ) ≤ 1) :
    (1 / 4 : ℝ) * (N : ℝ) * Real.log (N : ℝ) ≤
      nativePNTEvolvingTailCost nativePNTFirstRemainder N M alpha := by
  have hlog0 : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN)
  have hlinear :
      (N : ℝ) / 2 ≤ (N : ℝ) - 1 - Real.log (N : ℝ) := by
    linarith
  have hmain := mul_le_mul_of_nonneg_right hlinear hlog0
  have hscale' : alpha * Real.log (N : ℝ) ≤ (1 / 4 : ℝ) := by
    nlinarith
  have hNL0 : 0 ≤ (N : ℝ) * Real.log (N : ℝ) :=
    mul_nonneg (by positivity) hlog0
  have hpenalty0 := mul_le_mul_of_nonneg_right hscale' hNL0
  have hpenalty :
      alpha * (N : ℝ) * (Real.log (N : ℝ)) ^ 2 ≤
        (1 / 4 : ℝ) * (N : ℝ) * Real.log (N : ℝ) := by
    nlinarith [hpenalty0]
  have hcost :=
    nativePNTEvolvingTailCost_ge_canonical_obstruction N M alpha hN halpha
  nlinarith

/-- In the same regime, any proposed cubic cost budget whose coefficient still
satisfies `4*c*alpha^3*log N <= 1` is already no larger than the unavoidable
positive cost.  Thus the present absolute state cannot supply such a cubic net
gain by constant tuning. -/
theorem nativePNTEvolvingTailCost_ge_cubic_budget
    (N M : ℕ) (alpha c : ℝ)
    (hN : 1 ≤ N) (halpha : 0 ≤ alpha) (hc : 0 ≤ c)
    (hsize : 2 * (1 + Real.log (N : ℝ)) ≤ (N : ℝ))
    (hscale : 4 * alpha * Real.log (N : ℝ) ≤ 1)
    (hcubic : 4 * c * alpha ^ 3 * Real.log (N : ℝ) ≤ 1) :
    c * alpha ^ 3 * (N : ℝ) * (Real.log (N : ℝ)) ^ 2 ≤
      nativePNTEvolvingTailCost nativePNTFirstRemainder N M alpha := by
  have hlog0 : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN)
  have hquarter :=
    nativePNTEvolvingTailCost_ge_quarter_linear_log
      N M alpha hN halpha hsize hscale
  have hcubic' :
      c * alpha ^ 3 * Real.log (N : ℝ) ≤ (1 / 4 : ℝ) := by
    nlinarith
  have hNL0 : 0 ≤ (N : ℝ) * Real.log (N : ℝ) :=
    mul_nonneg (by positivity) hlog0
  have hmul := mul_le_mul_of_nonneg_right hcubic' hNL0
  have hbudget :
      c * alpha ^ 3 * (N : ℝ) * (Real.log (N : ℝ)) ^ 2 ≤
        (1 / 4 : ℝ) * (N : ℝ) * Real.log (N : ℝ) := by
    nlinarith [hmul]
  exact hbudget.trans hquarter

end RHLean.Analysis
