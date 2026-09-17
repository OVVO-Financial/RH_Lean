import Mathlib
import RHLean.Proof.SquareRootLowPrimeSharpFrameBudget
import «research.STABLE_FAR_PERRON_QUARTER_FRAME_BOUND»

/-!
# Basel-style sharpening of the odd-prime reciprocal frame

The classical Basel series explains why reciprocal-square coefficients are the
natural energy currency here.  For the Lean proof we keep the argument finite
and rational: the existing odd-number telescope is exact enough to retain the
first two terms `1/3^2` and `1/5^2` instead of paying their coarser telescope
allowances.

This gives the uniform finite bound

  sum_{q odd prime <= N} 1/q^2 <= 211/900 < 1/4.

The constant is slightly weaker than the full odd-integer Basel value
`pi^2/8 - 1`, but it is kernel-friendly, elementary, and already improves every
forward reciprocal-square frame or daughter-scale estimate without importing a
new analytic theorem about `pi`.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Retain the exact `3` and `5` contributions, then telescope from `7` onward.
The endpoint term is kept explicit for induction. -/
theorem sum_oddReciprocalSquares_le_twoTermBasel_sub (N : ℕ) :
    (∑ k ∈ Finset.range (N + 2),
      (1 : ℚ) / ((2 * k + 3 : ℕ) : ℚ) ^ 2) ≤
      (211 / 900 : ℚ) -
        1 / (4 * ((((N + 2 : ℕ) : ℚ)) + 1)) := by
  induction N with
  | zero =>
      norm_num [Finset.sum_range_succ]
  | succ N ih =>
      rw [show N.succ + 2 = (N + 2) + 1 by omega, Finset.sum_range_succ]
      calc
        (∑ k ∈ Finset.range (N + 2),
            (1 : ℚ) / ((2 * k + 3 : ℕ) : ℚ) ^ 2) +
            (1 : ℚ) / ((2 * (N + 2) + 3 : ℕ) : ℚ) ^ 2 ≤
          ((211 / 900 : ℚ) -
            1 / (4 * ((((N + 2 : ℕ) : ℚ)) + 1))) +
            (1 / (4 * ((((N + 2 : ℕ) : ℚ)) + 1)) -
              1 / (4 * ((((N + 2 : ℕ) : ℚ)) + 2))) :=
          add_le_add ih (oddReciprocalSquareTerm_le_telescope (N + 2))
        _ = (211 / 900 : ℚ) -
            1 / (4 * ((((N.succ + 2 : ℕ) : ℚ)) + 1)) := by
          push_cast
          ring

/-- Uniform finite odd-square budget obtained from the two exact initial terms
and the remaining telescope. -/
theorem sum_oddReciprocalSquares_le_twoTermBasel (N : ℕ) :
    (∑ k ∈ Finset.range N,
      (1 : ℚ) / ((2 * k + 3 : ℕ) : ℚ) ^ 2) ≤
      (211 / 900 : ℚ) := by
  by_cases hN : N < 2
  · interval_cases N <;> norm_num [Finset.sum_range_succ]
  · have hEq : N = (N - 2) + 2 := by omega
    rw [hEq]
    have h := sum_oddReciprocalSquares_le_twoTermBasel_sub (N - 2)
    have htail :
        (0 : ℚ) ≤
          1 / (4 * (((((N - 2) + 2 : ℕ) : ℚ)) + 1)) := by
      positivity
    linarith

private theorem oddPrimes_subset_baselOddImage (N : ℕ) :
    (primesUpTo N).erase 2 ⊆
      (Finset.range N).image (fun k : ℕ => (2 * k + 3 : ℕ)) := by
  intro q hq
  have hdata := mem_primesUpTo.mp (Finset.mem_erase.mp hq).2
  have hqN := hdata.2
  have hq2 := hdata.1.two_le
  have hne := (Finset.mem_erase.mp hq).1
  obtain ⟨k, hk⟩ := hdata.1.odd_of_ne_two hne
  have hk1 : 1 ≤ k := by omega
  refine Finset.mem_image.mpr ⟨k - 1, Finset.mem_range.mpr (by omega), ?_⟩
  omega

/-- Basel-style rational sharpening of the actual odd-prime owner budget. -/
theorem oddPrimeOwnerReciprocalSquareBudget_le_twoTermBasel (N : ℕ) :
    (∑ q ∈ (primesUpTo N).erase 2,
      (1 : ℚ) / (q : ℚ) ^ 2) ≤
      (211 / 900 : ℚ) := by
  have hsum :
      (∑ q ∈ (primesUpTo N).erase 2,
          (1 : ℚ) / (q : ℚ) ^ 2) ≤
        ∑ q ∈ (Finset.range N).image (fun k : ℕ => (2 * k + 3 : ℕ)),
          (1 : ℚ) / (q : ℚ) ^ 2 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (oddPrimes_subset_baselOddImage N) ?_
    intro q _hqImage _hqOld
    positivity
  rw [Finset.sum_image] at hsum
  · exact hsum.trans (sum_oddReciprocalSquares_le_twoTermBasel N)
  · intro a _ha b _hb hab
    have hmul : 2 * a = 2 * b := Nat.add_right_cancel hab
    omega

/-- The sharpened coefficient is strictly below the previous quarter budget. -/
theorem twoTermBaselBudget_lt_quarter :
    (211 / 900 : ℚ) < 1 / 4 := by
  norm_num

/-- Real form of the sharpened odd-prime reciprocal-square budget. -/
theorem oddPrimeOwnerReciprocalSquareBudgetReal_le_twoTermBasel (N : ℕ) :
    (∑ q ∈ (primesUpTo N).erase 2,
      (1 : ℝ) / (q : ℝ) ^ 2) ≤
      (211 / 900 : ℝ) := by
  have hQ := oddPrimeOwnerReciprocalSquareBudget_le_twoTermBasel N
  have hcast :
      (((∑ q ∈ (primesUpTo N).erase 2,
          (1 : ℚ) / (q : ℚ) ^ 2) : ℚ) : ℝ) ≤
        (((211 / 900 : ℚ)) : ℝ) := by
    exact_mod_cast hQ
  push_cast at hcast
  norm_num at hcast ⊢
  simpa [Nat.cast_pow] using hcast

/-- The Perron forward frame inherits the same improved reciprocal-square
coefficient. -/
theorem stableFarCriticalQ2OddPrimeSynthesis_energy_le_twoTermBasel
    (tau : ℝ) (N : ℕ) (a : ℕ → ℂ) :
    ‖stableFarCriticalQ2Synthesis tau ((primesUpTo N).erase 2) a‖ ^ 2 ≤
      (211 / 900 : ℝ) *
        ∑ q ∈ (primesUpTo N).erase 2, ‖a q‖ ^ 2 := by
  have hpos : ∀ q ∈ (primesUpTo N).erase 2, 0 < q := by
    intro q hq
    exact (mem_primesUpTo.mp (Finset.mem_erase.mp hq).2).1.pos
  have hframe :=
    stableFarCriticalQ2Synthesis_energy_le_reciprocalSquareBudget
      tau ((primesUpTo N).erase 2) a hpos
  have hbudget := oddPrimeOwnerReciprocalSquareBudgetReal_le_twoTermBasel N
  have henergy :
      0 ≤ ∑ q ∈ (primesUpTo N).erase 2, ‖a q‖ ^ 2 := by
    positivity
  calc
    ‖stableFarCriticalQ2Synthesis tau ((primesUpTo N).erase 2) a‖ ^ 2 ≤
        (∑ q ∈ (primesUpTo N).erase 2,
          (1 : ℝ) / (q : ℝ) ^ 2) *
          ∑ q ∈ (primesUpTo N).erase 2, ‖a q‖ ^ 2 := hframe
    _ ≤ (211 / 900 : ℝ) *
          ∑ q ∈ (primesUpTo N).erase 2, ‖a q‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hbudget henergy

/-- The same sharpened budget in literal q²-daughter cutoff units. -/
theorem sum_oddPrimeOwner_squareDilatedCutoffs_le_twoTermBasel_parent
    (N X : ℕ) :
    (∑ q ∈ (primesUpTo N).erase 2,
      ((X / (q * q) : ℕ) : ℚ)) ≤
      (211 / 900 : ℚ) * (X : ℚ) := by
  have hcut :=
    sum_squareDilatedCutoffs_le_scale_mul_budget
      ((primesUpTo N).erase 2) X
      (fun q hq => (mem_primesUpTo.mp (Finset.mem_erase.mp hq).2).1)
  have hbudget :=
    mul_le_mul_of_nonneg_left
      (oddPrimeOwnerReciprocalSquareBudget_le_twoTermBasel N)
      (by positivity : (0 : ℚ) ≤ (X : ℚ))
  calc
    (∑ q ∈ (primesUpTo N).erase 2,
        ((X / (q * q) : ℕ) : ℚ)) ≤
      (X : ℚ) *
        ∑ q ∈ (primesUpTo N).erase 2,
          (1 : ℚ) / (q : ℚ) ^ 2 := hcut
    _ ≤ (X : ℚ) * (211 / 900 : ℚ) := hbudget
    _ = (211 / 900 : ℚ) * (X : ℚ) := by ring

end RHLean.Proof
