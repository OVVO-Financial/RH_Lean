import Mathlib
import «research.STABLE_FAR_PERRON_BASEL_FRAME_SHARPENING»

/-!
# Composite-gap sharpening of the odd-prime reciprocal frame

The existing two-term rational Basel frame keeps the prime contributions at
`3` and `5` exact and telescopes over all odd integers from `7`.  Prime owners
cannot occupy the composite locations `9` and `15`; keeping
`3,5,7,11,13` exact and starting the tail at `17` therefore gives the
uniform constant `1565172113 / 7214407200`.

This is a finite arithmetic frame bound.  It does not supply the open signed
physical-remainder estimate in CORR-4.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- The odd reciprocal-square tail starting at `17` is at most `1/32`. -/
theorem sum_seventeenOddReciprocalSquares_le (N : ℕ) :
    (∑ k ∈ Finset.range N,
      (1 : ℚ) / ((2 * k + 17 : ℕ) : ℚ) ^ 2) ≤ (1 / 32 : ℚ) := by
  have hsub :
      (∑ k ∈ Finset.range N,
        (1 : ℚ) / ((2 * k + 17 : ℕ) : ℚ) ^ 2) ≤
        (1 / 32 : ℚ) - 1 / (4 * (((N : ℚ) + 8))) := by
    induction N with
    | zero => norm_num
    | succ N ih =>
        rw [Finset.sum_range_succ]
        have hterm := oddReciprocalSquareTerm_le_telescope (N + 7)
        calc
          (∑ k ∈ Finset.range N,
              (1 : ℚ) / ((2 * k + 17 : ℕ) : ℚ) ^ 2) +
              (1 : ℚ) / ((2 * N + 17 : ℕ) : ℚ) ^ 2 ≤
            ((1 / 32 : ℚ) - 1 / (4 * ((N : ℚ) + 8))) +
              (1 / (4 * ((N : ℚ) + 8)) -
                1 / (4 * ((N : ℚ) + 9))) := by
                  apply add_le_add ih
                  convert hterm using 1
                  all_goals push_cast
                  all_goals ring
          _ = (1 / 32 : ℚ) -
              1 / (4 * (((N.succ : ℕ) : ℚ) + 8)) := by
                push_cast
                ring
  have hnonneg : (0 : ℚ) ≤ 1 / (4 * ((N : ℚ) + 8)) := by positivity
  linarith

private theorem oddPrimesTail_subset_seventeenOddImage (N : ℕ) :
    ((primesUpTo N).erase 2).filter (fun q => 17 ≤ q) ⊆
      (Finset.range N).image (fun k : ℕ => 2 * k + 17) := by
  intro q hq
  have hbase := (Finset.mem_filter.mp hq).1
  have hq17 := (Finset.mem_filter.mp hq).2
  have hdata := mem_primesUpTo.mp (Finset.mem_erase.mp hbase).2
  have hne := (Finset.mem_erase.mp hbase).1
  obtain ⟨k, hk⟩ := hdata.1.odd_of_ne_two hne
  have hk8 : 8 ≤ k := by omega
  refine Finset.mem_image.mpr ⟨k - 8, Finset.mem_range.mpr ?_, ?_⟩
  · omega
  · omega

private theorem oddPrimesBelowSeventeen_subset (N : ℕ) :
    ((primesUpTo N).erase 2).filter (fun q => q < 17) ⊆
      ({3, 5, 7, 11, 13} : Finset ℕ) := by
  intro q hq
  have hbase := (Finset.mem_filter.mp hq).1
  have hq17 := (Finset.mem_filter.mp hq).2
  have hp := (mem_primesUpTo.mp (Finset.mem_erase.mp hbase).2).1
  have hne := (Finset.mem_erase.mp hbase).1
  interval_cases q <;> norm_num at *

/-- Exact `3,5,7,11,13` prime contributions plus the odd tail from `17`.
The missing odd locations `9` and `15` are excluded by primality. -/
theorem oddPrimeOwnerReciprocalSquareBudget_le_compositeGap (N : ℕ) :
    (∑ q ∈ (primesUpTo N).erase 2,
      (1 : ℚ) / (q : ℚ) ^ 2) ≤
        (1565172113 / 7214407200 : ℚ) := by
  let S := (primesUpTo N).erase 2
  let L := S.filter (fun q => q < 17)
  let H := S.filter (fun q => 17 ≤ q)
  have hdisj : Disjoint L H := by
    rw [Finset.disjoint_left]
    intro q hqL hqH
    have hlt := (Finset.mem_filter.mp hqL).2
    have hge := (Finset.mem_filter.mp hqH).2
    omega
  have hunion : L ∪ H = S := by
    ext q
    simp only [L, H, S, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hq, _⟩ | ⟨hq, _⟩) <;> exact hq
    · intro hq
      by_cases hlt : q < 17
      · exact Or.inl ⟨hq, hlt⟩
      · exact Or.inr ⟨hq, by omega⟩
  have hsmall :
      (∑ q ∈ L, (1 : ℚ) / (q : ℚ) ^ 2) ≤
        (1 / 9 + 1 / 25 + 1 / 49 + 1 / 121 + 1 / 169 : ℚ) := by
    have hsub : L ⊆ ({3, 5, 7, 11, 13} : Finset ℕ) := by
      simpa only [L, S] using oddPrimesBelowSeventeen_subset N
    calc
      _ ≤ ∑ q ∈ ({3, 5, 7, 11, 13} : Finset ℕ),
          (1 : ℚ) / (q : ℚ) ^ 2 := by
            apply Finset.sum_le_sum_of_subset_of_nonneg hsub
            intro q _ _
            positivity
      _ = (1 / 9 + 1 / 25 + 1 / 49 + 1 / 121 + 1 / 169 : ℚ) := by
        norm_num
  have hlarge :
      (∑ q ∈ H, (1 : ℚ) / (q : ℚ) ^ 2) ≤ (1 / 32 : ℚ) := by
    have hsub : H ⊆ (Finset.range N).image (fun k : ℕ => 2 * k + 17) := by
      simpa only [H, S] using oddPrimesTail_subset_seventeenOddImage N
    have hmono :
        (∑ q ∈ H, (1 : ℚ) / (q : ℚ) ^ 2) ≤
          ∑ q ∈ (Finset.range N).image (fun k : ℕ => 2 * k + 17),
            (1 : ℚ) / (q : ℚ) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro q _ _
      positivity
    rw [Finset.sum_image] at hmono
    · exact hmono.trans (sum_seventeenOddReciprocalSquares_le N)
    · intro a _ b _ hab
      have hmul : 2 * a = 2 * b := Nat.add_right_cancel hab
      omega
  change (∑ q ∈ S, (1 : ℚ) / (q : ℚ) ^ 2) ≤
    (1565172113 / 7214407200 : ℚ)
  rw [← hunion, Finset.sum_union hdisj]
  norm_num at hsmall hlarge ⊢
  linarith

/-- Real form of the composite-gap odd-prime reciprocal-square budget. -/
theorem oddPrimeOwnerReciprocalSquareBudgetReal_le_compositeGap (N : ℕ) :
    (∑ q ∈ (primesUpTo N).erase 2,
      (1 : ℝ) / (q : ℝ) ^ 2) ≤
        (1565172113 / 7214407200 : ℝ) := by
  have hQ := oddPrimeOwnerReciprocalSquareBudget_le_compositeGap N
  have hcast :
      (((∑ q ∈ (primesUpTo N).erase 2,
          (1 : ℚ) / (q : ℚ) ^ 2) : ℚ) : ℝ) ≤
        (((1565172113 / 7214407200 : ℚ)) : ℝ) := by
    exact_mod_cast hQ
  push_cast at hcast
  norm_num at hcast ⊢
  simpa [Nat.cast_pow] using! hcast

/-- The actual odd-prime Perron synthesis inherits the sharper frame. -/
theorem stableFarCriticalQ2OddPrimeSynthesis_energy_le_compositeGap
    (tau : ℝ) (N : ℕ) (a : ℕ → ℂ) :
    ‖stableFarCriticalQ2Synthesis tau ((primesUpTo N).erase 2) a‖ ^ 2 ≤
      (1565172113 / 7214407200 : ℝ) *
        ∑ q ∈ (primesUpTo N).erase 2, ‖a q‖ ^ 2 := by
  have hpos : ∀ q ∈ (primesUpTo N).erase 2, 0 < q := by
    intro q hq
    exact (mem_primesUpTo.mp (Finset.mem_erase.mp hq).2).1.pos
  have hframe :=
    stableFarCriticalQ2Synthesis_energy_le_reciprocalSquareBudget
      tau ((primesUpTo N).erase 2) a hpos
  have hbudget := oddPrimeOwnerReciprocalSquareBudgetReal_le_compositeGap N
  have henergy : 0 ≤ ∑ q ∈ (primesUpTo N).erase 2, ‖a q‖ ^ 2 := by
    positivity
  exact hframe.trans (mul_le_mul_of_nonneg_right hbudget henergy)

/-- The new constant is strictly smaller than the previous two-term budget. -/
theorem compositeGapBudget_lt_twoTermBasel :
    (1565172113 / 7214407200 : ℚ) < 211 / 900 := by
  norm_num

#print axioms oddPrimeOwnerReciprocalSquareBudget_le_compositeGap
#print axioms oddPrimeOwnerReciprocalSquareBudgetReal_le_compositeGap
#print axioms stableFarCriticalQ2OddPrimeSynthesis_energy_le_compositeGap

end RHLean.Proof
