import Mathlib
import «research.STABLE_FAR_PERRON_BASEL_FRAME_SHARPENING»
import «research.GLOBAL_RETURNED_CORE_INHERITED_DETERMINISTIC_CANCELLATION»

/-!
# Basel-sharpened threshold activity bound

The deterministic inherited-energy reduction already shows that each daughter
threshold contributes through a literal reciprocal coefficient `1/q`, and that
the square of each clipped second-difference atom is exactly a two-window
activity count.  Replacing the previous odd-prime `1/4` budget by the
Basel-style `211/900` budget therefore improves the daughter coefficient from
`1/2` to `211/450` after the final `(A-B)^2` split.

No new absolute value, Möbius estimate, or packetwise norm is introduced.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

private theorem lowOwnerInheritedReciprocalSquareBudget_le_twoTermBasel
    (R : ℕ) :
    (∑ q ∈ canonicalRoughLowQ2Owners R,
      ((1 : ℝ) / (q : ℝ)) ^ 2) ≤ (211 / 900 : ℝ) := by
  have hsub : canonicalRoughLowQ2Owners R ⊆ (primesUpTo (R - 1)).erase 2 :=
    Finset.sdiff_subset
  calc
    (∑ q ∈ canonicalRoughLowQ2Owners R,
        ((1 : ℝ) / (q : ℝ)) ^ 2) ≤
      ∑ q ∈ (primesUpTo (R - 1)).erase 2,
        ((1 : ℝ) / (q : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro q _hq _hnot
      positivity
    _ ≤ (211 / 900 : ℝ) := by
      simpa [div_pow] using
        (oddPrimeOwnerReciprocalSquareBudgetReal_le_twoTermBasel (R - 1))

/-- **Basel-budget daughter square.** -/
theorem lowOwnerThresholdDaughterClippedSum_sq_le_twoTermBasel_activity
    {R p r n : ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r) (hn : 0 < n) :
    (∑ q ∈ canonicalRoughLowQ2Owners R,
      ((1 : ℝ) / (q : ℝ)) *
        lowOwnerThresholdClippedDifference
          p r n (rawQ2ChildCutoff R q)) ^ 2 ≤
      (211 / 900 : ℝ) *
        ∑ q ∈ canonicalRoughLowQ2Owners R,
          (lowOwnerThresholdCrossingIndicator
              p n (rawQ2ChildCutoff R q) +
            lowOwnerThresholdCrossingIndicator
              p (r * n) (rawQ2ChildCutoff R q)) := by
  let S := canonicalRoughLowQ2Owners R
  let b : ℕ → ℝ := fun q =>
    lowOwnerThresholdClippedDifference p r n (rawQ2ChildCutoff R q)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (R := ℝ) S (fun q => (1 : ℝ) / (q : ℝ)) b
  have hbSq :
      (∑ q ∈ S, b q ^ 2) =
        ∑ q ∈ S,
          (lowOwnerThresholdCrossingIndicator
              p n (rawQ2ChildCutoff R q) +
            lowOwnerThresholdCrossingIndicator
              p (r * n) (rawQ2ChildCutoff R q)) := by
    apply Finset.sum_congr rfl
    intro q _hq
    unfold b
    rw [lowOwnerThresholdClippedDifference_eq_atomicMixedDifference
      hp.one_le hr.one_le]
    exact lowOwnerThresholdAtomicMixedDifference_sq_eq_activity hpr hn
  have hbudget :
      (∑ q ∈ S, ((1 : ℝ) / (q : ℝ)) ^ 2) ≤
        (211 / 900 : ℝ) := by
    exact lowOwnerInheritedReciprocalSquareBudget_le_twoTermBasel R
  have hbNonneg : 0 ≤ ∑ q ∈ S, b q ^ 2 := by
    apply Finset.sum_nonneg
    intro q _hq
    positivity
  calc
    (∑ q ∈ canonicalRoughLowQ2Owners R,
        ((1 : ℝ) / (q : ℝ)) *
          lowOwnerThresholdClippedDifference
            p r n (rawQ2ChildCutoff R q)) ^ 2 =
        (∑ q ∈ S, ((1 : ℝ) / (q : ℝ)) * b q) ^ 2 := by rfl
    _ ≤ (∑ q ∈ S, ((1 : ℝ) / (q : ℝ)) ^ 2) *
          ∑ q ∈ S, b q ^ 2 := hcs
    _ ≤ (211 / 900 : ℝ) * ∑ q ∈ S, b q ^ 2 :=
      mul_le_mul_of_nonneg_right hbudget hbNonneg
    _ = (211 / 900 : ℝ) *
        ∑ q ∈ canonicalRoughLowQ2Owners R,
          (lowOwnerThresholdCrossingIndicator
              p n (rawQ2ChildCutoff R q) +
            lowOwnerThresholdCrossingIndicator
              p (r * n) (rawQ2ChildCutoff R q)) := by
      rw [hbSq]

/-- **Basel-sharpened pointwise mixed-incidence square.**  The daughter
activity coefficient is `211/450 < 1/2`; the root boundary term is unchanged. -/
theorem lowOwnerThresholdSecondOwnerDifference_sq_le_twoTermBasel_activity
    {R p r n : ℕ}
    (hR : 1 ≤ R) (hp : p.Prime) (hr : r.Prime)
    (hpr : p < r) (hn : 0 < n) :
    lowOwnerThresholdSecondOwnerDifference R p r n ^ 2 ≤
      (211 / 450 : ℝ) *
        (∑ q ∈ canonicalRoughLowQ2Owners R,
          (lowOwnerThresholdCrossingIndicator
              p n (rawQ2ChildCutoff R q) +
            lowOwnerThresholdCrossingIndicator
              p (r * n) (rawQ2ChildCutoff R q))) +
      2 *
        (lowOwnerThresholdCrossingIndicator p n (R - 1) +
          lowOwnerThresholdCrossingIndicator p (r * n) (R - 1)) := by
  let A : ℝ :=
    ∑ q ∈ canonicalRoughLowQ2Owners R,
      ((1 : ℝ) / (q : ℝ)) *
        lowOwnerThresholdClippedDifference
          p r n (rawQ2ChildCutoff R q)
  let B : ℝ := lowOwnerThresholdClippedDifference p r n (R - 1)
  have hrewrite :
      lowOwnerThresholdSecondOwnerDifference R p r n = A - B := by
    simpa [A, B] using
      (lowOwnerThresholdSecondOwnerDifference_eq_clippedFubini
        hR hp.one_le hr.one_le)
  have hA : A ^ 2 ≤
      (211 / 900 : ℝ) *
        (∑ q ∈ canonicalRoughLowQ2Owners R,
          (lowOwnerThresholdCrossingIndicator
              p n (rawQ2ChildCutoff R q) +
            lowOwnerThresholdCrossingIndicator
              p (r * n) (rawQ2ChildCutoff R q))) := by
    simpa [A] using
      (lowOwnerThresholdDaughterClippedSum_sq_le_twoTermBasel_activity
        (R := R) hp hr hpr hn)
  have hB : B ^ 2 =
      lowOwnerThresholdCrossingIndicator p n (R - 1) +
        lowOwnerThresholdCrossingIndicator p (r * n) (R - 1) := by
    unfold B
    rw [lowOwnerThresholdClippedDifference_eq_atomicMixedDifference
      hp.one_le hr.one_le]
    exact lowOwnerThresholdAtomicMixedDifference_sq_eq_activity hpr hn
  rw [hrewrite]
  have hquad : (A - B) ^ 2 ≤ 2 * A ^ 2 + 2 * B ^ 2 := by
    nlinarith [sq_nonneg (A + B)]
  calc
    (A - B) ^ 2 ≤ 2 * A ^ 2 + 2 * B ^ 2 := hquad
    _ ≤ 2 * ((211 / 900 : ℝ) *
          (∑ q ∈ canonicalRoughLowQ2Owners R,
            (lowOwnerThresholdCrossingIndicator
                p n (rawQ2ChildCutoff R q) +
              lowOwnerThresholdCrossingIndicator
                p (r * n) (rawQ2ChildCutoff R q)))) +
        2 * B ^ 2 := by nlinarith [hA]
    _ = (211 / 450 : ℝ) *
          (∑ q ∈ canonicalRoughLowQ2Owners R,
            (lowOwnerThresholdCrossingIndicator
                p n (rawQ2ChildCutoff R q) +
              lowOwnerThresholdCrossingIndicator
                p (r * n) (rawQ2ChildCutoff R q))) +
        2 *
          (lowOwnerThresholdCrossingIndicator p n (R - 1) +
            lowOwnerThresholdCrossingIndicator p (r * n) (R - 1)) := by
      rw [hB]
      ring

/-- The improved daughter coefficient is strictly below the previous half. -/
theorem twoTermBasel_daughterCoefficient_lt_half :
    (211 / 450 : ℝ) < 1 / 2 := by
  norm_num

end RHLean.Proof
