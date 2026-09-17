import Mathlib
import «research.GLOBAL_RETURNED_CORE_INHERITED_DETERMINISTIC_CANCELLATION»
import «research.GLOBAL_RETURNED_CORE_DIAGONAL_BOUND»

/-!
# Root-scale L2 bound for one mixed owner coordinate

The pointwise estimate from the deterministic inherited-energy seam is summed on
the full positive physical clock.  Each threshold crossing is dominated by the
literal cutoff indicator `1_{n ≤ y}`; the transported crossing at `r*n` obeys
the same bound because `n ≤ r*n` for positive `r`.

The daughter activity is therefore paid exactly by the already-compiled q^2
cutoff census, while the root correction has only O(R) support.  No Mobius
cancellation, Mertens estimate, or logarithmic loss is used.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

private theorem lowOwnerThresholdCrossingIndicator_le_cutoffIndicator
    (p n y : ℕ) :
    lowOwnerThresholdCrossingIndicator p n y ≤
      if n ≤ y then (1 : ℝ) else 0 := by
  unfold lowOwnerThresholdCrossingIndicator
  by_cases hn : n ≤ y
  · simp [hn]
    by_cases hy : y < p * n <;> simp [hy]
  · simp [hn]

private theorem lowOwnerThresholdTransportedCrossingIndicator_le_cutoffIndicator
    {p r n y : ℕ} (hr : 0 < r) :
    lowOwnerThresholdCrossingIndicator p (r * n) y ≤
      if n ≤ y then (1 : ℝ) else 0 := by
  unfold lowOwnerThresholdCrossingIndicator
  by_cases hcross : r * n ≤ y ∧ y < p * (r * n)
  · have hnprod : n ≤ r * n := Nat.le_mul_of_pos_left n hr
    have hn : n ≤ y := hnprod.trans hcross.1
    simp [hcross, hn]
  · by_cases hn : n ≤ y <;> simp [hcross, hn]

private theorem sum_lowOwnerCutoffIndicator_eq_cast
    {X y : ℕ} (hy : y ≤ X) :
    (∑ n ∈ Finset.Icc 1 X,
      if n ≤ y then (1 : ℝ) else 0) = (y : ℝ) := by
  have hset :
      (Finset.Icc 1 X).filter (fun n => n ≤ y) = Finset.Icc 1 y := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [← Finset.sum_filter, hset]
  simp

/-- One ordinary threshold window has total mass at most its endpoint. -/
theorem sum_lowOwnerThresholdCrossingIndicator_le_cutoff
    {p X y : ℕ} (hy : y ≤ X) :
    (∑ n ∈ Finset.Icc 1 X,
      lowOwnerThresholdCrossingIndicator p n y) ≤ (y : ℝ) := by
  calc
    (∑ n ∈ Finset.Icc 1 X,
        lowOwnerThresholdCrossingIndicator p n y) ≤
      ∑ n ∈ Finset.Icc 1 X,
        if n ≤ y then (1 : ℝ) else 0 := by
          apply Finset.sum_le_sum
          intro n _hn
          exact lowOwnerThresholdCrossingIndicator_le_cutoffIndicator p n y
    _ = (y : ℝ) := sum_lowOwnerCutoffIndicator_eq_cast hy

/-- The transported `r*n` threshold window has the same endpoint bound. -/
theorem sum_lowOwnerThresholdTransportedCrossingIndicator_le_cutoff
    {p r X y : ℕ} (hr : 0 < r) (hy : y ≤ X) :
    (∑ n ∈ Finset.Icc 1 X,
      lowOwnerThresholdCrossingIndicator p (r * n) y) ≤ (y : ℝ) := by
  calc
    (∑ n ∈ Finset.Icc 1 X,
        lowOwnerThresholdCrossingIndicator p (r * n) y) ≤
      ∑ n ∈ Finset.Icc 1 X,
        if n ≤ y then (1 : ℝ) else 0 := by
          apply Finset.sum_le_sum
          intro n _hn
          exact
            lowOwnerThresholdTransportedCrossingIndicator_le_cutoffIndicator hr
    _ = (y : ℝ) := sum_lowOwnerCutoffIndicator_eq_cast hy

/-- **Daughter activity is root-scale.**  Summing the two disjoint mixed
threshold windows first in `n` costs at most twice each q^2 daughter cutoff;
the compiled cutoff census then gives one half of the parent endpoint. -/
theorem sum_lowOwnerThresholdDaughterActivity_le_half_endpoint
    (R p r : ℕ) (hr : 0 < r) :
    (∑ n ∈ Finset.Icc 1 (squareRootEndpoint R),
      ∑ q ∈ canonicalRoughLowQ2Owners R,
        (lowOwnerThresholdCrossingIndicator
            p n (rawQ2ChildCutoff R q) +
          lowOwnerThresholdCrossingIndicator
            p (r * n) (rawQ2ChildCutoff R q))) ≤
      (1 / 2 : ℝ) * (squareRootEndpoint R : ℝ) := by
  rw [Finset.sum_comm]
  have hterm : ∀ q ∈ canonicalRoughLowQ2Owners R,
      (∑ n ∈ Finset.Icc 1 (squareRootEndpoint R),
        (lowOwnerThresholdCrossingIndicator
            p n (rawQ2ChildCutoff R q) +
          lowOwnerThresholdCrossingIndicator
            p (r * n) (rawQ2ChildCutoff R q))) ≤
        2 * (rawQ2ChildCutoff R q : ℝ) := by
    intro q _hq
    have hY : rawQ2ChildCutoff R q ≤ squareRootEndpoint R := by
      unfold rawQ2ChildCutoff
      exact Nat.div_le_self _ _
    have hleft :=
      sum_lowOwnerThresholdCrossingIndicator_le_cutoff
        (p := p) (X := squareRootEndpoint R)
        (y := rawQ2ChildCutoff R q) hY
    have hright :=
      sum_lowOwnerThresholdTransportedCrossingIndicator_le_cutoff
        (p := p) (r := r) (X := squareRootEndpoint R)
        (y := rawQ2ChildCutoff R q) hr hY
    rw [Finset.sum_add_distrib]
    nlinarith
  calc
    (∑ q ∈ canonicalRoughLowQ2Owners R,
        ∑ n ∈ Finset.Icc 1 (squareRootEndpoint R),
          (lowOwnerThresholdCrossingIndicator
              p n (rawQ2ChildCutoff R q) +
            lowOwnerThresholdCrossingIndicator
              p (r * n) (rawQ2ChildCutoff R q))) ≤
      ∑ q ∈ canonicalRoughLowQ2Owners R,
        2 * (rawQ2ChildCutoff R q : ℝ) := by
          apply Finset.sum_le_sum
          intro q hq
          exact hterm q hq
    _ = 2 *
        (∑ q ∈ canonicalRoughLowQ2Owners R,
          (rawQ2ChildCutoff R q : ℝ)) := by
          rw [Finset.mul_sum]
    _ ≤ 2 * ((1 / 4 : ℝ) * (squareRootEndpoint R : ℝ)) := by
          exact mul_le_mul_of_nonneg_left
            (sum_lowOwnerRawQ2ChildCutoff_le_quarter_endpoint R) (by norm_num)
    _ = (1 / 2 : ℝ) * (squareRootEndpoint R : ℝ) := by ring

/-- The two root-crossing windows have only linear total support. -/
theorem sum_lowOwnerThresholdRootActivity_le_two_root
    {R p r : ℕ} (hR : 1 ≤ R) (hr : 0 < r) :
    (∑ n ∈ Finset.Icc 1 (squareRootEndpoint R),
      (lowOwnerThresholdCrossingIndicator p n (R - 1) +
        lowOwnerThresholdCrossingIndicator p (r * n) (R - 1))) ≤
      2 * ((R - 1 : ℕ) : ℝ) := by
  have hroot : R - 1 ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    have hsq : R ≤ R ^ 2 := by nlinarith
    omega
  have hleft :=
    sum_lowOwnerThresholdCrossingIndicator_le_cutoff
      (p := p) (X := squareRootEndpoint R) (y := R - 1) hroot
  have hright :=
    sum_lowOwnerThresholdTransportedCrossingIndicator_le_cutoff
      (p := p) (r := r) (X := squareRootEndpoint R) (y := R - 1)
      hr hroot
  rw [Finset.sum_add_distrib]
  nlinarith

/-- **Full-clock mixed-incidence L2 estimate.**  One fixed exterior owner pair
has square mass at most `X/4 + 4(R-1)` on the complete physical clock. -/
theorem sum_lowOwnerThresholdSecondOwnerDifference_sq_le_quarter_endpoint_add_four_root
    {R p r : ℕ}
    (hR : 1 ≤ R) (hp : p.Prime) (hr : r.Prime) (hpr : p < r) :
    (∑ n ∈ Finset.Icc 1 (squareRootEndpoint R),
      lowOwnerThresholdSecondOwnerDifference R p r n ^ 2) ≤
      (1 / 4 : ℝ) * (squareRootEndpoint R : ℝ) +
        4 * ((R - 1 : ℕ) : ℝ) := by
  let A : ℝ :=
    ∑ n ∈ Finset.Icc 1 (squareRootEndpoint R),
      ∑ q ∈ canonicalRoughLowQ2Owners R,
        (lowOwnerThresholdCrossingIndicator
            p n (rawQ2ChildCutoff R q) +
          lowOwnerThresholdCrossingIndicator
            p (r * n) (rawQ2ChildCutoff R q))
  let B : ℝ :=
    ∑ n ∈ Finset.Icc 1 (squareRootEndpoint R),
      (lowOwnerThresholdCrossingIndicator p n (R - 1) +
        lowOwnerThresholdCrossingIndicator p (r * n) (R - 1))
  have hA : A ≤ (1 / 2 : ℝ) * (squareRootEndpoint R : ℝ) := by
    simpa [A] using
      (sum_lowOwnerThresholdDaughterActivity_le_half_endpoint R p r hr.pos)
  have hB : B ≤ 2 * ((R - 1 : ℕ) : ℝ) := by
    simpa [B] using
      (sum_lowOwnerThresholdRootActivity_le_two_root hR hr.pos
        (p := p))
  have hsum :
      (∑ n ∈ Finset.Icc 1 (squareRootEndpoint R),
        lowOwnerThresholdSecondOwnerDifference R p r n ^ 2) ≤
        (1 / 2 : ℝ) * A + 2 * B := by
    calc
      (∑ n ∈ Finset.Icc 1 (squareRootEndpoint R),
          lowOwnerThresholdSecondOwnerDifference R p r n ^ 2) ≤
        ∑ n ∈ Finset.Icc 1 (squareRootEndpoint R),
          ((1 / 2 : ℝ) *
              (∑ q ∈ canonicalRoughLowQ2Owners R,
                (lowOwnerThresholdCrossingIndicator
                    p n (rawQ2ChildCutoff R q) +
                  lowOwnerThresholdCrossingIndicator
                    p (r * n) (rawQ2ChildCutoff R q))) +
            2 *
              (lowOwnerThresholdCrossingIndicator p n (R - 1) +
                lowOwnerThresholdCrossingIndicator
                  p (r * n) (R - 1))) := by
            apply Finset.sum_le_sum
            intro n hn
            exact lowOwnerThresholdSecondOwnerDifference_sq_le_activity
              hR hp hr hpr (Finset.mem_Icc.mp hn).1
      _ = (1 / 2 : ℝ) * A + 2 * B := by
        rw [Finset.sum_add_distrib]
        rw [← Finset.mul_sum, ← Finset.mul_sum]
        rfl
  calc
    (∑ n ∈ Finset.Icc 1 (squareRootEndpoint R),
        lowOwnerThresholdSecondOwnerDifference R p r n ^ 2) ≤
      (1 / 2 : ℝ) * A + 2 * B := hsum
    _ ≤ (1 / 2 : ℝ) *
          ((1 / 2 : ℝ) * (squareRootEndpoint R : ℝ)) +
        2 * (2 * ((R - 1 : ℕ) : ℝ)) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hA (by norm_num))
        (mul_le_mul_of_nonneg_left hB (by norm_num))
    _ = (1 / 4 : ℝ) * (squareRootEndpoint R : ℝ) +
        4 * ((R - 1 : ℕ) : ℝ) := by ring

/-- A loose root-square form convenient for downstream packing arguments. -/
theorem sum_lowOwnerThresholdSecondOwnerDifference_sq_le_five_root_sq
    {R p r : ℕ}
    (hR : 1 ≤ R) (hp : p.Prime) (hr : r.Prime) (hpr : p < r) :
    (∑ n ∈ Finset.Icc 1 (squareRootEndpoint R),
      lowOwnerThresholdSecondOwnerDifference R p r n ^ 2) ≤
      5 * (R : ℝ) ^ 2 := by
  have hmain :=
    sum_lowOwnerThresholdSecondOwnerDifference_sq_le_quarter_endpoint_add_four_root
      hR hp hr hpr
  have hX : (squareRootEndpoint R : ℝ) ≤ (R : ℝ) ^ 2 := by
    exact_mod_cast (Nat.sub_le (R ^ 2) 1)
  have hroot : (((R - 1 : ℕ) : ℝ)) ≤ (R : ℝ) := by
    exact_mod_cast (Nat.sub_le R 1)
  have hRreal : (1 : ℝ) ≤ R := by exact_mod_cast hR
  nlinarith

end RHLean.Proof
