import Mathlib
import «research.GLOBAL_RETURNED_CORE_FIRST_OWNER_GRAM»

/-!
# Elementary q² diagonal bound on the one-amplitude clock

The reciprocal daughter part of the final zero-frequency AMP weight has a
fixed root-scale diagonal.  Pointwise Cauchy--Schwarz uses the compiled
reciprocal-square owner budget; summing the active threshold indicators then
counts exactly the q² daughter cutoffs.  No Möbius cancellation is used.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

private theorem lowOwnerReciprocalSquareBudget_le_quarter (R : ℕ) :
    (∑ q ∈ canonicalRoughLowQ2Owners R, (1 : ℝ) / (q : ℝ) ^ 2) ≤ 1 / 4 := by
  have hsub : canonicalRoughLowQ2Owners R ⊆ (primesUpTo (R - 1)).erase 2 :=
    Finset.sdiff_subset
  calc
    (∑ q ∈ canonicalRoughLowQ2Owners R, (1 : ℝ) / (q : ℝ) ^ 2) ≤
        ∑ q ∈ (primesUpTo (R - 1)).erase 2, (1 : ℝ) / (q : ℝ) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro q _hq _hnot
      positivity
    _ ≤ 1 / 4 := oddPrimeOwnerReciprocalSquareBudgetReal_le_quarter (R - 1)

/-- Pointwise daughter weight is controlled by one quarter of the number of
active q² windows containing the site. -/
theorem lowOwnerReciprocalDaughterWeight_sq_le_quarter_activeCount
    (R n : ℕ) :
    lowOwnerReciprocalDaughterWeight R n ^ 2 ≤
      (1 / 4 : ℝ) *
        ∑ q ∈ canonicalRoughLowQ2Owners R,
          if n ≤ rawQ2ChildCutoff R q then 1 else 0 := by
  let S := canonicalRoughLowQ2Owners R
  let b : ℕ → ℝ := fun q => if n ≤ rawQ2ChildCutoff R q then 1 else 0
  have hrewrite :
      lowOwnerReciprocalDaughterWeight R n =
        ∑ q ∈ S, ((1 : ℝ) / (q : ℝ)) * b q := by
    unfold lowOwnerReciprocalDaughterWeight S b
    apply Finset.sum_congr rfl
    intro q _hq
    by_cases h : n ≤ rawQ2ChildCutoff R q <;> simp [h]
  rw [hrewrite]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (R := ℝ) S (fun q => (1 : ℝ) / (q : ℝ)) b
  have hbSq : (∑ q ∈ S, b q ^ 2) = ∑ q ∈ S, b q := by
    apply Finset.sum_congr rfl
    intro q _hq
    unfold b
    split <;> norm_num
  have hbudget :
      (∑ q ∈ S, ((1 : ℝ) / (q : ℝ)) ^ 2) ≤ 1 / 4 := by
    change (∑ q ∈ canonicalRoughLowQ2Owners R,
      ((1 : ℝ) / (q : ℝ)) ^ 2) ≤ 1 / 4
    have h := lowOwnerReciprocalSquareBudget_le_quarter R
    convert h using 1 <;> ring
  have hb0 : 0 ≤ ∑ q ∈ S, b q := by
    apply Finset.sum_nonneg
    intro q _hq
    unfold b
    split <;> norm_num
  calc
    (∑ q ∈ S, ((1 : ℝ) / (q : ℝ)) * b q) ^ 2 ≤
        (∑ q ∈ S, ((1 : ℝ) / (q : ℝ)) ^ 2) *
          ∑ q ∈ S, b q ^ 2 := hcs
    _ = (∑ q ∈ S, ((1 : ℝ) / (q : ℝ)) ^ 2) *
          ∑ q ∈ S, b q := by rw [hbSq]
    _ ≤ (1 / 4 : ℝ) * ∑ q ∈ S, b q :=
      mul_le_mul_of_nonneg_right hbudget hb0
    _ = (1 / 4 : ℝ) *
        ∑ q ∈ canonicalRoughLowQ2Owners R,
          if n ≤ rawQ2ChildCutoff R q then 1 else 0 := by rfl

/-- Summing active threshold indicators over the common positive clock counts
exactly one copy of every daughter cutoff. -/
theorem sum_lowOwnerActiveDaughterCount_eq_sum_cutoff (R : ℕ) :
    (∑ n ∈ Finset.Icc 1 (squareRootEndpoint R),
      ∑ q ∈ canonicalRoughLowQ2Owners R,
        if n ≤ rawQ2ChildCutoff R q then (1 : ℝ) else 0) =
      ∑ q ∈ canonicalRoughLowQ2Owners R,
        (rawQ2ChildCutoff R q : ℝ) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _hq
  have hY : rawQ2ChildCutoff R q ≤ squareRootEndpoint R := by
    unfold rawQ2ChildCutoff
    exact Nat.div_le_self _ _
  have hset :
      (Finset.Icc 1 (squareRootEndpoint R)).filter
          (fun n => n ≤ rawQ2ChildCutoff R q) =
        Finset.Icc 1 (rawQ2ChildCutoff R q) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [← Finset.sum_filter, hset]
  simp

/-- Total physical length of all low q² daughter windows is at most one quarter
of the parent endpoint. -/
theorem sum_lowOwnerRawQ2ChildCutoff_le_quarter_endpoint (R : ℕ) :
    (∑ q ∈ canonicalRoughLowQ2Owners R,
      (rawQ2ChildCutoff R q : ℝ)) ≤
      (1 / 4 : ℝ) * (squareRootEndpoint R : ℝ) := by
  have hterm : ∀ q ∈ canonicalRoughLowQ2Owners R,
      (rawQ2ChildCutoff R q : ℝ) ≤
        (squareRootEndpoint R : ℝ) * ((1 : ℝ) / (q : ℝ) ^ 2) := by
    intro q hq
    have hbase := (Finset.mem_sdiff.mp hq).1
    have hqPrime := (mem_primesUpTo.mp (Finset.mem_erase.mp hbase).2).1
    have hcast :
        ((squareRootEndpoint R / (q * q) : ℕ) : ℝ) ≤
          (squareRootEndpoint R : ℝ) / ((q * q : ℕ) : ℝ) := Nat.cast_div_le
    unfold rawQ2ChildCutoff
    calc
      ((squareRootEndpoint R / (q * q) : ℕ) : ℝ) ≤
          (squareRootEndpoint R : ℝ) / ((q * q : ℕ) : ℝ) := hcast
      _ = (squareRootEndpoint R : ℝ) * ((1 : ℝ) / (q : ℝ) ^ 2) := by
        push_cast
        field_simp [show (q : ℝ) ≠ 0 by exact_mod_cast hqPrime.ne_zero]
  calc
    (∑ q ∈ canonicalRoughLowQ2Owners R,
        (rawQ2ChildCutoff R q : ℝ)) ≤
      ∑ q ∈ canonicalRoughLowQ2Owners R,
        (squareRootEndpoint R : ℝ) * ((1 : ℝ) / (q : ℝ) ^ 2) := by
          apply Finset.sum_le_sum
          intro q hq
          exact hterm q hq
    _ = (squareRootEndpoint R : ℝ) *
        (∑ q ∈ canonicalRoughLowQ2Owners R, (1 : ℝ) / (q : ℝ) ^ 2) := by
          rw [Finset.mul_sum]
    _ ≤ (squareRootEndpoint R : ℝ) * (1 / 4 : ℝ) := by
      exact mul_le_mul_of_nonneg_left (lowOwnerReciprocalSquareBudget_le_quarter R)
        (by positivity)
    _ = (1 / 4 : ℝ) * (squareRootEndpoint R : ℝ) := by ring

/-- The reciprocal daughter coefficient itself has total square mass at most
one sixteenth of the endpoint. -/
theorem sum_lowOwnerReciprocalDaughterWeight_sq_le_sixteenth_endpoint (R : ℕ) :
    (∑ n ∈ Finset.Icc 1 (squareRootEndpoint R),
      lowOwnerReciprocalDaughterWeight R n ^ 2) ≤
      (1 / 16 : ℝ) * (squareRootEndpoint R : ℝ) := by
  calc
    (∑ n ∈ Finset.Icc 1 (squareRootEndpoint R),
        lowOwnerReciprocalDaughterWeight R n ^ 2) ≤
      ∑ n ∈ Finset.Icc 1 (squareRootEndpoint R),
        (1 / 4 : ℝ) *
          (∑ q ∈ canonicalRoughLowQ2Owners R,
            if n ≤ rawQ2ChildCutoff R q then (1 : ℝ) else 0) := by
          apply Finset.sum_le_sum
          intro n _hn
          exact lowOwnerReciprocalDaughterWeight_sq_le_quarter_activeCount R n
    _ = (1 / 4 : ℝ) *
        (∑ n ∈ Finset.Icc 1 (squareRootEndpoint R),
          ∑ q ∈ canonicalRoughLowQ2Owners R,
            if n ≤ rawQ2ChildCutoff R q then (1 : ℝ) else 0) := by
          rw [Finset.mul_sum]
    _ = (1 / 4 : ℝ) *
        (∑ q ∈ canonicalRoughLowQ2Owners R,
          (rawQ2ChildCutoff R q : ℝ)) := by
          rw [sum_lowOwnerActiveDaughterCount_eq_sum_cutoff]
    _ ≤ (1 / 4 : ℝ) * ((1 / 4 : ℝ) * (squareRootEndpoint R : ℝ)) := by
          exact mul_le_mul_of_nonneg_left
            (sum_lowOwnerRawQ2ChildCutoff_le_quarter_endpoint R) (by norm_num)
    _ = (1 / 16 : ℝ) * (squareRootEndpoint R : ℝ) := by ring

end RHLean.Proof
