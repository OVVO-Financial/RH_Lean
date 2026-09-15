import Mathlib
import «research.GLOBAL_RETURNED_CORE_FIRST_OWNER_GRAM»

/-!
# Elementary root-scale bound for the one-amplitude diagonal

After the whole zero-frequency AMP correction is placed on one physical Mobius
clock, its diagonal is not an RH-scale obstruction.  The reciprocal daughter
weight at one site is a critical q^2 synthesis of 0/1 threshold indicators.
Pointwise Cauchy--Schwarz gives the quarter owner budget; summing the active
indicators counts exactly the daughter cutoffs, whose total is again controlled
by the reciprocal-square prime budget.

No signed cancellation is used in this file.
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
active q^2 windows containing the site. -/
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
  have hbSq :
      (∑ q ∈ S, b q ^ 2) = ∑ q ∈ S, b q := by
    apply Finset.sum_congr rfl
    intro q _hq
    unfold b
    split <;> norm_num
  have hbudget :
      (∑ q ∈ S, ((1 : ℝ) / (q : ℝ)) ^ 2) ≤ 1 / 4 := by
    change (∑ q ∈ canonicalRoughLowQ2Owners R,
      ((1 : ℝ) / (q : ℝ)) ^ 2) ≤ 1 / 4
    have h := lowOwnerReciprocalSquareBudget_le_quarter R
    simpa only [div_pow] using h
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

/-- Summing active threshold indicators over the common clock counts exactly
one copy of each daughter cutoff. -/
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
  calc
    (∑ n ∈ Finset.Icc 1 (squareRootEndpoint R),
        if n ≤ rawQ2ChildCutoff R q then (1 : ℝ) else 0) =
      ∑ n ∈ (Finset.Icc 1 (squareRootEndpoint R)).filter
          (fun n => n ≤ rawQ2ChildCutoff R q), (1 : ℝ) := by
        symm
        exact Finset.sum_filter _ _
    _ = ∑ _n ∈ Finset.Icc 1 (rawQ2ChildCutoff R q), (1 : ℝ) := by rw [hset]
    _ = (rawQ2ChildCutoff R q : ℝ) := by simp

/-- Total physical length of all low q^2 daughter windows is at most one quarter
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

/-- The full reciprocal daughter coefficient has linear total square mass. -/
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

/-- The complete common-clock diagonal is bounded by a fixed multiple of the
endpoint.  This deliberately uses the loose constant `4`; the exact preceding
bounds are substantially stronger. -/
theorem lowOwnerZeroFrequencyMobiusDiagonal_le_four_endpoint (R : ℕ) :
    lowOwnerZeroFrequencyMobiusDiagonal R ≤
      4 * (squareRootEndpoint R : ℝ) := by
  unfold lowOwnerZeroFrequencyMobiusDiagonal signedBlockEnergy
  have hsite : ∀ n ∈ Finset.range (squareRootEndpoint R + 1),
      lowOwnerZeroFrequencyMobiusSite R n ^ 2 ≤
        2 * lowOwnerFarTailWeight R n ^ 2 +
          2 * lowOwnerReciprocalDaughterWeight R n ^ 2 := by
    intro n _hn
    have hmu := realMoebiusStep_sq_le_one n
    have hw0 := lowOwnerZeroFrequencyMobiusWeight_nonneg R n
    have htail0 : 0 ≤ lowOwnerFarTailWeight R n := by
      unfold lowOwnerFarTailWeight
      split <;> norm_num
    have hd0 := lowOwnerReciprocalDaughterWeight_nonneg R n
    unfold lowOwnerZeroFrequencyMobiusSite lowOwnerZeroFrequencyMobiusWeight
    have hwsq :
        (lowOwnerFarTailWeight R n + lowOwnerReciprocalDaughterWeight R n) ^ 2 *
            realMoebiusStep n ^ 2 ≤
          (lowOwnerFarTailWeight R n + lowOwnerReciprocalDaughterWeight R n) ^ 2 :=
      mul_le_mul_of_nonneg_left hmu (sq_nonneg _)
    nlinarith [sq_nonneg
      (lowOwnerFarTailWeight R n - lowOwnerReciprocalDaughterWeight R n)]
  calc
    (∑ n ∈ Finset.range (squareRootEndpoint R + 1),
        lowOwnerZeroFrequencyMobiusSite R n ^ 2) ≤
      ∑ n ∈ Finset.range (squareRootEndpoint R + 1),
        (2 * lowOwnerFarTailWeight R n ^ 2 +
          2 * lowOwnerReciprocalDaughterWeight R n ^ 2) :=
        Finset.sum_le_sum hsite
    _ = 2 * (∑ n ∈ Finset.range (squareRootEndpoint R + 1),
          lowOwnerFarTailWeight R n ^ 2) +
        2 * (∑ n ∈ Finset.range (squareRootEndpoint R + 1),
          lowOwnerReciprocalDaughterWeight R n ^ 2) := by
          rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ 2 * (squareRootEndpoint R : ℝ) +
        2 * ((1 / 16 : ℝ) * (squareRootEndpoint R : ℝ)) := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ (by norm_num)
        calc
          (∑ n ∈ Finset.range (squareRootEndpoint R + 1),
              lowOwnerFarTailWeight R n ^ 2) ≤
            ∑ _n ∈ Finset.range (squareRootEndpoint R + 1), (1 : ℝ) := by
              apply Finset.sum_le_sum
              intro n _hn
              unfold lowOwnerFarTailWeight
              split <;> norm_num
          _ = ((squareRootEndpoint R + 1 : ℕ) : ℝ) := by simp
          _ ≤ (squareRootEndpoint R : ℝ) + 1 := by norm_num
          _ ≤ 2 * (squareRootEndpoint R : ℝ) := by
            by_cases hX : squareRootEndpoint R = 0
            · subst hX
              norm_num
            · have hX1 : (1 : ℝ) ≤ (squareRootEndpoint R : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hX
              linarith
      · apply mul_le_mul_of_nonneg_left _ (by norm_num)
        have hzero : lowOwnerReciprocalDaughterWeight R 0 = 0 := by
          unfold lowOwnerReciprocalDaughterWeight
          apply Finset.sum_eq_zero
          intro q _hq
          simp [rawQ2ChildCutoff]
        have hsplit :
            (∑ n ∈ Finset.range (squareRootEndpoint R + 1),
              lowOwnerReciprocalDaughterWeight R n ^ 2) =
            ∑ n ∈ Finset.Icc 1 (squareRootEndpoint R),
              lowOwnerReciprocalDaughterWeight R n ^ 2 := by
          have hset :
              Finset.range (squareRootEndpoint R + 1) =
                insert 0 (Finset.Icc 1 (squareRootEndpoint R)) := by
            ext n
            simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
            omega
          rw [hset, Finset.sum_insert]
          · rw [hzero]
            simp
          · simp
        rw [hsplit]
        exact sum_lowOwnerReciprocalDaughterWeight_sq_le_sixteenth_endpoint R
    _ ≤ 4 * (squareRootEndpoint R : ℝ) := by
      nlinarith [show 0 ≤ (squareRootEndpoint R : ℝ) by positivity]

/-- At the square endpoint this is a root-scale diagonal. -/
theorem lowOwnerZeroFrequencyMobiusDiagonal_le_four_root_sq
    (R : ℕ) :
    lowOwnerZeroFrequencyMobiusDiagonal R ≤ 4 * (R : ℝ) ^ 2 := by
  have h := lowOwnerZeroFrequencyMobiusDiagonal_le_four_endpoint R
  have hX : (squareRootEndpoint R : ℝ) ≤ (R : ℝ) ^ 2 := by
    unfold squareRootEndpoint
    push_cast
    nlinarith [show (0 : ℝ) ≤ (R : ℝ) by positivity]
  nlinarith

end RHLean.Proof
