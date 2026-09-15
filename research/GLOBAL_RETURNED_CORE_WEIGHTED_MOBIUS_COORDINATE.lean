import Mathlib
import «research.GLOBAL_RETURNED_CORE_CONTINUATION_CARRIER»

/-!
# One weighted Möbius coordinate for the zero-frequency AMP square

The decisive covariance step should square one amplitude, not a list of
bookkeeping packets.  This file begins that reindexing by collapsing the full
reciprocal q² daughter column onto the common physical Möbius clock.

For each site `n`, its coefficient is the sum of the reciprocal owner weights
`1/q` over precisely those low q² daughters whose cutoff still contains `n`.
The coefficient is nonnegative.  Thus the zero-frequency AMP remainder can be
viewed as one real weighted Möbius trajectory before the Gram expansion.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Real form of the literal reciprocal q² Mertens column. -/
def lowOwnerReciprocalMertensColumnReal (R : ℕ) : ℝ :=
  ∑ q ∈ canonicalRoughLowQ2Owners R,
    (1 / (q : ℝ)) * (mertensSummatoryInt (rawQ2ChildCutoff R q) : ℝ)

/-- Total reciprocal daughter weight seen by one physical Möbius site. -/
def lowOwnerReciprocalDaughterWeight (R n : ℕ) : ℝ :=
  ∑ q ∈ canonicalRoughLowQ2Owners R,
    if n ≤ rawQ2ChildCutoff R q then 1 / (q : ℝ) else 0

/-- Every reciprocal daughter coefficient is nonnegative. -/
theorem lowOwnerReciprocalDaughterWeight_nonneg (R n : ℕ) :
    0 ≤ lowOwnerReciprocalDaughterWeight R n := by
  unfold lowOwnerReciprocalDaughterWeight
  apply Finset.sum_nonneg
  intro q _hq
  split
  · positivity
  · norm_num

/-- The real reciprocal column is the same object as the complex AMP column. -/
theorem lowOwnerReciprocalMertensColumnReal_cast (R : ℕ) :
    (lowOwnerReciprocalMertensColumnReal R : ℂ) =
      lowOwnerReciprocalMertensColumn R := by
  unfold lowOwnerReciprocalMertensColumnReal lowOwnerReciprocalMertensColumn
    lowOwnerRawMertensAmplitude
  push_cast
  simp only [mertensSummatoryInt_cast]

/-- **Common-clock Fubini for the reciprocal q² daughters.**  Instead of one
Mertens prefix per owner, the entire reciprocal column is one weighted Möbius
amplitude on `1 <= n <= X_R`. -/
theorem lowOwnerReciprocalMertensColumnReal_eq_weightedMobiusSum (R : ℕ) :
    lowOwnerReciprocalMertensColumnReal R =
      ∑ n ∈ Finset.Icc 1 (squareRootEndpoint R),
        lowOwnerReciprocalDaughterWeight R n * realMoebiusStep n := by
  unfold lowOwnerReciprocalMertensColumnReal
  simp_rw [mertensSummatoryInt_eq_Icc]
  push_cast
  change
    (∑ q ∈ canonicalRoughLowQ2Owners R,
      (1 / (q : ℝ)) *
        (∑ n ∈ Finset.Icc 1 (rawQ2ChildCutoff R q), realMoebiusStep n)) = _
  calc
    (∑ q ∈ canonicalRoughLowQ2Owners R,
        (1 / (q : ℝ)) *
          (∑ n ∈ Finset.Icc 1 (rawQ2ChildCutoff R q), realMoebiusStep n)) =
      ∑ q ∈ canonicalRoughLowQ2Owners R,
        ∑ n ∈ Finset.Icc 1 (squareRootEndpoint R),
          if n ≤ rawQ2ChildCutoff R q then
            (1 / (q : ℝ)) * realMoebiusStep n else 0 := by
        apply Finset.sum_congr rfl
        intro q _hq
        rw [Finset.mul_sum]
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
        rw [← hset]
        exact Finset.sum_filter _ _
    _ = ∑ n ∈ Finset.Icc 1 (squareRootEndpoint R),
        ∑ q ∈ canonicalRoughLowQ2Owners R,
          if n ≤ rawQ2ChildCutoff R q then
            (1 / (q : ℝ)) * realMoebiusStep n else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ n ∈ Finset.Icc 1 (squareRootEndpoint R),
        lowOwnerReciprocalDaughterWeight R n * realMoebiusStep n := by
      apply Finset.sum_congr rfl
      intro n _hn
      unfold lowOwnerReciprocalDaughterWeight
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q _hq
      by_cases hq : n ≤ rawQ2ChildCutoff R q <;> simp [hq]

end RHLean.Proof
