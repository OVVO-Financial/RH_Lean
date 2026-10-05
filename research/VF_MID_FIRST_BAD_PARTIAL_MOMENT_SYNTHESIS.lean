import Mathlib
import «research.VF_MID_GLOBAL_FIRST_BAD_RADIAL_BUDGET»
import «research.LOW_OWNER_RETURNED_CORE_ZERO_TARGET_GRAM»

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

attribute [local instance] Classical.propDecidable

def vfMidAnchoredZeroTargetCoPartialGram
    {α : Type*} [DecidableEq α]
    (s : Finset α) (a : α → ℝ) (D : ℝ) : ℝ :=
  zeroTargetCoPartialGram s a +
    2 * (∑ i ∈ s, zeroTargetCoPartialPair (-D) (a i)) +
    D ^ 2

def vfMidAnchoredZeroTargetDivergentGram
    {α : Type*} [DecidableEq α]
    (s : Finset α) (a : α → ℝ) (D : ℝ) : ℝ :=
  zeroTargetDivergentGram s a +
    2 * (∑ i ∈ s, zeroTargetDivergentPair (-D) (a i))

theorem vfMidAnchoredZeroTarget_crossExcess_eq
    {α : Type*} [DecidableEq α]
    (s : Finset α) (a : α → ℝ) (D : ℝ) :
    (∑ i ∈ s, zeroTargetCoPartialPair (-D) (a i)) -
        (∑ i ∈ s, zeroTargetDivergentPair (-D) (a i)) =
      -D * (∑ i ∈ s, a i) := by
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ i ∈ s,
      (zeroTargetCoPartialPair (-D) (a i) -
        zeroTargetDivergentPair (-D) (a i))) =
      ∑ i ∈ s, ((-D) * a i) := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact zeroTargetCoPartial_sub_divergent_eq_mul (-D) (a i)
    _ = -D * (∑ i ∈ s, a i) := by
      rw [Finset.mul_sum]

theorem vfMidAnchoredZeroTarget_excess_eq_sub_sq
    {α : Type*} [DecidableEq α]
    (s : Finset α) (a : α → ℝ) (D : ℝ) :
    vfMidAnchoredZeroTargetCoPartialGram s a D -
        vfMidAnchoredZeroTargetDivergentGram s a D =
      ((∑ i ∈ s, a i) - D) ^ 2 := by
  have hgram := zeroTarget_globalGram_reassembly s a
  have hcross := vfMidAnchoredZeroTarget_crossExcess_eq s a D
  unfold vfMidAnchoredZeroTargetCoPartialGram
    vfMidAnchoredZeroTargetDivergentGram
  nlinarith

theorem vfMid_sourceAffineBill_eq_anchoredPartialExcess_sub_anchorSq
    {α : Type*} [DecidableEq α]
    (s : Finset α) (a : α → ℝ) (D : ℝ) :
    (∑ i ∈ s, a i) ^ 2 -
        2 * D * (∑ i ∈ s, a i) =
      (vfMidAnchoredZeroTargetCoPartialGram s a D -
        vfMidAnchoredZeroTargetDivergentGram s a D) - D ^ 2 := by
  rw [vfMidAnchoredZeroTarget_excess_eq_sub_sq]
  ring

theorem vfMid_sourceAffineBill_le_radialBudget_iff_anchoredPartialExcess
    {α : Type*} [DecidableEq α]
    (s : Finset α) (a : α → ℝ) (D W : ℝ) :
    ((∑ i ∈ s, a i) ^ 2 -
        2 * D * (∑ i ∈ s, a i) ≤
      W ^ 2 - D ^ 2) ↔
    (vfMidAnchoredZeroTargetCoPartialGram s a D -
        vfMidAnchoredZeroTargetDivergentGram s a D ≤
      W ^ 2) := by
  rw [vfMid_sourceAffineBill_eq_anchoredPartialExcess_sub_anchorSq]
  constructor <;> intro h <;> linarith

end RHLean.Analysis
