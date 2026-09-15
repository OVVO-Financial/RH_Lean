import Mathlib
import «research.LOW_OWNER_RETURNED_AMPLITUDE_CORE»
import «research.LOW_OWNER_Q_MEMORY_REMAINDER_NORMAL_FORM»
import «research.ZERO_TARGET_PARTIAL_MOMENT_COVARIANCE»

/-!
# Returned-core square in global zero-target covariance currency

The zero-frequency AMP remainder has two exact non-root normal forms already in
`main`: the global returned core and the q-owner physical memory census.  This
file identifies them before squaring, then records the zero-target NNS
co-partial/divergent decomposition for an arbitrary finite Gram carrier.

The point is to make the next theorem purely a carrier theorem: once the q-owner
physical amplitude is expanded on its literal finite carrier, every pair can be
classified by first separation without introducing packetwise triangle bounds.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- The coupled returned core is exactly the negative q-owner physical memory
census.  Thus no four-packet Gram expansion is needed. -/
theorem lowOwnerReturnedAmplitudeCore_eq_neg_qMemoryCensus
    (R : ℕ) (hR : 56 ≤ R) :
    lowOwnerReturnedAmplitudeCore R = -lowOwnerPhysicalQMemoryCensus R := by
  unfold lowOwnerReturnedAmplitudeCore lowOwnerPhysicalQMemoryCensus
  rw [lowOwnerPhysicalFarCensus_eq_neg_globalReturnedReciprocal_sub_memory_sub_terminal
    R hR]
  ring

/-- Squaring the returned core is therefore literally the q-owner physical
memory energy. -/
theorem norm_sq_lowOwnerReturnedAmplitudeCore_eq_qMemoryCensus
    (R : ℕ) (hR : 56 ≤ R) :
    ‖lowOwnerReturnedAmplitudeCore R‖ ^ 2 =
      ‖lowOwnerPhysicalQMemoryCensus R‖ ^ 2 := by
  rw [lowOwnerReturnedAmplitudeCore_eq_neg_qMemoryCensus R hR]
  simp

/-- Same-sign zero-target mass on an arbitrary finite ordered Gram carrier. -/
def zeroTargetCoPartialGram
    {α : Type*} [DecidableEq α]
    (s : Finset α) (a : α → ℝ) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s, zeroTargetCoPartialPair (a i) (a j)

/-- Opposite-sign zero-target mass on an arbitrary finite ordered Gram carrier. -/
def zeroTargetDivergentGram
    {α : Type*} [DecidableEq α]
    (s : Finset α) (a : α → ℝ) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s, zeroTargetDivergentPair (a i) (a j)

/-- The full finite Gram is exactly co-partial minus divergent mass at target
zero.  This is the global form of the NNS identity, with no pairwise estimate. -/
theorem zeroTarget_globalGram_reassembly
    {α : Type*} [DecidableEq α]
    (s : Finset α) (a : α → ℝ) :
    (∑ i ∈ s, a i) ^ 2 =
      zeroTargetCoPartialGram s a - zeroTargetDivergentGram s a := by
  have hpair :
      (∑ i ∈ s, ∑ j ∈ s, a i * a j) =
        zeroTargetCoPartialGram s a - zeroTargetDivergentGram s a := by
    unfold zeroTargetCoPartialGram zeroTargetDivergentGram
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    exact (zeroTargetCoPartial_sub_divergent_eq_mul (a i) (a j)).symm
  calc
    (∑ i ∈ s, a i) ^ 2 =
        (∑ i ∈ s, a i) * (∑ j ∈ s, a j) := by ring
    _ = ∑ i ∈ s, a i * (∑ j ∈ s, a j) := by
      rw [Finset.sum_mul]
    _ = ∑ i ∈ s, ∑ j ∈ s, a i * a j := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
    _ = zeroTargetCoPartialGram s a - zeroTargetDivergentGram s a := hpair

/-- A carrier-level domination of positive zero-target leakage immediately
bounds the full Gram.  The decisive remaining theorem will instantiate `B` by
the clipped first-separation energy. -/
theorem zeroTarget_globalGram_le_of_coPartial_sub_divergent_le
    {α : Type*} [DecidableEq α]
    (s : Finset α) (a : α → ℝ) (B : ℝ)
    (hB : zeroTargetCoPartialGram s a - zeroTargetDivergentGram s a ≤ B) :
    (∑ i ∈ s, a i) ^ 2 ≤ B := by
  rw [zeroTarget_globalGram_reassembly]
  exact hB

end RHLean.Proof
