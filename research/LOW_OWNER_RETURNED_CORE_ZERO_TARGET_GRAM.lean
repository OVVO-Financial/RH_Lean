import Mathlib
import «research.LOW_OWNER_RETURNED_AMPLITUDE_CORE»
import «research.LOW_OWNER_Q_MEMORY_REMAINDER_NORMAL_FORM»
import «research.ZERO_TARGET_PARTIAL_MOMENT_COVARIANCE»
import «research.ZERO_TARGET_CRITICAL_CLIPPED_EDGE_BOUNDARY_SPLIT»

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
    intro i _hi
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    exact (zeroTargetCoPartial_sub_divergent_eq_mul (a i) (a j)).symm
  calc
    (∑ i ∈ s, a i) ^ 2 =
        (∑ i ∈ s, a i) * (∑ j ∈ s, a j) := by ring
    _ = ∑ i ∈ s, a i * (∑ j ∈ s, a j) := by
      rw [Finset.sum_mul]
    _ = ∑ i ∈ s, ∑ j ∈ s, a i * a j := by
      apply Finset.sum_congr rfl
      intro i _hi
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

/-- **Finite first-separation induction.**  Any property that holds on the
terminal owner class and propagates from the stripped ordered parent to a
recursive child holds on every nonzero pair in the physical remainder carrier.
This rules out an infinite unnamed cross-owner population: every such chain
terminates because the fresh-prime separation rank drops by exactly one. -/
theorem postRootCovariancePhysicalPair_induction
    (W : ℕ) (P : ℕ × ℕ → Prop)
    (hterminal : ∀ {mn : ℕ × ℕ},
      mn ∈ postRootCovarianceRemainderTerminalPairCarrier W →
      realMoebiusStep mn.1 * realMoebiusStep mn.2 ≠ 0 → P mn)
    (hstep : ∀ {mn : ℕ × ℕ},
      mn ∈ postRootCovarianceRemainderRecursivePairCarrier W →
      realMoebiusStep mn.1 * realMoebiusStep mn.2 ≠ 0 →
      P (squarefreePairFreshPrimeOrderedParent mn.1 mn.2) → P mn) :
    ∀ {mn : ℕ × ℕ},
      mn ∈ postRootCovarianceRemainderPhysicalPairCarrier W →
      realMoebiusStep mn.1 * realMoebiusStep mn.2 ≠ 0 → P mn := by
  let rank : ℕ × ℕ → ℕ := fun mn =>
    (squarefreePairFreshPrimeSet mn.1 mn.2).card
  have hstrong : ∀ k : ℕ, ∀ {mn : ℕ × ℕ},
      rank mn = k →
      mn ∈ postRootCovarianceRemainderPhysicalPairCarrier W →
      realMoebiusStep mn.1 * realMoebiusStep mn.2 ≠ 0 → P mn := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro mn hrank hphys hweight
        by_cases ht : SquarefreePairFreshPrimeParentsEqual mn
        · exact hterminal (Finset.mem_filter.mpr ⟨hphys, ht⟩) hweight
        · have hrec : mn ∈ postRootCovarianceRemainderRecursivePairCarrier W :=
            Finset.mem_filter.mpr ⟨hphys, ht⟩
          let parent := squarefreePairFreshPrimeOrderedParent mn.1 mn.2
          have hdesc :=
            postRootCovarianceRemainderRecursivePair_owner_descent hrec hweight
          dsimp only at hdesc
          have hparentWeight :
              realMoebiusStep parent.1 * realMoebiusStep parent.2 ≠ 0 := by
            intro hz
            apply hweight
            rw [hdesc.2.2.2, hz, neg_zero]
          have hparentRankLt : rank parent < k := by
            dsimp [rank, parent]
            dsimp [rank] at hrank
            rw [← hrank]
            omega
          have hparentP : P parent :=
            ih (rank parent) hparentRankLt rfl hdesc.1 hparentWeight
          exact hstep hrec hweight hparentP
  intro mn hphys hweight
  exact hstrong (rank mn) rfl hphys hweight

/-- **First admitted-wall critical split.**  Once the stripped owner parent is
inside the LCM wall, the complete part has a negative coefficient and the only
positive geometric leakage is the companion-clipped first-separation term.
Parents still beyond the LCM wall are intentionally excluded here: they are the
recursive branch that must be telescoped by the rank-dropping owner descent. -/
theorem criticalPhysicalMellinStencil_firstAdmittedWall_eq_negative_add_clipped
    {W p a b : ℕ}
    (hp : p.Prime) (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b)
    (hab : a ≤ b) (hbW : b ≤ W) (hpaW : p * a ≤ W)
    (hlcmW : Nat.lcm a b ≤ W) :
    physicalSuperLcmMellinStencil W p (1 / (p : ℝ)) a b =
      -((1 / (p : ℝ)) * (2 - 1 / (p : ℝ))) *
          (if W < p * Nat.lcm a b then 1 else 0) +
        (1 / (p : ℝ)) * (1 - 1 / (p : ℝ)) *
          (if W < p * Nat.lcm a b ∧ W < p * b then 1 else 0) := by
  rw [physicalSuperLcmMellinStencil_eq_neg_firstCrossing_add_edge_of_mul_le
    (1 / (p : ℝ)) hp hpa hpb hab hbW hpaW]
  rw [critical_one_sub_mul_edge_eq_quadratic_add_reciprocalBoundary
    hp hpa hpb hab hbW hpaW]
  by_cases hwall : W < p * Nat.lcm a b
  · simp [hlcmW, hpaW, hwall]
    ring
  · simp [hwall]

end RHLean.Proof
