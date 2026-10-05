import Mathlib
import «research.VF_MID_FRACTIONAL_INCIDENCE_CAPACITY»
import «research.GLOBAL_RETURNED_CORE_ZERO_TARGET_GEOMETRIC_TREE_BUDGET»
import «research.ZERO_TARGET_MELLIN_COMPLETE_POST_ROOT_CUBES»

/-!
# VF final signed-rank contraction: all-depth clipped capacity

After #890 the active completed gate packet has entered legal reciprocal
currency with an exact capacity fraction.  The remaining positive outlet of the
signed greatest-owner continuation is the companion-clipped exit.

This file sums that positive outlet through the entire finite descendant tree.
The existing chronology-preserving reciprocal tree costs at most twice its root
energy, while every clipped outlet costs at most one quarter of the local parent
energy.  Hence all clipped exits at all descendant depths cost at most one half
of the selected root reciprocal energy.

Complete post-root critical Mellin families are recorded separately as
nonpositive.  Thus no cardinality fraction, packet-to-full-scale inheritance,
triangle inequality on a signed packet, or new analytic hypothesis enters.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Retained-coefficient clipped outgoing energy at one parent, after the
incidence gate has legally entered reciprocal currency. -/
def vfMidRetainedAboveFirstClippedOutgoingEnergy
    (R first : ℕ) (parent : ℕ × ℕ) (coefficient : ℝ) : ℝ :=
  coefficient ^ 2 *
    lowOwnerGreatestOwnerAboveFirstClippedOutgoingEnergy R first parent

/-- One retained-coefficient clipped outlet costs at most one quarter of its
local reciprocal parent energy. -/
theorem vfMidRetainedAboveFirstClippedOutgoingEnergy_le_quarter
    {R first : ℕ} (hfirst : first.Prime)
    (parent : ℕ × ℕ) (coefficient : ℝ) :
    vfMidRetainedAboveFirstClippedOutgoingEnergy
        R first parent coefficient ≤
      (1 / 4 : ℝ) *
        lowOwnerRetainedCoefficientParentEnergy coefficient parent := by
  have hclip :=
    lowOwnerGreatestOwnerAboveFirstClippedOutgoingEnergy_le_quarter
      (R := R) hfirst parent
  unfold vfMidRetainedAboveFirstClippedOutgoingEnergy
  rw [lowOwnerRetainedCoefficientParentEnergy_eq_coefficient_sq_mul]
  calc
    coefficient ^ 2 *
        lowOwnerGreatestOwnerAboveFirstClippedOutgoingEnergy
          R first parent ≤
      coefficient ^ 2 *
        ((1 / 4 : ℝ) * postRootCovarianceReciprocalPairEnergy parent) :=
      mul_le_mul_of_nonneg_left hclip (sq_nonneg coefficient)
    _ = (1 / 4 : ℝ) *
        (coefficient ^ 2 * postRootCovarianceReciprocalPairEnergy parent) := by
      ring

/-- All clipped outlets in a finite descendant tree.  The coefficient is
retained exactly on every descendant, matching the existing reciprocal tree
currency. -/
def vfMidRetainedAboveFirstClippedExitTreeEnergy
    (R first depth : ℕ) (parent : ℕ × ℕ) (coefficient : ℝ) : ℝ :=
  match depth with
  | 0 => 0
  | d + 1 =>
      vfMidRetainedAboveFirstClippedOutgoingEnergy
        R first parent coefficient +
        ∑ r ∈ lowOwnerRevealedPrimesAbove R first,
          ∑ child ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent r,
            vfMidRetainedAboveFirstClippedExitTreeEnergy
              R first d child coefficient

@[simp] theorem vfMidRetainedAboveFirstClippedExitTreeEnergy_nonneg
    (R first depth : ℕ) (parent : ℕ × ℕ) (coefficient : ℝ) :
    0 ≤ vfMidRetainedAboveFirstClippedExitTreeEnergy
      R first depth parent coefficient := by
  induction depth generalizing parent with
  | zero =>
      simp [vfMidRetainedAboveFirstClippedExitTreeEnergy]
  | succ d ih =>
      simp only [vfMidRetainedAboveFirstClippedExitTreeEnergy]
      apply add_nonneg
      · unfold vfMidRetainedAboveFirstClippedOutgoingEnergy
        exact mul_nonneg (sq_nonneg coefficient)
          (by
            unfold lowOwnerGreatestOwnerAboveFirstClippedOutgoingEnergy
            apply Finset.sum_nonneg
            intro r _hr
            split
            · apply Finset.sum_nonneg
              intro child _hchild
              exact postRootCovarianceReciprocalPairEnergy_nonneg child
            · norm_num)
      · apply Finset.sum_nonneg
        intro r _hr
        apply Finset.sum_nonneg
        intro child _hchild
        exact ih child

/-- **All-depth local clipped budget.**

At every finite depth, all clipped exits below one reciprocal parent cost at
most one quarter of the corresponding retained-coefficient tree energy. -/
theorem vfMidRetainedAboveFirstClippedExitTreeEnergy_le_quarter_tree
    {R first : ℕ} (hfirst : first.Prime)
    (depth : ℕ) (parent : ℕ × ℕ) (coefficient : ℝ) :
    vfMidRetainedAboveFirstClippedExitTreeEnergy
        R first depth parent coefficient ≤
      (1 / 4 : ℝ) *
        lowOwnerRetainedCoefficientAboveFirstTreeEnergy
          R first depth parent coefficient := by
  induction depth generalizing parent with
  | zero =>
      simp [vfMidRetainedAboveFirstClippedExitTreeEnergy,
        lowOwnerRetainedCoefficientAboveFirstTreeEnergy]
  | succ d ih =>
      have hroot :=
        vfMidRetainedAboveFirstClippedOutgoingEnergy_le_quarter
          hfirst parent coefficient
      have hchildren :
          (∑ r ∈ lowOwnerRevealedPrimesAbove R first,
            ∑ child ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent r,
              vfMidRetainedAboveFirstClippedExitTreeEnergy
                R first d child coefficient) ≤
            (1 / 4 : ℝ) *
              (∑ r ∈ lowOwnerRevealedPrimesAbove R first,
                ∑ child ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent r,
                  lowOwnerRetainedCoefficientAboveFirstTreeEnergy
                    R first d child coefficient) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro r _hr
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro child _hchild
        exact ih child
      simp only [vfMidRetainedAboveFirstClippedExitTreeEnergy,
        lowOwnerRetainedCoefficientAboveFirstTreeEnergy]
      calc
        vfMidRetainedAboveFirstClippedOutgoingEnergy
              R first parent coefficient +
            (∑ r ∈ lowOwnerRevealedPrimesAbove R first,
              ∑ child ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent r,
                vfMidRetainedAboveFirstClippedExitTreeEnergy
                  R first d child coefficient) ≤
          (1 / 4 : ℝ) *
              lowOwnerRetainedCoefficientParentEnergy coefficient parent +
            (1 / 4 : ℝ) *
              (∑ r ∈ lowOwnerRevealedPrimesAbove R first,
                ∑ child ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent r,
                  lowOwnerRetainedCoefficientAboveFirstTreeEnergy
                    R first d child coefficient) :=
          add_le_add hroot hchildren
        _ = (1 / 4 : ℝ) *
            (lowOwnerRetainedCoefficientParentEnergy coefficient parent +
              ∑ r ∈ lowOwnerRevealedPrimesAbove R first,
                ∑ child ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent r,
                  lowOwnerRetainedCoefficientAboveFirstTreeEnergy
                    R first d child coefficient) := by
          ring

/-- **Uniform all-depth clipped contraction.**

Combining the preceding quarter-outlet estimate with the existing factor-two
bound on the entire legal later-owner reciprocal tree gives a depth-independent
one-half bound on every clipped exit below the root parent. -/
theorem vfMidRetainedAboveFirstClippedExitTreeEnergy_le_half_parent
    {R first : ℕ} (hfirst : first.Prime)
    (depth : ℕ) (parent : ℕ × ℕ) (coefficient : ℝ) :
    vfMidRetainedAboveFirstClippedExitTreeEnergy
        R first depth parent coefficient ≤
      (1 / 2 : ℝ) *
        lowOwnerRetainedCoefficientParentEnergy coefficient parent := by
  have hexit :=
    vfMidRetainedAboveFirstClippedExitTreeEnergy_le_quarter_tree
      hfirst depth parent coefficient
  have htree :=
    lowOwnerRetainedCoefficientAboveFirstTreeEnergy_le_two
      hfirst depth parent coefficient
  have hscale : (0 : ℝ) ≤ 1 / 4 := by norm_num
  calc
    vfMidRetainedAboveFirstClippedExitTreeEnergy
        R first depth parent coefficient ≤
      (1 / 4 : ℝ) *
        lowOwnerRetainedCoefficientAboveFirstTreeEnergy
          R first depth parent coefficient := hexit
    _ ≤ (1 / 4 : ℝ) *
        (2 * lowOwnerRetainedCoefficientParentEnergy coefficient parent) :=
      mul_le_mul_of_nonneg_left htree hscale
    _ = (1 / 2 : ℝ) *
        lowOwnerRetainedCoefficientParentEnergy coefficient parent := by
      ring

/-- Selected all-depth clipped-exit energy below the literal active completed
gate parents from #890. -/
def vfMidCompletedGateSelectedClippedExitTreeEnergy
    (R p : ℕ) (sig : Finset ℕ) (r depth : ℕ) : ℝ :=
  ∑ parent ∈
      lowOwnerFirstOwnerActiveCompletedPolarizationRawParentSet R p sig r,
    vfMidRetainedAboveFirstClippedExitTreeEnergy
      R r depth parent (lowOwnerThresholdEulerPairCoefficient R p r parent)

/-- The entire selected clipped descendant tree costs at most one half of the
exact selected reciprocal parent capacity. -/
theorem vfMidCompletedGateSelectedClippedExitTreeEnergy_le_half_selected
    {R p r depth : ℕ} {sig : Finset ℕ}
    (hr : r.Prime) :
    vfMidCompletedGateSelectedClippedExitTreeEnergy R p sig r depth ≤
      (1 / 2 : ℝ) * vfMidCompletedGateSelectedParentEnergy R p sig r := by
  unfold vfMidCompletedGateSelectedClippedExitTreeEnergy
    vfMidCompletedGateSelectedParentEnergy
    vfMidSelectedReciprocalParentEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro parent _hparent
  exact
    vfMidRetainedAboveFirstClippedExitTreeEnergy_le_half_parent
      hr depth parent (lowOwnerThresholdEulerPairCoefficient R p r parent)

/-- **Fractional all-depth gate budget.**

The all-depth positive clipped leakage inherits the full completed gate square
only through #890's exact reciprocal capacity fraction. -/
theorem vfMidCompletedGateSelectedClippedExitTreeEnergy_le_half_fractionalGate
    {R p r depth : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) (hr : r.Prime) :
    vfMidCompletedGateSelectedClippedExitTreeEnergy R p sig r depth ≤
      (1 / 2 : ℝ) *
        (vfMidCompletedGateActiveCapacityFraction R p sig r *
          lowOwnerFirstOwnerCompletedIncidenceGateSquareMass R p sig r) := by
  have h :=
    vfMidCompletedGateSelectedClippedExitTreeEnergy_le_half_selected
      (R := R) (p := p) (r := r) (depth := depth) (sig := sig) hr
  have hreconstruct :=
    vfMidCompletedGateActiveCapacityFraction_mul_gate_eq_selected
      (R := R) (p := p) (r := r) (sig := sig) hp
  rw [hreconstruct]
  exact h

/-- Critical owner ratios are nonnegative on genuine prime owners. -/
theorem zeroTargetCriticalOwnerRatio_nonneg_of_prime
    {p : ℕ} (hp : p.Prime) :
    0 ≤ zeroTargetCriticalOwnerRatio p := by
  unfold zeroTargetCriticalOwnerRatio
  positivity

/-- Critical owner ratios lie below two on genuine prime owners. -/
theorem zeroTargetCriticalOwnerRatio_le_two_of_prime
    {p : ℕ} (hp : p.Prime) :
    zeroTargetCriticalOwnerRatio p ≤ 2 := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_le
  unfold zeroTargetCriticalOwnerRatio
  apply (div_le_iff₀ hp0).2
  nlinarith

/-- **Critical complete-family dissipation.**

At the actual critical owner ratio, the aggregate of every complete post-root
family is nonpositive.  Therefore complete families cannot consume any positive
first-bad energy budget. -/
theorem sum_all_zeroTargetMellinCompletePostRootFamilies_critical_nonpos
    (W : ℕ) :
    (∑ p ∈ postRootPrimeFamilySet W,
      ∑ mn ∈ mertensPositivePhysicalPairCarrier (W / p),
        zeroTargetMellinPhysicalSuperLcmFourCorner W p
          (zeroTargetCriticalOwnerRatio p) mn.1 mn.2) ≤ 0 := by
  apply sum_all_zeroTargetMellinCompletePostRootFamilies_nonpos
  · intro p hpMem
    exact zeroTargetCriticalOwnerRatio_nonneg_of_prime
      (mem_postRootPrimeFamilySet.mp hpMem).2.2
  · intro p hpMem
    exact zeroTargetCriticalOwnerRatio_le_two_of_prime
      (mem_postRootPrimeFamilySet.mp hpMem).2.2

/-- Existing rank-zero/equal-parent remainder terminals are favorable in the
same zero-target signed currency. -/
theorem vfMidFinalRankTerminalPair_zeroTarget_nonpos
    {W : ℕ} {mn : ℕ × ℕ}
    (hmn : mn ∈ postRootCovarianceRemainderTerminalPairCarrier W) :
    postRootZeroTargetPairExcess mn ≤ 0 :=
  postRootCovarianceRemainderTerminalPair_zeroTargetExcess_nonpos hmn

end RHLean.Analysis
