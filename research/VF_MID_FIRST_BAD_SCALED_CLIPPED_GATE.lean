import Mathlib
import «research.VF_MID_FIRST_BAD_ACTIVE_CLIPPED_BOUNDARY»
import «research.VF_MID_COMPLETED_GATE_PM_DENOMINATOR»

/-!
# Parentwise-scaled clipped-gate contraction for the first-bad source

This is the already-green #900 retained-scale contraction slice, transplanted
onto the #912 stack.  Every active completed raw parent keeps an arbitrary
scalar coefficient through the exact PM-to-reciprocal dictionary and the
all-depth clipped-exit half contraction.

No source-to-gate identification is asserted here.  This file supplies only the
coefficient-stable inequality engine needed after that exact identification.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Literal degree-two PM denominator after multiplying each completed-gate atom
by an arbitrary retained scalar attached to its raw parent. -/
def vfMidScaledCompletedGatePMDegreeTwoDenominator
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ)
    (scale : ℕ × ℕ → ℝ) : ℝ :=
  ∑ parent ∈
      lowOwnerFirstOwnerActiveCompletedPolarizationRawParentSet R p sig r,
    |scale parent *
      lowOwnerCompletedIncidenceFourCornerMass R p (r, parent)| ^ 2

/-- The correspondingly scaled all-depth positive clipped-exit ledger. -/
def vfMidScaledCompletedGateClippedExitTreeEnergy
    (R p : ℕ) (sig : Finset ℕ) (r depth : ℕ)
    (scale : ℕ × ℕ → ℝ) : ℝ :=
  ∑ parent ∈
      lowOwnerFirstOwnerActiveCompletedPolarizationRawParentSet R p sig r,
    vfMidRetainedAboveFirstClippedExitTreeEnergy
      R r depth parent
        (scale parent *
          lowOwnerThresholdEulerPairCoefficient R p r parent)

/-- The completed-gate PM square is exactly the retained reciprocal parent
energy after an arbitrary parentwise scalar is attached. -/
theorem vfMidScaledCompletedGatePMDegreeTwoDenominator_eq_retainedParentEnergy
    {R p r : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) (scale : ℕ × ℕ → ℝ) :
    vfMidScaledCompletedGatePMDegreeTwoDenominator R p sig r scale =
      ∑ parent ∈
        lowOwnerFirstOwnerActiveCompletedPolarizationRawParentSet R p sig r,
        lowOwnerRetainedCoefficientParentEnergy
          (scale parent *
            lowOwnerThresholdEulerPairCoefficient R p r parent)
          parent := by
  unfold vfMidScaledCompletedGatePMDegreeTwoDenominator
  apply Finset.sum_congr rfl
  intro parent hparent
  have hcompleted :
      parent ∈
        lowOwnerFirstOwnerCompletedPolarizationRawParentSet R p sig r :=
    (Finset.mem_filter.mp hparent).1
  rcases lowOwnerFirstOwnerCompletedPolarizationRawParent_data hp hcompleted with
    ⟨hr, _hpr, hra, hrb, haPos, hbPos⟩
  have hgate :
      lowOwnerCompletedIncidenceFourCornerMass R p (r, parent) ^ 2 =
        lowOwnerThresholdEulerPairCoefficient R p r parent ^ 2 *
          postRootCovarianceReciprocalPairEnergy parent := by
    simpa [lowOwnerCompletedIncidenceFourCornerMass,
      lowOwnerThresholdEulerParentEnergy] using
      (lowOwnerThresholdIncidence_fourCorner_sq_eq_eulerParentEnergy
        (R := R) (p := p) (r := r)
        (a := parent.1) (b := parent.2)
        hr hra hrb haPos hbPos)
  rw [sq_abs,
    lowOwnerRetainedCoefficientParentEnergy_eq_coefficient_sq_mul]
  calc
    (scale parent *
        lowOwnerCompletedIncidenceFourCornerMass R p (r, parent)) ^ 2 =
      scale parent ^ 2 *
        lowOwnerCompletedIncidenceFourCornerMass R p (r, parent) ^ 2 := by
          ring
    _ = scale parent ^ 2 *
        (lowOwnerThresholdEulerPairCoefficient R p r parent ^ 2 *
          postRootCovarianceReciprocalPairEnergy parent) := by
          rw [hgate]
    _ = (scale parent *
          lowOwnerThresholdEulerPairCoefficient R p r parent) ^ 2 *
        postRootCovarianceReciprocalPairEnergy parent := by
          ring

/-- **Parentwise-scaled all-depth half contraction.** -/
theorem vfMidScaledCompletedGateClippedExitTreeEnergy_le_half_pmDegreeTwo
    {R p r depth : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) (hr : r.Prime)
    (scale : ℕ × ℕ → ℝ) :
    vfMidScaledCompletedGateClippedExitTreeEnergy
        R p sig r depth scale ≤
      (1 / 2 : ℝ) *
        vfMidScaledCompletedGatePMDegreeTwoDenominator
          R p sig r scale := by
  rw [vfMidScaledCompletedGatePMDegreeTwoDenominator_eq_retainedParentEnergy
    hp scale]
  unfold vfMidScaledCompletedGateClippedExitTreeEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro parent _hparent
  exact
    vfMidRetainedAboveFirstClippedExitTreeEnergy_le_half_parent
      hr depth parent
        (scale parent *
          lowOwnerThresholdEulerPairCoefficient R p r parent)

/-- Global degree-two PM denominator with a different retained scalar allowed
at every outer Fubini label and raw parent. -/
def vfMidGlobalScaledCompletedGatePMDegreeTwoDenominator
    (R : ℕ)
    (scale : ℕ → Finset ℕ → ℕ → (ℕ × ℕ) → ℝ) : ℝ :=
  ∑ p ∈ primesUpTo (squareRootEndpoint R),
    ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
      ∑ r ∈ lowOwnerRevealedPrimesAbove R p,
        vfMidScaledCompletedGatePMDegreeTwoDenominator
          R p sig r (scale p sig r)

/-- Matching globally scaled positive clipped-exit tree ledger. -/
def vfMidGlobalScaledCompletedGateClippedExitTreeEnergy
    (R depth : ℕ)
    (scale : ℕ → Finset ℕ → ℕ → (ℕ × ℕ) → ℝ) : ℝ :=
  ∑ p ∈ primesUpTo (squareRootEndpoint R),
    ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
      ∑ r ∈ lowOwnerRevealedPrimesAbove R p,
        vfMidScaledCompletedGateClippedExitTreeEnergy
          R p sig r depth (scale p sig r)

/-- Global finite Fubini of the parentwise-scaled half contraction. -/
theorem vfMidGlobalScaledCompletedGateClippedExitTreeEnergy_le_half_pmDegreeTwo
    (R depth : ℕ)
    (scale : ℕ → Finset ℕ → ℕ → (ℕ × ℕ) → ℝ) :
    vfMidGlobalScaledCompletedGateClippedExitTreeEnergy R depth scale ≤
      (1 / 2 : ℝ) *
        vfMidGlobalScaledCompletedGatePMDegreeTwoDenominator R scale := by
  unfold vfMidGlobalScaledCompletedGateClippedExitTreeEnergy
    vfMidGlobalScaledCompletedGatePMDegreeTwoDenominator
  calc
    (∑ p ∈ primesUpTo (squareRootEndpoint R),
      ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
        ∑ r ∈ lowOwnerRevealedPrimesAbove R p,
          vfMidScaledCompletedGateClippedExitTreeEnergy
            R p sig r depth (scale p sig r)) ≤
      ∑ p ∈ primesUpTo (squareRootEndpoint R),
        ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
          ∑ r ∈ lowOwnerRevealedPrimesAbove R p,
            (1 / 2 : ℝ) *
              vfMidScaledCompletedGatePMDegreeTwoDenominator
                R p sig r (scale p sig r) := by
      apply Finset.sum_le_sum
      intro p hpMem
      have hp : p.Prime := (mem_primesUpTo.mp hpMem).1
      apply Finset.sum_le_sum
      intro sig _hsig
      apply Finset.sum_le_sum
      intro r hrMem
      have hr : r.Prime :=
        (mem_primesUpTo.mp (Finset.mem_filter.mp hrMem).1).1
      exact
        vfMidScaledCompletedGateClippedExitTreeEnergy_le_half_pmDegreeTwo
          (R := R) (p := p) (r := r) (depth := depth) (sig := sig)
          hp hr (scale p sig r)
    _ = (1 / 2 : ℝ) *
        (∑ p ∈ primesUpTo (squareRootEndpoint R),
          ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
            ∑ r ∈ lowOwnerRevealedPrimesAbove R p,
              vfMidScaledCompletedGatePMDegreeTwoDenominator
                R p sig r (scale p sig r)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _hp
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro sig _hsig
      rw [Finset.mul_sum]

end RHLean.Analysis
