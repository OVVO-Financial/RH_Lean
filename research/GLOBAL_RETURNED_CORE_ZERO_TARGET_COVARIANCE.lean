import Mathlib
import «research.LOW_OWNER_RETURNED_AMPLITUDE_CORE»
import «research.ZERO_TARGET_CLIPPED_OWNER_ENERGY_CONTRACTION»
import «research.ZERO_TARGET_MELLIN_COMPLETE_POST_ROOT_CUBES»
import «research.ZERO_TARGET_COVARIANCE_OWNER_DESCENT»

/-!
# Global zero-target covariance frontier for the returned AMP core

This file starts the decisive post-AMP square step.  The full returned core is
kept coupled before squaring.  The critical physical owner square is then
resolved exactly into three pieces:

* the favorable negative first-LCM crossing;
* a quadratic continuation of the same parent zero-target mode;
* the genuinely one-dimensional companion-clipped exit, already carrying the
  reciprocal critical owner factor.

Thus there is no fourth local cross-owner population.  The remaining global
job is a finite first-separation-owner reindexing of the quadratic continuation;
if that continuation telescopes through the strictly increasing owner/rank
recursion, the only positive exit is the clipped carrier already contracted by
`79/81`.

No norm, triangle inequality, RH hypothesis, or Mertens magnitude estimate is
introduced here.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-! ## Keep the returned core coupled before the square -/

/-- The reciprocal returned packet and its Euler-memory packet are one exact
centered q² tower.  This is the useful pre-square form of the returned core. -/
theorem lowOwnerReturnedAmplitudeCore_eq_reciprocal_add_centered_add_terminal
    (R : ℕ) :
    lowOwnerReturnedAmplitudeCore R =
      lowOwnerReciprocalMertensColumn R + farFourQ2CenteredTower R +
        farFourTerminalRemainder R := by
  unfold lowOwnerReturnedAmplitudeCore
  rw [farFourQ2CenteredTower_eq_globalReturnedReciprocal_add_memory R]
  ring

/-- Equivalently, above the stable-far onset the entire non-root returned core
is the reciprocal q² daughter column minus the already signed physical far
residual.  No returned bookkeeping component is normed separately. -/
theorem lowOwnerReturnedAmplitudeCore_eq_reciprocal_sub_farResidual
    (R : ℕ) (hR : 56 ≤ R) :
    lowOwnerReturnedAmplitudeCore R =
      lowOwnerReciprocalMertensColumn R - lowWheelFrozenTopFarResidual R := by
  rw [lowOwnerReturnedAmplitudeCore_eq_reciprocal_add_centered_add_terminal,
    lowWheelFrozenTopFarResidual_eq_neg_q2CenteredTower_sub_terminal R hR]
  ring

/-! ## Exact critical owner-square trichotomy -/

/-- The favorable first-LCM crossing indicator on an admitted owner square. -/
def zeroTargetCriticalFirstCrossingIndicator
    (W p a b : ℕ) : ℝ :=
  if Nat.lcm a b ≤ W ∧ W < p * Nat.lcm a b ∧ p * a ≤ W then 1 else 0

/-- The quadratic continuation indicator.  Unlike the first-crossing term, it
also remains present when the parent LCM was already beyond the endpoint; this
is why it must be reindexed globally rather than discarded pointwise. -/
def zeroTargetCriticalContinuationIndicator
    (W p a b : ℕ) : ℝ :=
  if W < p * Nat.lcm a b then 1 else 0

/-- The only genuinely one-dimensional incomplete exit: the first owner wall
is crossed and the companion mixed corner `p*b` is clipped by the endpoint. -/
def zeroTargetCriticalClippedExitIndicator
    (W p a b : ℕ) : ℝ :=
  if W < p * Nat.lcm a b ∧ W < p * b then 1 else 0

/-- **Exact critical three-term owner square.**  On every admitted mixed owner
child there are exactly three signed pieces: negative first crossing, quadratic
continuation of the parent mode, and reciprocal companion-clipped exit.

In particular there is no additional local cross-owner remainder hidden by the
Mellin interpolation. -/
theorem zeroTargetMellinPhysicalSuperLcmFourCorner_critical_eq_threeTerm
    {W p a b : ℕ}
    (hp : p.Prime) (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b)
    (hab : a ≤ b) (hbW : b ≤ W) (hpaW : p * a ≤ W) :
    zeroTargetMellinPhysicalSuperLcmFourCorner W p
        (zeroTargetCriticalOwnerRatio p) a b =
      -postRootZeroTargetPairExcess (a, b) *
          zeroTargetCriticalFirstCrossingIndicator W p a b +
      postRootZeroTargetPairExcess (a, b) *
          (1 - 1 / (p : ℝ)) ^ 2 *
          zeroTargetCriticalContinuationIndicator W p a b +
      postRootZeroTargetPairExcess (a, b) *
          ((1 / (p : ℝ)) * (1 - 1 / (p : ℝ))) *
          zeroTargetCriticalClippedExitIndicator W p a b := by
  rw [zeroTargetMellinPhysicalSuperLcmFourCorner_critical_eq_neg_firstCrossing_add_memoryEdge
    hp hpa hpb hab hbW hpaW]
  have hEdge :=
    critical_one_sub_mul_edge_eq_quadratic_add_reciprocalBoundary
      (W := W) (p := p) (a := a) (b := b)
      hp hpa hpb hab hbW hpaW
  unfold zeroTargetCriticalFirstCrossingIndicator
    zeroTargetCriticalContinuationIndicator
    zeroTargetCriticalClippedExitIndicator
  calc
    -postRootZeroTargetPairExcess (a, b) *
          (if Nat.lcm a b ≤ W ∧ W < p * Nat.lcm a b ∧ p * a ≤ W
            then 1 else 0) +
        (1 - 1 / (p : ℝ)) * postRootZeroTargetPairExcess (a, b) *
          physicalSuperLcmMellinEdge W p (1 / (p : ℝ)) a b =
      -postRootZeroTargetPairExcess (a, b) *
          (if Nat.lcm a b ≤ W ∧ W < p * Nat.lcm a b ∧ p * a ≤ W
            then 1 else 0) +
        postRootZeroTargetPairExcess (a, b) *
          ((1 - 1 / (p : ℝ)) *
            physicalSuperLcmMellinEdge W p (1 / (p : ℝ)) a b) := by ring
    _ =
      -postRootZeroTargetPairExcess (a, b) *
          (if Nat.lcm a b ≤ W ∧ W < p * Nat.lcm a b ∧ p * a ≤ W
            then 1 else 0) +
      postRootZeroTargetPairExcess (a, b) *
          (1 - 1 / (p : ℝ)) ^ 2 *
          (if W < p * Nat.lcm a b then 1 else 0) +
      postRootZeroTargetPairExcess (a, b) *
          ((1 / (p : ℝ)) * (1 - 1 / (p : ℝ))) *
          (if W < p * Nat.lcm a b ∧ W < p * b then 1 else 0) := by
      rw [hEdge]
      ring

/-- The clipped coefficient in the exact trichotomy already contains one
reciprocal owner factor before squaring. -/
theorem zeroTargetCriticalClippedCoefficient_sq
    (p : ℕ) :
    ((1 / (p : ℝ)) * (1 - 1 / (p : ℝ))) ^ 2 =
      (1 - 1 / (p : ℝ)) ^ 2 * (1 / (p : ℝ)) ^ 2 := by
  ring

end RHLean.Proof
