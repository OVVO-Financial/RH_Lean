import Mathlib
import «research.GLOBAL_RETURNED_CORE_EMITTED_RECIPROCAL_CHARGE»

/-!
# The sufficient reciprocal envelope lives on inherited gate energy

The completed incidence gate has already crossed from signed polarization into
nonnegative reciprocal currency.  PR #740 proves the exact-label charge

  completed gate emitted energy <= global recursive inherited energy

and separately the coarse owner-parent majorant

  global recursive inherited energy <= (2/9) * global owner-parent energy.

The second inequality is useful but is not logically required for closure.
The physical right-rail object retains the literal child factor `1/r^2`, so a
root-scale estimate may be proved directly on the inherited ledger without
first proving the visibly stronger unweighted parent-energy estimate.

On the nonzero Mobius carrier there is a further exact simplification.  The
Euler lift contributes one factor of each parent coordinate, while reciprocal
pair energy contributes the inverse square of their product.  Since nonzero
Mobius weights have square one, these factors cancel exactly.  The retained
parent energy is therefore the square of the two commuting second incidence
differences of the deterministic threshold potential.  This is an identity,
not an estimate and not a Mertens input.

This file records that hierarchy as named interfaces.  No signed survivor,
AMP Gram, rank recurrence, or unweighted parent inventory is introduced into
the inherited target.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- A nonzero real Mobius step has unit square.  Kept local to this seam so the
cancellation theorem does not depend on an unrelated diagonal-energy module. -/
private theorem realMoebiusStep_sq_eq_one_of_ne_zero_inherited
    {n : ℕ} (hn : realMoebiusStep n ≠ 0) :
    realMoebiusStep n ^ 2 = 1 := by
  rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;>
    simp [realMoebiusStep, h] at hn ⊢

/-- On a nonzero reciprocal pair the reciprocal energy is exactly the inverse
square of the coordinate product. -/
private theorem postRootCovarianceReciprocalPairEnergy_eq_inv_product_sq_inherited
    {a b : ℕ}
    (hma : realMoebiusStep a ≠ 0)
    (hmb : realMoebiusStep b ≠ 0) :
    postRootCovarianceReciprocalPairEnergy (a, b) =
      1 / (((a : ℝ) ^ 2) * ((b : ℝ) ^ 2)) := by
  have hmaSq : realMoebiusStep a ^ 2 = 1 :=
    realMoebiusStep_sq_eq_one_of_ne_zero_inherited hma
  have hmbSq : realMoebiusStep b ^ 2 = 1 :=
    realMoebiusStep_sq_eq_one_of_ne_zero_inherited hmb
  unfold postRootCovarianceReciprocalPairEnergy
    postRootCovarianceReciprocalPairAmplitude
  rw [div_pow]
  rw [mul_pow, hmaSq, hmbSq]
  ring

/-- **Exact Mobius/reciprocal cancellation.**  On a positive nonzero parent,
Euler normalization cancels the reciprocal pair denominators and the squared
Mobius weights.  What remains is purely the product of the two second mixed
incidence squares of the deterministic threshold potential. -/
theorem lowOwnerThresholdEulerParentEnergy_eq_secondOwnerDifference_sq
    {R p r a b : ℕ}
    (hr : 0 < r) (ha : 0 < a) (hb : 0 < b)
    (hma : realMoebiusStep a ≠ 0)
    (hmb : realMoebiusStep b ≠ 0) :
    lowOwnerThresholdEulerParentEnergy R p r (a, b) =
      lowOwnerThresholdSecondOwnerDifference R p r a ^ 2 *
        lowOwnerThresholdSecondOwnerDifference R p r b ^ 2 := by
  have ha0 : (a : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt ha)
  have hb0 : (b : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hb)
  unfold lowOwnerThresholdEulerParentEnergy
  rw [postRootCovarianceReciprocalPairEnergy_eq_inv_product_sq_inherited hma hmb]
  unfold lowOwnerThresholdEulerPairCoefficient
  rw [lowOwnerThresholdCriticalEulerDifference_eq_nat_mul_secondDifference hr,
    lowOwnerThresholdCriticalEulerDifference_eq_nat_mul_secondDifference hr]
  field_simp [ha0, hb0]
  ring

/-- Root-scale envelope statement for the actual reciprocal energy emitted by
all greatest-owner children after the completed incidence gate.  This is the
minimal positive right-rail estimate needed to bound the gate output. -/
def LowOwnerGlobalRecursiveInheritedEnergyBound (C : ℝ) : Prop :=
  ∀ R : ℕ, ∀ K : ℝ,
    56 ≤ R →
    LowerMertensCriticalEnvelope R K →
    lowOwnerGlobalRecursiveInheritedEnergy R ≤
      C * (R : ℝ) ^ 2 * K

/-- Stronger optional envelope on the unweighted owner-labelled parent ledger.
It implies the inherited estimate, but closure does not require proving it. -/
def LowOwnerGlobalRecursiveOwnerParentEnergyBound (C : ℝ) : Prop :=
  ∀ R : ℕ, ∀ K : ℝ,
    56 ≤ R →
    LowerMertensCriticalEnvelope R K →
    lowOwnerGlobalRecursiveOwnerParentEnergy R ≤
      C * (R : ℝ) ^ 2 * K

/-- The global inherited ledger itself has the already-compiled `2/9`
owner-parent majorant.  This theorem merely exposes the local contraction from
#740 as a reusable global statement. -/
theorem lowOwnerGlobalRecursiveInheritedEnergy_le_two_ninths_globalOwnerParentEnergy
    (R : ℕ) :
    lowOwnerGlobalRecursiveInheritedEnergy R ≤
      (2 / 9 : ℝ) * lowOwnerGlobalRecursiveOwnerParentEnergy R := by
  unfold lowOwnerGlobalRecursiveInheritedEnergy
    lowOwnerGlobalRecursiveOwnerParentEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hpMem
  have hp : p.Prime := (mem_primesUpTo.mp hpMem).1
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro sig _hsig
  exact
    lowOwnerFirstOwnerRecursiveInheritedEnergy_le_two_ninths_ownerParentEnergy hp

/-- Any root-scale parent-ledger bound therefore supplies a root-scale inherited
bound with the expected `2/9` coefficient. -/
theorem lowOwnerGlobalRecursiveInheritedEnergyBound_of_ownerParentEnergyBound
    {C : ℝ}
    (hparent : LowOwnerGlobalRecursiveOwnerParentEnergyBound C) :
    LowOwnerGlobalRecursiveInheritedEnergyBound ((2 / 9 : ℝ) * C) := by
  intro R K hR hK
  have hinherited :=
    lowOwnerGlobalRecursiveInheritedEnergy_le_two_ninths_globalOwnerParentEnergy R
  have hparentR := hparent R K hR hK
  have hscale : (0 : ℝ) ≤ 2 / 9 := by norm_num
  calc
    lowOwnerGlobalRecursiveInheritedEnergy R ≤
        (2 / 9 : ℝ) * lowOwnerGlobalRecursiveOwnerParentEnergy R := hinherited
    _ ≤ (2 / 9 : ℝ) * (C * (R : ℝ) ^ 2 * K) :=
      mul_le_mul_of_nonneg_left hparentR hscale
    _ = ((2 / 9 : ℝ) * C) * (R : ℝ) ^ 2 * K := by ring

/-- **The inherited envelope is already sufficient for the completed gate.**
No parent-square estimate is needed: #740's exact-label charge lands directly
on this ledger. -/
theorem lowOwnerCompletedGateEmittedEnergy_le_root_sq_K_of_inheritedEnergyBound
    {C : ℝ}
    (hinherited : LowOwnerGlobalRecursiveInheritedEnergyBound C) :
    ∀ R : ℕ, ∀ K : ℝ,
      56 ≤ R →
      LowerMertensCriticalEnvelope R K →
      lowOwnerCompletedGateEmittedEnergy R ≤
        C * (R : ℝ) ^ 2 * K := by
  intro R K hR hK
  exact
    (lowOwnerCompletedGateEmittedEnergy_le_globalRecursiveInheritedEnergy R).trans
      (hinherited R K hR hK)

/-- Parent-envelope form, retained only as a convenient stronger sufficient
interface. -/
theorem lowOwnerCompletedGateEmittedEnergy_le_root_sq_K_of_ownerParentEnergyBound
    {C : ℝ}
    (hparent : LowOwnerGlobalRecursiveOwnerParentEnergyBound C) :
    ∀ R : ℕ, ∀ K : ℝ,
      56 ≤ R →
      LowerMertensCriticalEnvelope R K →
      lowOwnerCompletedGateEmittedEnergy R ≤
        ((2 / 9 : ℝ) * C) * (R : ℝ) ^ 2 * K := by
  exact
    lowOwnerCompletedGateEmittedEnergy_le_root_sq_K_of_inheritedEnergyBound
      (lowOwnerGlobalRecursiveInheritedEnergyBound_of_ownerParentEnergyBound hparent)

end RHLean.Proof
