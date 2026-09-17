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

This file records that hierarchy as named interfaces.  No signed survivor,
AMP Gram, rank recurrence, or unweighted parent inventory is introduced into
the inherited target.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

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
