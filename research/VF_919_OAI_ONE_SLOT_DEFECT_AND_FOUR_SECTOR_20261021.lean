import Mathlib
import «research.VF_919_NNS_NORM_FIBER_BOUNDARY_CORRESPONDENCE_20261021»

/-!
# One-slot source: norm-window identity, conditional cancellation model,
# phase-defect witness, and a lossless four-sector finite carrier.

The OAI actual marked physical source includes a Mellin integral,
sextic Gauss sums, spectral masks, Hecke phases, and normalizers.
Nothing in this file identifies the scalar model with those originals.
In particular the (k+1)^(-1) owner weight is modelled EXPLICITLY,
not claimed to occur in compensatedTuple_one.

No independent phase moment saving, original column match,
or pointwise OAI j=0 annihilation is asserted.
-/

noncomputable section
open scoped Classical BigOperators

namespace RHLean.Proof.CompensatedTupleSourceBridge

/-- Scale equality for the actual per-prime norm, no P_ref dilation. -/
theorem rescaled_window_arg_eq_marked_arg
    (U Np Nb : ℝ) (hU : U ≠ 0) (hNp : Np ≠ 0) :
    Nb / (U / Np) = (Np * Nb) / U := by
  field_simp [hU, hNp]
  ring

/-- Exact algebraic shape of OAI one-slot compensation.
The arguments markedPhysical and rescaledPhysical represent the FULL
theta/Poisson amplitudes, not Möbius/log-polynomial surrogates. -/
def originalOneSlotShape
    (etaBar rescaleFactor markedPhysical rescaledPhysical : ℂ) : ℂ :=
  etaBar * markedPhysical - rescaleFactor * rescaledPhysical

theorem originalOneSlotShape_eq_zero_iff
    (etaBar rescaleFactor markedPhysical rescaledPhysical : ℂ) :
    originalOneSlotShape etaBar rescaleFactor
      markedPhysical rescaledPhysical = 0 ↔
      etaBar * markedPhysical =
        rescaleFactor * rescaledPhysical := by
  unfold originalOneSlotShape
  exact sub_eq_zero

/-- Pure-source counterexample: matched arguments need not imply
matched physical coefficients or normalized phases. -/
theorem oneSlot_matching_window_not_enough_example :
    originalOneSlotShape 1 1 1 2 = -1 := by
  norm_num [originalOneSlotShape]

/-! ## Explicitly CONDITIONAL scalar owner-log model -/

def rescaledModelAtom (w Lb : ℂ) (j : ℕ) : ℂ :=
  w * Lb ^ j

def markedModelAtom (w : ℂ) (k : ℕ) (Lb Lp : ℂ) (j : ℕ) : ℂ :=
  -(w / ((k : ℂ) + 1)) * (Lb + Lp) ^ j

def multiSelectedModelOverlap (w : ℂ) (k : ℕ) (Lb : ℂ) (j : ℕ) : ℂ :=
  ((k : ℂ) / ((k : ℂ) + 1)) * w * Lb ^ j

def logDerivativeModelShift (w : ℂ) (k : ℕ)
    (Lb Lp : ℂ) (j : ℕ) : ℂ :=
  -(w / ((k : ℂ) + 1)) * ((Lb + Lp) ^ j - Lb ^ j)

theorem natCast_add_one_ne_zero (k : ℕ) : (k : ℂ) + 1 ≠ 0 := by
  exact_mod_cast Nat.succ_ne_zero k

theorem model_rescaled_add_marked_eq_overlap_add_shift
    (w Lb Lp : ℂ) (k j : ℕ) :
    rescaledModelAtom w Lb j + markedModelAtom w k Lb Lp j =
      multiSelectedModelOverlap w k Lb j +
        logDerivativeModelShift w k Lb Lp j := by
  unfold rescaledModelAtom markedModelAtom
    multiSelectedModelOverlap logDerivativeModelShift
  have hk : (k : ℂ) + 1 ≠ 0 := natCast_add_one_ne_zero k
  field_simp [hk]
  ring

theorem model_single_selected_degree_zero_cancels (w Lb Lp : ℂ) :
    rescaledModelAtom w Lb 0 + markedModelAtom w 0 Lb Lp 0 = 0 := by
  simp [rescaledModelAtom, markedModelAtom]

theorem model_logDerivativeShift_one
    (w Lb Lp : ℂ) (k : ℕ) :
    logDerivativeModelShift w k Lb Lp 1 =
      -(w / ((k : ℂ) + 1)) * Lp := by
  unfold logDerivativeModelShift
  ring

theorem model_logDerivativeShift_two
    (w Lb Lp : ℂ) (k : ℕ) :
    logDerivativeModelShift w k Lb Lp 2 =
      -(w / ((k : ℂ) + 1)) * (2 * Lb * Lp + Lp ^ 2) := by
  unfold logDerivativeModelShift
  ring

/-- An unproved relative phase/weight multiplier gamma changes the
degree-zero result, even when scalar cutoff arguments coincide. -/
def phaseMarkedModelAtom (gamma w : ℂ) (k : ℕ)
    (Lb Lp : ℂ) (j : ℕ) : ℂ :=
  -(gamma * w / ((k : ℂ) + 1)) * (Lb + Lp) ^ j

theorem single_selected_phase_defect
    (gamma w Lb Lp : ℂ) :
    rescaledModelAtom w Lb 0 +
        phaseMarkedModelAtom gamma w 0 Lb Lp 0 =
      w * (1 - gamma) := by
  simp [rescaledModelAtom, phaseMarkedModelAtom]
  ring

theorem phase_reversal_prevents_degree_zero_cancellation :
    rescaledModelAtom (1 : ℂ) 1 0 +
        phaseMarkedModelAtom (-1) 1 0 1 0 = 2 := by
  norm_num [rescaledModelAtom, phaseMarkedModelAtom]

/-! ## Four sectors with priority collision, inert, low, other/high -/

variable {alpha : Type*}

def collisionSector (S : Finset alpha) (collision : alpha → Prop) : Finset alpha :=
  S.filter collision

def inertSector (S : Finset alpha)
    (collision inert : alpha → Prop) : Finset alpha :=
  S.filter (fun a => ¬ collision a ∧ inert a)

def canonicalLowSector (S : Finset alpha)
    (collision inert low : alpha → Prop) : Finset alpha :=
  S.filter (fun a => ¬ collision a ∧ ¬ inert a ∧ low a)

def otherHighSector (S : Finset alpha)
    (collision inert low : alpha → Prop) : Finset alpha :=
  S.filter (fun a => ¬ collision a ∧ ¬ inert a ∧ ¬ low a)

/-- No ideal labels, masks or high-height atoms are dropped. -/
theorem full_source_eq_four_sector_sums
    (S : Finset alpha) (collision inert low : alpha → Prop)
    (z : alpha → ℂ) :
    (∑ a ∈ S, z a) =
      (∑ a ∈ collisionSector S collision, z a) +
      (∑ a ∈ inertSector S collision inert, z a) +
      (∑ a ∈ canonicalLowSector S collision inert low, z a) +
      (∑ a ∈ otherHighSector S collision inert low, z a) := by
  classical
  unfold collisionSector inertSector canonicalLowSector otherHighSector
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hc : collision a <;>
  by_cases hi : inert a <;>
  by_cases hl : low a <;>
    simp [hc, hi, hl]

end RHLean.Proof.CompensatedTupleSourceBridge

#print axioms RHLean.Proof.CompensatedTupleSourceBridge.rescaled_window_arg_eq_marked_arg
#print axioms RHLean.Proof.CompensatedTupleSourceBridge.originalOneSlotShape_eq_zero_iff
#print axioms RHLean.Proof.CompensatedTupleSourceBridge.oneSlot_matching_window_not_enough_example
#print axioms RHLean.Proof.CompensatedTupleSourceBridge.model_rescaled_add_marked_eq_overlap_add_shift
#print axioms RHLean.Proof.CompensatedTupleSourceBridge.model_single_selected_degree_zero_cancels
#print axioms RHLean.Proof.CompensatedTupleSourceBridge.model_logDerivativeShift_one
#print axioms RHLean.Proof.CompensatedTupleSourceBridge.model_logDerivativeShift_two
#print axioms RHLean.Proof.CompensatedTupleSourceBridge.single_selected_phase_defect
#print axioms RHLean.Proof.CompensatedTupleSourceBridge.phase_reversal_prevents_degree_zero_cancellation
#print axioms RHLean.Proof.CompensatedTupleSourceBridge.full_source_eq_four_sector_sums
