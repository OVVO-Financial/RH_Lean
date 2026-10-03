import Mathlib
import «research.VF_MID_FLOOR_LI_SIGNED_POPULATION_BALANCE»

/-!
# Floor-Li event transport and quadratic cancellation

This file records the exact theorem-grade content suggested by the finite
floor-Li relocation experiments.

The point is deliberately stronger than pointwise event alignment.  The
integer square-block correction

  delta_R = P_R - F_R

is simultaneously:

* the discrete derivative of the square-endpoint floor-Li backlog;
* the signed mass of the primitive {-1,0,1} floor-Li mismatch stream;
* minus the existing floor-Li block prime defect, hence an exact chronological
  owner-census correction;
* within strictly less than one count of the already-compiled Mobius/Abel
  carrier, the only difference being endpoint floor rounding.

The second part formalizes the cancellation invariant that motivated the
numerical stress tests.  If a control defect D is perturbed by an arbitrary
endpoint displacement e, then the difference of the two quadratic energy
increments is an exact boundary difference.  No assumption on the local
frequency, phase, spacing, or sign pattern of e is used.

The final part packages the hydrotope-style global chamber expression for a
finite family of signed event relocations.  A relocation is represented by a
birth step minus a death step.  Its active contribution is therefore one
signed interval, and the first difference of the total potential is exactly
the signed birth/death endpoint stream.

Nothing in this file asserts the empirical short-lifetime observation as an
asymptotic theorem.  The finite 10^8 experiment and its scope are documented in
`research/VF_MID_FLOOR_LI_TRANSPORT_MINING.md`.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

attribute [local instance] Classical.propDecidable

/-! ## Exact square-block actual-minus-floor-Li correction -/

/-- Actual square-block prime supply minus integer floor-Li block demand. -/
def vfMidFloorLiActualBlockCorrection (R : ℕ) : ℤ :=
  (vfMidIntegerBlockPrimeSupply R : ℤ) -
    vfMidFloorLiBlockSupply R

/-- The actual-minus-floor-Li block correction is exactly the discrete
derivative of the square-endpoint integer backlog. -/
theorem vfMidFloorLiActualBlockCorrection_eq_backlog_increment
    (R : ℕ) :
    vfMidFloorLiActualBlockCorrection R =
      vfMidPrimeFloorLiBacklog (R + 1) -
        vfMidPrimeFloorLiBacklog R := by
  rw [vfMidPrimeFloorLiBacklog_succ]
  unfold vfMidFloorLiActualBlockCorrection
  ring

/-- The same block correction is exactly the signed primitive mismatch mass on
the corresponding square block. -/
theorem vfMidFloorLiActualBlockCorrection_eq_signedMismatchMass
    (R : ℕ) :
    vfMidFloorLiActualBlockCorrection R =
      vfMidFloorLiSignedMismatchMass (R ^ 2) ((R + 1) ^ 2) := by
  have hsq : R ^ 2 ≤ (R + 1) ^ 2 := by nlinarith
  have hmass :=
    vfMidFloorLiSignedMismatchMass_eq_backlog_increment hsq
  rw [vfMidPrimeFloorLiIntegerBacklog_sq,
    vfMidPrimeFloorLiIntegerBacklog_sq] at hmass
  calc
    vfMidFloorLiActualBlockCorrection R =
        vfMidPrimeFloorLiBacklog (R + 1) -
          vfMidPrimeFloorLiBacklog R :=
      vfMidFloorLiActualBlockCorrection_eq_backlog_increment R
    _ = vfMidFloorLiSignedMismatchMass (R ^ 2) ((R + 1) ^ 2) :=
      hmass.symm

/-- The actual-minus-floor-Li correction is the negative of the repository's
native floor-Li block prime defect. -/
theorem vfMidFloorLiActualBlockCorrection_eq_neg_blockPrimeDefect
    (R : ℕ) :
    vfMidFloorLiActualBlockCorrection R =
      -vfMidFloorLiBlockPrimeDefect R := by
  unfold vfMidFloorLiActualBlockCorrection
    vfMidFloorLiBlockPrimeDefect
  ring

/-- On the parity-reduced chronological-owner carrier, the actual-minus-floor-Li
correction is exactly floor-Li composite demand minus the owner census. -/
theorem vfMidFloorLiActualBlockCorrection_eq_reference_sub_ownerCensus
    (R : ℕ) (hR : 2 ≤ R) :
    vfMidFloorLiActualBlockCorrection R =
      vfMidOddFloorLiCompositeReference R -
        ∑ p ∈ vfMidSquareBandLateOwnerPrimes 2 R,
          ((vfMidSquareBandCompositeOwner R p).card : ℤ) := by
  rw [vfMidFloorLiActualBlockCorrection_eq_neg_blockPrimeDefect]
  rw [← vfMidOddFloorLiCompositeDefect_eq_blockPrimeDefect R hR]
  rw [vfMidOddFloorLiCompositeDefect_eq_ownerCensus_sub_reference R hR]
  ring

/-- Square-block specialization of the existing exact Mobius/Abel bridge:
actual-minus-floor-Li block correction differs from the Mobius/Abel carrier by
strictly less than one count, entirely from endpoint floor rounding. -/
theorem norm_vfMidFloorLiActualBlockCorrection_sub_moebiusAbel_lt_one
    (R : ℕ) :
    ‖(vfMidFloorLiActualBlockCorrection R : ℂ) -
        vfMidFloorLiMoebiusAbelCarrier (R ^ 2) ((R + 1) ^ 2)‖ < 1 := by
  have hsq : R ^ 2 ≤ (R + 1) ^ 2 := by nlinarith
  rw [vfMidFloorLiActualBlockCorrection_eq_signedMismatchMass]
  exact norm_vfMidFloorLiSignedMismatchMass_sub_moebiusAbel_lt_one hsq

/-- Exact one-block quadratic energy identity for the floor-Li backlog. -/
theorem vfMidPrimeFloorLiBacklog_energy_step
    (R : ℕ) :
    vfMidPrimeFloorLiBacklog (R + 1) ^ 2 -
        vfMidPrimeFloorLiBacklog R ^ 2 =
      vfMidFloorLiActualBlockCorrection R ^ 2 +
        2 * vfMidPrimeFloorLiBacklog R *
          vfMidFloorLiActualBlockCorrection R := by
  rw [vfMidFloorLiActualBlockCorrection_eq_backlog_increment]
  ring

/-! ## Frequency/spacing perturbations are exact boundary energy -/

/-- **Quadratic perturbation telescope.**

Let `D,D'` be consecutive endpoint values for any control defect and
`e,e'` any perturbation whatsoever.  The difference between the quadratic
energy step of `D+e` and that of `D` is exactly the increment of the boundary
energy `2*D*e + e^2`.

There is no hypothesis on the local frequency, phase, spacing, correlation, or
sign pattern of the perturbation. -/
theorem quadraticPerturbationStep_eq_boundaryIncrement
    {α : Type*} [CommRing α]
    (D D' e e' : α) :
    (((D' + e') - (D + e)) ^ 2 +
        2 * (D + e) * ((D' + e') - (D + e))) -
      ((D' - D) ^ 2 + 2 * D * (D' - D)) =
        (2 * D' * e' + e' ^ 2) -
          (2 * D * e + e ^ 2) := by
  ring

/-! ## Global signed event-transport chamber formula -/

/-- A signed step that turns on at integer event location `a`. -/
def vfMidSignedTransportStep (σ : ℤ) (a n : ℕ) : ℤ :=
  if a ≤ n then σ else 0

/-- A signed relocation interval: birth step at `a`, death step at `b`. -/
def vfMidSignedTransportInterval
    (σ : ℤ) (a b n : ℕ) : ℤ :=
  vfMidSignedTransportStep σ a n -
    vfMidSignedTransportStep σ b n

/-- A single step has one primitive endpoint atom. -/
theorem vfMidSignedTransportStep_diff
    (σ : ℤ) (a q : ℕ) (hq : 0 < q) :
    vfMidSignedTransportStep σ a q -
        vfMidSignedTransportStep σ a (q - 1) =
      if q = a then σ else 0 := by
  unfold vfMidSignedTransportStep
  by_cases haq : a ≤ q
  · by_cases hap : a ≤ q - 1
    · have hqa : q ≠ a := by omega
      simp [haq, hap, hqa]
    · have hqa : q = a := by omega
      simp [haq, hap, hqa]
  · have hap : ¬ a ≤ q - 1 := by omega
    have hqa : q ≠ a := by omega
    simp [haq, hap, hqa]

/-- A relocation interval differentiates to exactly one signed birth atom and
one opposite signed death atom. -/
theorem vfMidSignedTransportInterval_diff
    (σ : ℤ) (a b q : ℕ) (hq : 0 < q) :
    vfMidSignedTransportInterval σ a b q -
        vfMidSignedTransportInterval σ a b (q - 1) =
      (if q = a then σ else 0) -
        (if q = b then σ else 0) := by
  unfold vfMidSignedTransportInterval
  calc
    (vfMidSignedTransportStep σ a q -
          vfMidSignedTransportStep σ b q) -
        (vfMidSignedTransportStep σ a (q - 1) -
          vfMidSignedTransportStep σ b (q - 1)) =
      (vfMidSignedTransportStep σ a q -
          vfMidSignedTransportStep σ a (q - 1)) -
        (vfMidSignedTransportStep σ b q -
          vfMidSignedTransportStep σ b (q - 1)) := by ring
    _ = (if q = a then σ else 0) -
          (if q = b then σ else 0) := by
      rw [vfMidSignedTransportStep_diff σ a q hq,
        vfMidSignedTransportStep_diff σ b q hq]

/-- When birth precedes death, the step difference is exactly the global
activation-condition form `σ * 1_{a ≤ n < b}`. -/
theorem vfMidSignedTransportInterval_eq_chamber
    (σ : ℤ) {a b n : ℕ} (hab : a ≤ b) :
    vfMidSignedTransportInterval σ a b n =
      if a ≤ n ∧ n < b then σ else 0 := by
  unfold vfMidSignedTransportInterval vfMidSignedTransportStep
  by_cases han : a ≤ n
  · by_cases hbn : b ≤ n
    · have hnot : ¬ (a ≤ n ∧ n < b) := by omega
      simp [han, hbn, hnot]
    · have hlt : n < b := by omega
      simp [han, hbn, hlt]
  · have hbn : ¬ b ≤ n := by omega
    have hnot : ¬ (a ≤ n ∧ n < b) := by simp [han]
    simp [han, hbn, hnot]

/-- Finite superposition of signed relocation intervals. -/
def vfMidSignedTransportPotential
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (σ : ι → ℤ)
    (birth death : ι → ℕ) (n : ℕ) : ℤ :=
  ∑ i ∈ s,
    vfMidSignedTransportInterval (σ i) (birth i) (death i) n

/-- **Global chamber closed form.**
If every relocation has birth before death, all local cases are encoded in one
finite activation sum. -/
theorem vfMidSignedTransportPotential_eq_chamberSum
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (σ : ι → ℤ)
    (birth death : ι → ℕ)
    (hbd : ∀ i ∈ s, birth i ≤ death i)
    (n : ℕ) :
    vfMidSignedTransportPotential s σ birth death n =
      ∑ i ∈ s,
        if birth i ≤ n ∧ n < death i then σ i else 0 := by
  unfold vfMidSignedTransportPotential
  apply Finset.sum_congr rfl
  intro i hi
  exact vfMidSignedTransportInterval_eq_chamber
    (σ i) (hbd i hi)

/-- The first difference of the whole transport potential is exactly the
signed birth/death endpoint stream.  Interior spacing does not produce a new
bulk term. -/
theorem vfMidSignedTransportPotential_diff
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (σ : ι → ℤ)
    (birth death : ι → ℕ)
    (q : ℕ) (hq : 0 < q) :
    vfMidSignedTransportPotential s σ birth death q -
        vfMidSignedTransportPotential s σ birth death (q - 1) =
      ∑ i ∈ s,
        ((if q = birth i then σ i else 0) -
          (if q = death i then σ i else 0)) := by
  unfold vfMidSignedTransportPotential
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  exact vfMidSignedTransportInterval_diff
    (σ i) (birth i) (death i) q hq

end RHLean.Analysis
