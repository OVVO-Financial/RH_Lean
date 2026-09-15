import Mathlib
import «research.LOW_OWNER_RETURNED_AMPLITUDE_CORE»
import RHLean.Proof.SquareRootCrossRegionAmplification

/-!
# Quantitative closure from the returned AMP core

The exact splice now writes the zero-frequency AMP remainder as one coupled
non-root returned core plus the independently controlled root correction.
This file shows that a root-scale energy bound on that single core is sufficient
for the original physical AMP remainder theorem.
-/

noncomputable section

namespace RHLean.Proof

/-- The only remaining quantitative AMP target after exact returned-coordinate
reassembly. -/
def LowOwnerReturnedAmplitudeCoreBound (C : ℝ) : Prop :=
  ∀ R : ℕ, ∀ K : ℝ, 56 ≤ R → LowerMertensCriticalEnvelope R K →
    ‖lowOwnerReturnedAmplitudeCore R‖ ^ 2 ≤ C * (R : ℝ) ^ 2 * K

private theorem norm_add_sq_le_two_sum_sq_core (a b : ℂ) :
    ‖a + b‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  have htri : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
  have hsq : ‖a + b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := by
    nlinarith [norm_nonneg (a + b), norm_nonneg a, norm_nonneg b]
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

/-- The compiled `8R` root correction contributes at most `64 R² K` under the
lower-envelope convention. -/
theorem norm_returnedAmplitudeRootCorrection_sq_le_sixtyFour_root_sq_mul_envelope
    (R : ℕ) (K : ℝ) (hR : 56 ≤ R)
    (hK : LowerMertensCriticalEnvelope R K) :
    ‖frozenTopFarRoughRootCorrection R‖ ^ 2 ≤
      64 * (R : ℝ) ^ 2 * K := by
  have hroot := norm_returnedAmplitudeRootCorrection_le_eight_root R hR
  have hK1 : 1 ≤ K :=
    one_le_of_lowerMertensCriticalEnvelope (by omega) hK
  have hR0 : 0 ≤ (R : ℝ) := by positivity
  have hrootSq :
      ‖frozenTopFarRoughRootCorrection R‖ ^ 2 ≤ 64 * (R : ℝ) ^ 2 := by
    nlinarith [norm_nonneg (frozenTopFarRoughRootCorrection R)]
  have habsorb : 64 * (R : ℝ) ^ 2 ≤ 64 * (R : ℝ) ^ 2 * K := by
    have hnon : 0 ≤ 64 * (R : ℝ) ^ 2 := by positivity
    nlinarith
  exact hrootSq.trans habsorb

/-- **Returned-core closure.**  A bound on the single coupled non-root core
implies the original physical AMP remainder bound. -/
theorem physicalAmplitudeRemainderBound_of_returnedCoreBound
    {C : ℝ} (hC : LowOwnerReturnedAmplitudeCoreBound C) :
    LowOwnerPhysicalAmplitudeRemainderBound (2 * (C + 64)) := by
  intro R K hR hK
  rw [lowOwnerPhysicalAmplitudeRemainder_zero_eq_neg_returnedCore_sub_root
    R hR]
  have hsum := norm_add_sq_le_two_sum_sq_core
    (-lowOwnerReturnedAmplitudeCore R)
    (-frozenTopFarRoughRootCorrection R)
  have hcore := hC R K hR hK
  have hroot :=
    norm_returnedAmplitudeRootCorrection_sq_le_sixtyFour_root_sq_mul_envelope
      R K hR hK
  simp only [norm_neg] at hsum
  calc
    ‖-lowOwnerReturnedAmplitudeCore R -
        frozenTopFarRoughRootCorrection R‖ ^ 2 ≤
      2 * (‖lowOwnerReturnedAmplitudeCore R‖ ^ 2 +
        ‖frozenTopFarRoughRootCorrection R‖ ^ 2) := by
          simpa [sub_eq_add_neg] using hsum
    _ ≤ 2 * ((C * (R : ℝ) ^ 2 * K) +
      (64 * (R : ℝ) ^ 2 * K)) := by gcongr
    _ = (2 * (C + 64)) * (R : ℝ) ^ 2 * K := by ring

end RHLean.Proof
