import Mathlib
import «research.GLOBAL_RETURNED_CORE_RAW_PARENT_GLOBAL_ENDPOINT_GAP»
import «research.LOW_OWNER_AMPLITUDE_MELLIN_LEDGER_SPLICE»
import «research.LOW_OWNER_PHYSICAL_AMPLITUDE_TRANSPORT»

/-!
# Post-#755 global amplitude closure

PR #755 removed the raw-parent, revealed-signature, and lower-signature
bookkeeping before squaring.  The resulting real branch amplitude is

  sum_q M(Y_q)/q - M(R-1) + M(X_R).

The pre-existing zero-frequency AMP remainder is the opposite orientation of
that same endpoint ledger.  This file identifies the two exactly and then
applies the already-compiled reciprocal q^2 frame to the literal Mertens
daughter column.

No new arithmetic hypothesis, packetwise norm, or coefficient-L2 surrogate is
introduced.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- **#755 reaches the old AMP seam exactly.**  The fully reassembled real
raw-parent branch amplitude is the negative zero-frequency physical AMP
remainder. -/
theorem lowOwnerGlobalBranchIncidenceDifferenceAmplitude_cast_eq_neg_physicalRemainder_zero
    {R p r : ℕ}
    (hR : 56 ≤ R) (hp : p.Prime) (hr : r.Prime) (hpr : p < r) :
    ((lowOwnerGlobalBranchIncidenceDifferenceAmplitude R p r : ℝ) : ℂ) =
      -lowOwnerPhysicalAmplitudeRemainder R 0 := by
  rw [lowOwnerGlobalBranchIncidenceDifferenceAmplitude_eq_mertensGap
      (by omega : 2 ≤ R) hp hr hpr]
  rw [lowOwnerPhysicalAmplitudeRemainder_zero_eq_correlation_sub_reciprocalColumn
      R hR]
  rw [squareRootCanonicalRoughCorrelation_eq_mertens_pred_sub_endpoint
      R (by omega)]
  rw [← lowOwnerReciprocalMertensColumnReal_cast R]
  push_cast
  simp only [mertensSummatoryInt_cast]
  ring

/-- Energy version of the exact post-#755 identification. -/
theorem lowOwnerGlobalBranchIncidenceDifferenceAmplitude_sq_eq_remainderNormSq
    {R p r : ℕ}
    (hR : 56 ≤ R) (hp : p.Prime) (hr : r.Prime) (hpr : p < r) :
    lowOwnerGlobalBranchIncidenceDifferenceAmplitude R p r ^ 2 =
      ‖lowOwnerPhysicalAmplitudeRemainder R 0‖ ^ 2 := by
  have h :=
    lowOwnerGlobalBranchIncidenceDifferenceAmplitude_cast_eq_neg_physicalRemainder_zero
      hR hp hr hpr
  rw [← h, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rfl

/-- The exact reciprocal Mertens daughter column exposed by #755 inherits the
already-compiled quarter-frame energy estimate. -/
theorem lowOwnerReciprocalMertensColumnReal_sq_le_quarter_lowQ2DaughterEnergy
    (R : ℕ) :
    lowOwnerReciprocalMertensColumnReal R ^ 2 ≤
      (1 / 4 : ℝ) * canonicalRoughLowQ2DaughterEnergy R := by
  have h := lowOwnerCriticalMertensSynthesis_energy_le_quarter R 0
  rw [lowOwnerCriticalMertensSynthesis_zero_eq_reciprocalColumn R,
    ← lowOwnerReciprocalMertensColumnReal_cast R,
    Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
  exact h

/-- The remaining quantitative statement can now be stated directly on one
fixed #755 amplitude.  Owner-independence makes the auxiliary choice 2<3
irrelevant. -/
def LowOwnerPost755GlobalAmplitudeBound (C : ℝ) : Prop :=
  ∀ R : ℕ, ∀ K : ℝ,
    56 ≤ R →
    LowerMertensCriticalEnvelope R K →
    lowOwnerGlobalBranchIncidenceDifferenceAmplitude R 2 3 ^ 2 ≤
      C * (R : ℝ) ^ 2 * K

/-- **Name-lock:** a bound on the post-#755 global amplitude is exactly the
pre-existing physical AMP remainder bound, with the same constant. -/
theorem lowOwnerPost755GlobalAmplitudeBound_iff_physicalAmplitudeRemainderBound
    (C : ℝ) :
    LowOwnerPost755GlobalAmplitudeBound C ↔
      LowOwnerPhysicalAmplitudeRemainderBound C := by
  constructor
  · intro h
    intro R K hR hK
    rw [← lowOwnerGlobalBranchIncidenceDifferenceAmplitude_sq_eq_remainderNormSq
      hR (by norm_num : Nat.Prime 2) (by norm_num : Nat.Prime 3) (by norm_num : 2 < 3)]
    exact h R K hR hK
  · intro h
    intro R K hR hK
    rw [lowOwnerGlobalBranchIncidenceDifferenceAmplitude_sq_eq_remainderNormSq
      hR (by norm_num : Nat.Prime 2) (by norm_num : Nat.Prime 3) (by norm_num : 2 < 3)]
    exact h R K hR hK

/-- Any root-scale estimate on the post-#755 global amplitude therefore closes
the existing LOW-q² correlation consumer immediately. -/
theorem correlationLowQ2Energy_of_post755GlobalAmplitudeBound
    {C : ℝ} (h : LowOwnerPost755GlobalAmplitudeBound C) :
    CanonicalRoughCorrelationLowQ2EnergyStatementWith (1 / 2) (2 * C) := by
  apply correlationLowQ2Energy_of_physicalAmplitudeRemainderBound
  exact (lowOwnerPost755GlobalAmplitudeBound_iff_physicalAmplitudeRemainderBound C).mp h

end RHLean.Proof
