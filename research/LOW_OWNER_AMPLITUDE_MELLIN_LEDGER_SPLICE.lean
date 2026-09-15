import Mathlib
import «research.LOW_OWNER_PHYSICAL_AMPLITUDE_TRANSPORT»
import «research.COVARIANCE_RECIPROCAL_OWNER_CONGESTION»
import RHLean.Proof.StableFarAdaptiveLedgerCollapse

/-!
# Mellin-ledger form of the physical AMP remainder

PR #715 gives the exact physical amplitude transport

  Corr_R = S_R(tau) + E_R(tau)

with the genuine unscaled q^2 Mertens daughters in `S_R`.  At zero frequency
the critical multiplier is exactly `1/q`, so the transport remainder is the
difference between the canonical rough correlation and the literal reciprocal
low-owner Mertens column.

Independently, the adaptive raw chronology is already known to equal the same
rough correlation on every complete descending prime schedule.  The first
section therefore identifies the outstanding AMP remainder as one exact Mellin
endpoint gap

  E_R(0) = raw adaptive Euler ledger - reciprocal q^2 daughter column.

No physical population is normed separately and no estimate is introduced.
The repository separately constructs a canonical complete descending schedule;
this module keeps the schedule abstract so the arithmetic splice does not depend
on that bookkeeping implementation.

The second section packages #714's pointwise `79/81` reciprocal-square
congestion into the corresponding finite weighted-energy contraction.  This is
the quantitative consumer available once the Mellin endpoint gap has been
routed onto the literal covariance owner graph.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Literal zero-frequency reciprocal column on the genuine LOW q^2 daughters. -/
def lowOwnerReciprocalMertensColumn (R : ℕ) : ℂ :=
  ∑ q ∈ canonicalRoughLowQ2Owners R,
    (1 / (q : ℂ)) * lowOwnerRawMertensAmplitude R q

/-- At zero log frequency the critical synthesis is exactly the reciprocal
Mertens column.  This uses the forward `1/q` critical multiplier and does not
invert the synthesis map. -/
theorem lowOwnerCriticalMertensSynthesis_zero_eq_reciprocalColumn
    (R : ℕ) :
    lowOwnerCriticalMertensSynthesis R 0 =
      lowOwnerReciprocalMertensColumn R := by
  unfold lowOwnerCriticalMertensSynthesis stableFarCriticalQ2Synthesis
    lowOwnerReciprocalMertensColumn
  apply Finset.sum_congr rfl
  intro q hq
  have hsub : q ∈ (primesUpTo (R - 1)).erase 2 :=
    Finset.sdiff_subset hq
  have hqpos : 0 < q :=
    (mem_primesUpTo.mp (Finset.mem_erase.mp hsub).2).1.pos
  rw [stableFarCriticalQ2LogMultiplier_eq_reciprocal_phase 0 hqpos]
  simp

/-- **Zero-frequency AMP remainder = raw correlation minus reciprocal daughter
column.**  This is just #715 with its multiplier normalized explicitly. -/
theorem lowOwnerPhysicalAmplitudeRemainder_zero_eq_correlation_sub_reciprocalColumn
    (R : ℕ) (hR : 56 ≤ R) :
    lowOwnerPhysicalAmplitudeRemainder R 0 =
      squareRootCanonicalRoughCorrelation R -
        lowOwnerReciprocalMertensColumn R := by
  have h :=
    squareRootCanonicalRoughCorrelation_eq_criticalSynthesis_add_physicalRemainder
      R hR 0
  rw [lowOwnerCriticalMertensSynthesis_zero_eq_reciprocalColumn R] at h
  linear_combination h

/-- Raw Euler ledger on any chosen descending prime schedule. -/
def adaptiveRawCorrelationLedger (R : ℕ) (ps : List ℕ) : ℂ :=
  squareRootCanonicalRoughAdaptiveRawLedger R ps
    (Finset.Icc 1 (squareRootEndpoint R))
    (fun _ => (1 : ℂ))

/-- Every complete descending schedule carries exactly the rough correlation. -/
theorem adaptiveRawCorrelationLedger_eq_correlation_of_completeSchedule
    (R : ℕ) (hR : 56 ≤ R) (ps : List ℕ)
    (hsched : SquareRootCanonicalRoughCompleteDescendingSchedule R ps) :
    adaptiveRawCorrelationLedger R ps =
      squareRootCanonicalRoughCorrelation R := by
  unfold adaptiveRawCorrelationLedger
  exact adaptiveRawLedger_eq_roughCorrelation_of_completeSchedule
    R hR ps hsched

/-- The outstanding physical AMP correction is one exact Mellin endpoint gap:
the complete raw zero-factor Euler ledger minus the reciprocal q^2 daughter
column.  All stable-far, terminal, owner-two and root populations have already
been reassembled into the raw ledger before this identity is stated. -/
theorem lowOwnerPhysicalAmplitudeRemainder_zero_eq_rawLedger_sub_reciprocalColumn
    (R : ℕ) (hR : 56 ≤ R) (ps : List ℕ)
    (hsched : SquareRootCanonicalRoughCompleteDescendingSchedule R ps) :
    lowOwnerPhysicalAmplitudeRemainder R 0 =
      adaptiveRawCorrelationLedger R ps -
        lowOwnerReciprocalMertensColumn R := by
  rw [lowOwnerPhysicalAmplitudeRemainder_zero_eq_correlation_sub_reciprocalColumn
      R hR,
    adaptiveRawCorrelationLedger_eq_correlation_of_completeSchedule R hR ps hsched]

/-! ## Quantitative consumer from #714 -/

/-- Weighted reciprocal-square congestion energy on an arbitrary finite set of
literal covariance parents. -/
def postRootCovarianceReciprocalCongestionEnergy
    (W : ℕ) (parents : Finset (ℕ × ℕ)) (E : (ℕ × ℕ) → ℚ) : ℚ :=
  ∑ parent ∈ parents,
    postRootCovarianceReciprocalOwnerCongestion W parent * E parent

/-- **Aggregate 79/81 contraction.**  Once an energy has been transported onto
the literal covariance owner graph with its natural reciprocal-square owner
weight, #714 contracts every nonnegative parent energy by the same strict
constant. -/
theorem postRootCovarianceReciprocalCongestionEnergy_le_79_over_81
    (W : ℕ) (parents : Finset (ℕ × ℕ)) (E : (ℕ × ℕ) → ℚ)
    (hE : ∀ parent ∈ parents, 0 ≤ E parent) :
    postRootCovarianceReciprocalCongestionEnergy W parents E ≤
      (79 / 81 : ℚ) * ∑ parent ∈ parents, E parent := by
  unfold postRootCovarianceReciprocalCongestionEnergy
  calc
    (∑ parent ∈ parents,
        postRootCovarianceReciprocalOwnerCongestion W parent * E parent) ≤
      ∑ parent ∈ parents, (79 / 81 : ℚ) * E parent := by
        apply Finset.sum_le_sum
        intro parent hparent
        exact mul_le_mul_of_nonneg_right
          (postRootCovarianceReciprocalOwnerCongestion_le_79_over_81 W parent)
          (hE parent hparent)
    _ = (79 / 81 : ℚ) * ∑ parent ∈ parents, E parent := by
      rw [Finset.mul_sum]

/-- The contraction coefficient has explicit positive slack `2/81`. -/
theorem postRootCovarianceReciprocalCongestionEnergy_add_slack_le_parentEnergy
    (W : ℕ) (parents : Finset (ℕ × ℕ)) (E : (ℕ × ℕ) → ℚ)
    (hE : ∀ parent ∈ parents, 0 ≤ E parent) :
    postRootCovarianceReciprocalCongestionEnergy W parents E +
        (2 / 81 : ℚ) * ∑ parent ∈ parents, E parent ≤
      ∑ parent ∈ parents, E parent := by
  have h :=
    postRootCovarianceReciprocalCongestionEnergy_le_79_over_81
      W parents E hE
  linarith

end RHLean.Proof
