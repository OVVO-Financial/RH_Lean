import Mathlib
import «research.GLOBAL_RETURNED_CORE_SYNTHESIS»
import «research.STABLE_FAR_PERRON_BASEL_FRAME_SHARPENING»

/-!
# CORR-4: a relaxed full-physical-remainder inlet

The parent is the ACTUAL canonical rough correlation; the low daughters are the
literal Mertens values at floor((R^2-1)/q^2).  The physical remainder is the
complete compensated zero-frequency amplitude from the existing AMP transport.

All theorems in this file are finite deterministic inequalities or CONDITIONAL
RH consumers.  The central arithmetic inequality
  ||B_R||^2 <= (9/4) E_low(R) + C R^2 K
is NOT asserted unconditionally.

The already-proved two-term odd-prime Basel envelope 211/900 improves the
critical synthesis bound beyond the earlier 17/72 budget.  Young's inequality
then gives the strict coefficient 886/225 < 4, which feeds the existing CORR-4
terminal engine.  No individual owner is bounded by its daughter: the complete
remainder and every physical cross term remain intact.
-/

noncomputable section

open scoped BigOperators ArithmeticFunction.Moebius

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- The genuine low-owner critical synthesis has a stronger frame than 17/72.
    No arithmetic sign assumption enters the proof. -/
theorem lowOwnerCriticalSynthesis_energy_le_twoTermBasel
    (R : ℕ) (tau : ℝ) :
    ‖lowOwnerCriticalMertensSynthesis R tau‖ ^ 2 ≤
      (211 / 900 : ℝ) * canonicalRoughLowQ2DaughterEnergy R := by
  have hsub : canonicalRoughLowQ2Owners R ⊆
      (primesUpTo (R - 1)).erase 2 := Finset.sdiff_subset
  have hpos : ∀ q ∈ canonicalRoughLowQ2Owners R, 0 < q := by
    intro q hq
    exact (mem_primesUpTo.mp (Finset.mem_erase.mp (hsub hq)).2).1.pos
  have hbudget :
      (∑ q ∈ canonicalRoughLowQ2Owners R, (1 : ℝ) / (q : ℝ) ^ 2) ≤
        (211 / 900 : ℝ) := by
    calc
      _ ≤ ∑ q ∈ (primesUpTo (R - 1)).erase 2,
          (1 : ℝ) / (q : ℝ) ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro q _hq _hnot
        positivity
      _ ≤ (211 / 900 : ℝ) :=
        oddPrimeOwnerReciprocalSquareBudgetReal_le_twoTermBasel (R - 1)
  have hframe := stableFarCriticalQ2Synthesis_energy_le_reciprocalSquareBudget
    tau (canonicalRoughLowQ2Owners R) (lowOwnerRawMertensAmplitude R) hpos
  simp only [norm_sq_lowOwnerRawMertensAmplitude] at hframe
  change ‖lowOwnerCriticalMertensSynthesis R tau‖ ^ 2 ≤
    (∑ q ∈ canonicalRoughLowQ2Owners R, (1 : ℝ) / (q : ℝ) ^ 2) *
      canonicalRoughLowQ2DaughterEnergy R at hframe
  exact hframe.trans (mul_le_mul_of_nonneg_right hbudget
    (canonicalRoughLowQ2DaughterEnergy_nonneg R))

private theorem norm_add_sq_le_four_fourThirds (u v : ℂ) :
    ‖u + v‖ ^ 2 ≤ 4 * ‖u‖ ^ 2 + (4 / 3 : ℝ) * ‖v‖ ^ 2 := by
  have ht := norm_add_le u v
  have hu := norm_nonneg u
  have hv := norm_nonneg v
  have huv := norm_nonneg (u + v)
  have hsq : ‖u + v‖ ^ 2 ≤ (‖u‖ + ‖v‖) ^ 2 := by
    nlinarith
  nlinarith [sq_nonneg (3 * ‖u‖ - ‖v‖)]

/-- Useful for the imported 7/8 GUIDEPOST: isolate the endpoint rough
    correlation, leaving exactly 9/4 of low-daughter energy. -/
private theorem norm_sub_sq_le_guidepost (u v : ℂ) :
    ‖u - v‖ ^ 2 ≤
      (2025 / 1814 : ℝ) * ‖u‖ ^ 2 +
      (2025 / 211 : ℝ) * ‖v‖ ^ 2 := by
  have ht := norm_sub_le u v
  have hu := norm_nonneg u
  have hv := norm_nonneg v
  have huv := norm_nonneg (u - v)
  have hsq : ‖u - v‖ ^ 2 ≤ (‖u‖ + ‖v‖) ^ 2 := by
    nlinarith
  nlinarith [sq_nonneg (211 * ‖u‖ - 1814 * ‖v‖)]

/-- Unconditional full-physical-remainder comparison.  All mixed terms remain
    inside the norm: this is NOT the RH-strength remainder bound. -/
theorem lowOwnerPhysicalRemainder_sq_le_twoPointTwoFive_daughter_add_correlation
    (R : ℕ) (hR : 56 ≤ R) :
    ‖lowOwnerPhysicalAmplitudeRemainder R 0‖ ^ 2 ≤
      (9 / 4 : ℝ) * canonicalRoughLowQ2DaughterEnergy R +
        (2025 / 1814 : ℝ) * ‖squareRootCanonicalRoughCorrelation R‖ ^ 2 := by
  have hid := squareRootCanonicalRoughCorrelation_eq_criticalSynthesis_add_physicalRemainder
    R hR 0
  have hrearrange :
      lowOwnerPhysicalAmplitudeRemainder R 0 =
        squareRootCanonicalRoughCorrelation R -
          lowOwnerCriticalMertensSynthesis R 0 := by
    rw [hid]
    ring
  have hy := norm_sub_sq_le_guidepost
    (squareRootCanonicalRoughCorrelation R) (lowOwnerCriticalMertensSynthesis R 0)
  have hU := lowOwnerCriticalSynthesis_energy_le_twoTermBasel R 0
  have hE := canonicalRoughLowQ2DaughterEnergy_nonneg R
  rw [hrearrange]
  nlinarith

/-- The new arithmetic proposition to attack, on the COMPLETE compensation
    remainder (not the false pointwise owner=two*daughter assertion). -/
def LowOwnerPhysicalRelaxedRemainderBound (C : ℝ) : Prop :=
  ∀ R : ℕ, ∀ K : ℝ,
    56 ≤ R →
    LowerMertensCriticalEnvelope R K →
    ‖lowOwnerPhysicalAmplitudeRemainder R 0‖ ^ 2 ≤
      (9 / 4 : ℝ) * canonicalRoughLowQ2DaughterEnergy R +
        C * (R : ℝ) ^ 2 * K

/-- Equivalent signed Co-minus-Div target, with the REAL physical diagonal
    subtracted rather than silently discarded. -/
def LowOwnerRelaxedFirstOwnerGramBound (C : ℝ) : Prop :=
  ∀ R : ℕ, ∀ K : ℝ,
    56 ≤ R →
    LowerMertensCriticalEnvelope R K →
    2 * (∑ p ∈ primesUpTo (squareRootEndpoint R),
      lowOwnerZeroFrequencyFirstOwnerGram R p) ≤
        (9 / 4 : ℝ) * canonicalRoughLowQ2DaughterEnergy R +
        C * (R : ℝ) ^ 2 * K -
          lowOwnerZeroFrequencyMobiusDiagonal R

theorem relaxedFirstOwnerGram_iff_physicalRemainder (C : ℝ) :
    LowOwnerRelaxedFirstOwnerGramBound C ↔
      LowOwnerPhysicalRelaxedRemainderBound C := by
  constructor
  · intro h R K hR hK
    have heq :=
      norm_sq_lowOwnerPhysicalAmplitudeRemainder_zero_eq_diagonal_add_firstOwners
        R hR
    rw [heq]
    have hh := h R K hR hK
    linarith
  · intro h R K hR hK
    have heq :=
      norm_sq_lowOwnerPhysicalAmplitudeRemainder_zero_eq_diagonal_add_firstOwners
        R hR
    have hh := h R K hR hK
    rw [heq] at hh
    linarith

/-- The relaxed full-physical-remainder input gives the genuine CORR-4
    terminal contract.  Young: 4*(211/900)+(4/3)*(9/4)=886/225<4. -/
theorem correlationFour_of_relaxedPhysicalRemainder
    {C : ℝ} (hC : 0 ≤ C)
    (h : LowOwnerPhysicalRelaxedRemainderBound C) :
    CanonicalRoughCorrelationFourQ2EnergyStatement := by
  let C0 : ℝ := (4 / 3 : ℝ) * C
  have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
  refine ⟨C0, hC0, ?_⟩
  intro R K hR hK
  have hid := squareRootCanonicalRoughCorrelation_eq_criticalSynthesis_add_physicalRemainder
    R hR 0
  have hy := norm_add_sq_le_four_fourThirds
    (lowOwnerCriticalMertensSynthesis R 0)
    (lowOwnerPhysicalAmplitudeRemainder R 0)
  rw [← hid] at hy
  have hU := lowOwnerCriticalSynthesis_energy_le_twoTermBasel R 0
  have hB := h R K hR hK
  have hE := canonicalRoughLowQ2DaughterEnergy_nonneg R
  have hsum := canonicalRoughLow_add_high_Q2Energy_eq_full R
  have hhi := canonicalRoughHighQ2DaughterEnergy_nonneg R
  have hle : canonicalRoughLowQ2DaughterEnergy R ≤
      farFourOddQ2DaughterEnergy R := by linarith
  have hcombined :
      ‖squareRootCanonicalRoughCorrelation R‖ ^ 2 ≤
        (886 / 225 : ℝ) * canonicalRoughLowQ2DaughterEnergy R +
          (4 / 3 : ℝ) * C * (R : ℝ) ^ 2 * K := by
    nlinarith
  have hcoarse :
      (886 / 225 : ℝ) * canonicalRoughLowQ2DaughterEnergy R ≤
        4 * farFourOddQ2DaughterEnergy R := by
    nlinarith
  change ‖squareRootCanonicalRoughCorrelation R‖ ^ 2 ≤
    4 * farFourOddQ2DaughterEnergy R + C0 * (R : ℝ) ^ 2 * K
  dsimp [C0]
  nlinarith

/-- Conditional closure, with every unproved arithmetic input visible. -/
theorem riemannHypothesis_of_relaxedPhysicalRemainder
    {C : ℝ} (hC : 0 ≤ C)
    (h : LowOwnerPhysicalRelaxedRemainderBound C) :
    RiemannHypothesis :=
  riemannHypothesis_of_canonicalRoughCorrelationFourQ2Energy
    (correlationFour_of_relaxedPhysicalRemainder hC h)

/-- Same closure stated in Fred's unnormalized signed NNS Co/Div currency. -/
theorem riemannHypothesis_of_relaxedFirstOwnerGram
    {C : ℝ} (hC : 0 ≤ C)
    (h : LowOwnerRelaxedFirstOwnerGramBound C) :
    RiemannHypothesis :=
  riemannHypothesis_of_relaxedPhysicalRemainder hC
    ((relaxedFirstOwnerGram_iff_physicalRemainder C).mp h)

/-- The contraction available from the improved source coefficient, if the
    CORR-4 shell is rebuilt with it. The compiled consumer only needs <4. -/
theorem relaxedRemainder_effective_coefficient_subcritical :
    ((886 / 225 : ℝ) * (37 / 36) * (17 / 72)) < 1 := by
  norm_num

#print axioms lowOwnerCriticalSynthesis_energy_le_twoTermBasel
#print axioms lowOwnerPhysicalRemainder_sq_le_twoPointTwoFive_daughter_add_correlation
#print axioms relaxedFirstOwnerGram_iff_physicalRemainder
#print axioms correlationFour_of_relaxedPhysicalRemainder
#print axioms riemannHypothesis_of_relaxedPhysicalRemainder
