import Mathlib
import «research.CORR4_OAI_SQUARE_ENDPOINT_BOOTSTRAP_20261025»

/-!
# CORR4: power remainder -> exact nearest-square endpoint renewal

This is the PRECISE all-root arithmetic step between the independent physical
remainder estimate and a Mertens power bootstrap.

Assume only a source-level B_R estimate:
    |B_R|² <= (9/4)*E_low(R) + A*R^(4*beta).
No Mertens power assumption is smuggled into that hypothesis.

The proved steps below:
  1. original U+B=Crough with sharp 211/900 frame;
  2. 37/36 nearest-square rounding of *actual* q² daughters;
  3. 101/100 parent Young step with the true M(R-1).

The next step is induction on strictly smaller nearest-square roots plus the
previously compiled all-integer interpolation. That induction is not asserted
in this file. In particular, neither these finite identities nor an assumed
physical remainder estimate proves RH without that real induction.
-/

noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- A genuinely source-level, all-root power-saving TARGET, not a theorem. -/
def Corr4PowerPhysicalRemainder (A β : ℝ) : Prop :=
  ∀ R : ℕ, 56 ≤ R →
    ‖lowOwnerPhysicalAmplitudeRemainder R 0‖ ^ 2 ≤
      (9 / 4 : ℝ) * canonicalRoughLowQ2DaughterEnergy R +
        A * Real.rpow (R : ℝ) (4 * β)

private theorem corr4_power_norm_add_sq
    (u v : ℂ) :
    ‖u + v‖ ^ 2 ≤
      4 * ‖u‖ ^ 2 + (4 / 3 : ℝ) * ‖v‖ ^ 2 := by
  have ht := norm_add_le u v
  have hu := norm_nonneg u
  have hv := norm_nonneg v
  have huv := norm_nonneg (u + v)
  have hsq : ‖u + v‖ ^ 2 ≤ (‖u‖ + ‖v‖) ^ 2 := by nlinarith
  nlinarith [sq_nonneg (3 * ‖u‖ - ‖v‖)]

private theorem corr4_power_norm_sub_sq_onePercent
    (u v : ℂ) :
    ‖u - v‖ ^ 2 ≤
      (101 / 100 : ℝ) * ‖u‖ ^ 2 + 101 * ‖v‖ ^ 2 := by
  have ht := norm_sub_le u v
  have hu := norm_nonneg u
  have hv := norm_nonneg v
  have huv := norm_nonneg (u - v)
  have hsq : ‖u - v‖ ^ 2 ≤ (‖u‖ + ‖v‖) ^ 2 := by nlinarith
  nlinarith [sq_nonneg (‖u‖ - 100 * ‖v‖)]

/-- Physically original Crough energy, with the *actual rounded-square*
    daughter energy and the independently assumed B_R power saving. -/
theorem corr4_rough_power_recurrence_after_rounding
    {A β : ℝ} (hB : Corr4PowerPhysicalRemainder A β)
    (R : ℕ) (hR : 56 ≤ R) :
    ‖squareRootCanonicalRoughCorrelation R‖ ^ 2 ≤
      ((886 / 225 : ℝ) * (37 / 36)) *
          corr4NearestSquareDaughterEnergy R +
        ((886 / 225 : ℝ) * (629 / 72)) * (R : ℝ) ^ 2 +
        (4 / 3 : ℝ) * A * Real.rpow (R : ℝ) (4 * β) := by
  have hid :=
    squareRootCanonicalRoughCorrelation_eq_criticalSynthesis_add_physicalRemainder
      R hR 0
  have hy := corr4_power_norm_add_sq
    (lowOwnerCriticalMertensSynthesis R 0)
    (lowOwnerPhysicalAmplitudeRemainder R 0)
  rw [← hid] at hy
  have hU := lowOwnerCriticalSynthesis_energy_le_twoTermBasel R 0
  have hB0 := hB R hR
  have hRound := corr4_daughter_round_to_square R
  nlinarith

/-- The unrounded parent is M(R-1)-M(R²-1).  One 1%-Young step leaves a
    genuine historical M(R-1)² rather than silently deleting it. -/
theorem corr4_mertens_endpoint_power_recurrence
    {A β : ℝ} (hB : Corr4PowerPhysicalRemainder A β)
    (R : ℕ) (hR : 56 ≤ R) :
    ‖mertensSummatory (squareRootEndpoint R)‖ ^ 2 ≤
      (101 / 100 : ℝ) *
        ((886 / 225 : ℝ) * (37 / 36)) *
          corr4NearestSquareDaughterEnergy R +
      (101 / 100 : ℝ) *
        ((886 / 225 : ℝ) * (629 / 72)) * (R : ℝ) ^ 2 +
      (101 / 100 : ℝ) * (4 / 3 : ℝ) *
        A * Real.rpow (R : ℝ) (4 * β) +
      101 * ‖mertensSummatory (R - 1)‖ ^ 2 := by
  have hcorr :=
    squareRootCanonicalRoughCorrelation_eq_mertens_pred_sub_endpoint
      R (by omega)
  have hM :
      mertensSummatory (squareRootEndpoint R) =
        squareRootCanonicalRoughCorrelation R -
          mertensSummatory (R - 1) := by
    rw [hcorr]
    ring
  have hsplit := corr4_power_norm_sub_sq_onePercent
    (squareRootCanonicalRoughCorrelation R)
    (mertensSummatory (R - 1))
  rw [← hM] at hsplit
  have hrec := corr4_rough_power_recurrence_after_rounding hB R hR
  nlinarith

/-- Strict one-step renewal coefficient: 1% root-term Young slack and 37/36
    nearest-square loss still leave >4% of the parent quadratic envelope. -/
theorem corr4_power_rounded_root_coefficient_lt_one :
    ((101 / 100 : ℝ) * (886 / 225) * (37 / 36) * (211 / 900)) < 1 := by
  norm_num

#print axioms corr4_rough_power_recurrence_after_rounding
#print axioms corr4_mertens_endpoint_power_recurrence
#print axioms corr4_power_rounded_root_coefficient_lt_one

end RHLean.Proof
