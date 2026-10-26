import Mathlib
import «research.CORR4_OAI_RELAXED_REMAINDER_20261024»
import «research.MERTENS_EXPONENT_ENVELOPES»

/-!
# OpenAI 7/8 is a GUIDEPOST, not a fixed exponent

This file consumes a replaceable genuine MertensPowerBound(a).  At any
nonnegative exponent a it yields the exact physical CORR-4 remainder bound

  |B_R|^2 <= (9/4) E_low(R) + (2025/1814) * (C_a * X_R^a)^2.

The existing unconditional OpenAI 7/8 certificate can be instantiated in a
DEDICATED upstream-OAI workflow (not the native research closure). Any future
independently proved improvement to the Mertens exponent plugs into exactly
the same theorem.  The residual O(X^(2a)) is NOT the critical O(R^2 K_R)
needed for RH, and this file does not pretend otherwise.
-/

noncomputable section

open scoped BigOperators ArithmeticFunction.Moebius

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic RHLean.Analysis.MertensExponent

/-- Genuine rough correlation inherits any supplied Mertens exponent,
    with no need to guess future improvements to OpenAI's 7/8. -/
theorem roughCorrelation_norm_le_of_mertensPowerBound
    {a C : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hM : ∀ n : ℕ, 1 ≤ n →
      ‖mertensSummatory n‖ ≤ C * Real.rpow (n : ℝ) a)
    (R : ℕ) (hR : 56 ≤ R) :
    ‖squareRootCanonicalRoughCorrelation R‖ ≤
      (2 * C) * Real.rpow (squareRootEndpoint R : ℝ) a := by
  have hRX : R - 1 ≤ squareRootEndpoint R := by
    have hr2 : R ≤ R ^ 2 := by nlinarith
    unfold squareRootEndpoint
    omega
  have hRmin : 1 ≤ R - 1 := by omega
  have hXmin : 1 ≤ squareRootEndpoint R := by omega
  have hcast : ((R - 1 : ℕ) : ℝ) ≤ (squareRootEndpoint R : ℝ) := by
    exact_mod_cast hRX
  have hpowers :
      Real.rpow ((R - 1 : ℕ) : ℝ) a ≤
        Real.rpow (squareRootEndpoint R : ℝ) a :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hcast ha
  rw [squareRootCanonicalRoughCorrelation_eq_mertens_pred_sub_endpoint R (by omega)]
  calc
    ‖mertensSummatory (R - 1) - mertensSummatory (squareRootEndpoint R)‖ ≤
      ‖mertensSummatory (R - 1)‖ +
        ‖mertensSummatory (squareRootEndpoint R)‖ := norm_sub_le _ _
    _ ≤ C * Real.rpow ((R - 1 : ℕ) : ℝ) a +
          C * Real.rpow (squareRootEndpoint R : ℝ) a :=
        add_le_add (hM (R - 1) hRmin)
          (hM (squareRootEndpoint R) hXmin)
    _ ≤ C * Real.rpow (squareRootEndpoint R : ℝ) a +
          C * Real.rpow (squareRootEndpoint R : ℝ) a := by
        exact add_le_add (mul_le_mul_of_nonneg_left hpowers hC) le_rfl
    _ = (2 * C) * Real.rpow (squareRootEndpoint R : ℝ) a := by ring

/-- Uniform at *any* admissible exponent: 9/4 of the genuine low daughters
    plus a separate power error.  Neither replaces the lower Mertens envelope. -/
theorem physicalRemainder_powerGuidepost_of_mertensPowerBound
    {a : ℝ} (ha : 0 ≤ a)
    (hM : MertensExponent.MertensPowerBound a) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ R : ℕ, 56 ≤ R →
        ‖lowOwnerPhysicalAmplitudeRemainder R 0‖ ^ 2 ≤
          (9 / 4 : ℝ) * canonicalRoughLowQ2DaughterEnergy R +
            (2025 / 1814 : ℝ) *
              (C * Real.rpow (squareRootEndpoint R : ℝ) a) ^ 2 := by
  rcases hM with ⟨C0, hC0, hbound⟩
  refine ⟨2 * C0, by positivity, ?_⟩
  intro R hR
  have hcorr :=
    roughCorrelation_norm_le_of_mertensPowerBound ha hC0 hbound R hR
  have hright : 0 ≤
      (2 * C0) * Real.rpow (squareRootEndpoint R : ℝ) a :=
    mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hsq :
      ‖squareRootCanonicalRoughCorrelation R‖ ^ 2 ≤
        ((2 * C0) * Real.rpow (squareRootEndpoint R : ℝ) a) ^ 2 := by
    have hnorm : 0 ≤ ‖squareRootCanonicalRoughCorrelation R‖ :=
      norm_nonneg _
    nlinarith
  have hphysical :=
    lowOwnerPhysicalRemainder_sq_le_twoPointTwoFive_daughter_add_correlation R hR
  nlinarith

/-- Native 7/8 consumer: hM is the ACTUAL certified OpenAI Mertens growth
    theorem supplied by the separate upstream-OAI kernel-check workflow.
    Generic research CI must not import the upstream OAI package. -/
theorem physicalRemainder_sevenEighths_of_mertensGrowth
    (hM : MertensExponent.MertensGrowthAtMost ((7 : ℝ) / 8))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ R : ℕ, 56 ≤ R →
        ‖lowOwnerPhysicalAmplitudeRemainder R 0‖ ^ 2 ≤
          (9 / 4 : ℝ) * canonicalRoughLowQ2DaughterEnergy R +
            (2025 / 1814 : ℝ) *
              (C * Real.rpow (squareRootEndpoint R : ℝ)
                ((7 : ℝ) / 8 + ε)) ^ 2 := by
  exact physicalRemainder_powerGuidepost_of_mertensPowerBound
    (a := (7 : ℝ) / 8 + ε) (by linarith) (hM ε hε)

#print axioms roughCorrelation_norm_le_of_mertensPowerBound
#print axioms physicalRemainder_powerGuidepost_of_mertensPowerBound
#print axioms physicalRemainder_sevenEighths_of_mertensGrowth

end RHLean.Proof
