import Mathlib
import «research.VF_MID_THIRTY_FACTOR_RANGE_LOWER_GATE»

/-!
# Adaptive frozen factor-wheel budget: an entire infinite family of finite wheels

The wheel-30 proof is the first exact base case, but fixing a small modulus
forever is not the only option.  On any run [A,B), freeze a larger factor
prefix z at its STARTING anchor A. Its Boolean cube has exactly
2^(primesUpTo z).card faces, and the already compiled four-endpoint
wheel theorem bounds its ENTIRE cumulative phase by FOUR times this face
count, independently of B-A.

If 2^(# primes <= z) <= A, then the transition from the full native VF
tracking defect to the genuine p>z least-prime-owner late-removal
currency costs no more than 4A. The historical RH-scale wall allows
K A log A, so a controlled face budget is asymptotically smaller.

The final signed p>z owner-return restriction is OPEN.
This module constructs the exact necessary/sufficient obstruction.
It does NOT assume that finitely many prime distribution tests generalize.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

/-- A source-native admissibility rule for a locally frozen factor prefix.
This refers ONLY to the finite prime-coordinate list, never to
Nat.primeCounting at a square endpoint. It controls the *number of
Boolean inclusion-exclusion faces* rather than imposing RH-scale tracking. -/
def VFMidAdaptiveFrozenFaceBudget (z A : ℕ) : Prop :=
  z ≤ A ∧ 2 ^ (primesUpTo z).card ≤ A

/-- Uniform exact signed transfer for arbitrary frozen factor cutoffs.
Nothing probabilistic, Li-based or RH-equivalent is assumed. -/
theorem vfMidAdaptiveOwnerResidual_sub_nativeTracking_eq_phase
    (z A B : ℕ) (hA : 2 ≤ A) (hAB : A ≤ B) :
    (vfMidDyadicLateRemoval z A B -
        vfMidDyadicLateReference z A B) -
          vfMidDyadicVFTrackingDefect A B =
      vfMidDyadicPrefixSupply z A B -
        vfMidPrefixWheelDensity z * vfMidDyadicInteriorLength A B := by
  rw [vfMidDyadicVFTrackingDefect_eq_vfMass_sub_primeSupply
    A B hA hAB]
  unfold vfMidDyadicLateRemoval vfMidDyadicLateReference
  ring

/-- A controlled, possibly much larger, frozen factor wheel translates
into a physical p>z signed-owner ledger with at most 4A error across
ARBITRARILY MANY square blocks. The bound is INDEPENDENT of B-A. -/
theorem vfMidAdaptiveOwnerResidual_sub_nativeTracking_abs_le_four_anchor
    (z A B : ℕ) (hA : 2 ≤ A) (hAB : A ≤ B)
    (hbudget : VFMidAdaptiveFrozenFaceBudget z A) :
    |(vfMidDyadicLateRemoval z A B -
        vfMidDyadicLateReference z A B) -
          vfMidDyadicVFTrackingDefect A B| ≤ 4 * (A : ℝ) := by
  rw [vfMidAdaptiveOwnerResidual_sub_nativeTracking_eq_phase
    z A B hA hAB]
  exact abs_vfMidDyadicPrefixSupply_sub_density_le_four_mul_A
    hbudget.2

/-- Quantify a lower first-bad wall breach as a large PHYSICAL signed
owner overrun for ANY cutoff z with only a 4A Boolean-face cost.
This is an exact alternative to the special 30-wheel's sharper
32-count phase, trading a larger phase allowance for the removal
of more low-prime owner coordinates. -/
theorem vfMidAdaptiveFirstLowerBreach_forces_ownerReturnOverrun
    (K : ℝ) {z A B : ℕ}
    (hA : 5 ≤ A) (hAB : A ≤ B)
    (hbudget : VFMidAdaptiveFrozenFaceBudget z A)
    (hgood : VFMidThirtyLowerFactorSafe K A)
    (hbad : ¬ VFMidThirtyLowerFactorSafe K B) :
    vfMidThirtyLowerHistoricalSlack K A +
        K * ((B : ℝ) * Real.log (B : ℝ) -
          (A : ℝ) * Real.log (A : ℝ)) -
          4 * (A : ℝ) <
      vfMidDyadicLateRemoval z A B -
        vfMidDyadicLateReference z A B := by
  have hover :=
    vfMidThirtyFirstLowerBreach_forces_factorRunOverrun
      K hA hAB hgood hbad
  rw [vfMidThirtyRunExcess_eq_nativeTracking hA hAB] at hover
  have hphase :=
    vfMidAdaptiveOwnerResidual_sub_nativeTracking_abs_le_four_anchor
      z A B (by omega : 2 ≤ A) hAB hbudget
  have hlower := (abs_le.mp hphase).1
  linarith

/-- Wiles-style proof-contract consumer: an independently established
signed physical p>z owner-return upper bound (with the exact historical
slack and face budget) EXCLUDES a lower first bad event. This proof
is a finite contradiction, not the missing bound itself. -/
theorem vfMidAdaptiveLowerSafe_of_physicalReturnUpper
    (K : ℝ) {z A B : ℕ}
    (hA : 5 ≤ A) (hAB : A ≤ B)
    (hbudget : VFMidAdaptiveFrozenFaceBudget z A)
    (hgood : VFMidThirtyLowerFactorSafe K A)
    (hreturn :
      vfMidDyadicLateRemoval z A B -
          vfMidDyadicLateReference z A B ≤
        vfMidThirtyLowerHistoricalSlack K A +
          K * ((B : ℝ) * Real.log (B : ℝ) -
            (A : ℝ) * Real.log (A : ℝ)) -
          4 * (A : ℝ)) :
    VFMidThirtyLowerFactorSafe K B := by
  by_contra hbad
  have hcontradiction :=
    vfMidAdaptiveFirstLowerBreach_forces_ownerReturnOverrun
      K hA hAB hbudget hgood hbad
  linarith

end RHLean.Analysis
