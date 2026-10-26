import Mathlib
import «research.CORR4_OAI_RELAXED_REMAINDER_20261024»
import «research.ODD_PRIME_COMPOSITE_GAP_BASEL_20261025»

/-!
# Sharp frame-only inverse obstruction for CORR-4

The merged odd-prime frame has constant
`b₇ = 1565172113 / 7214407200`.  This file proves the sharp scalar
consequence of that unsigned information and specializes it to the literal
CORR-4 parent, daughter energy, and complete physical remainder.

The result is an inverse obstruction, not a signed estimate: any excess of the
physical remainder above `(9/4) E_R` must be paid by the square-endpoint
correlation.  It does not prove the open physical-remainder bound or a Mertens
exponent improvement.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- The genuine low-owner critical synthesis inherits the merged composite-gap
odd-prime frame constant. -/
theorem lowOwnerCriticalSynthesis_energy_le_compositeGap
    (R : ℕ) (tau : ℝ) :
    ‖lowOwnerCriticalMertensSynthesis R tau‖ ^ 2 ≤
      (1565172113 / 7214407200 : ℝ) *
        canonicalRoughLowQ2DaughterEnergy R := by
  have hsub : canonicalRoughLowQ2Owners R ⊆
      (primesUpTo (R - 1)).erase 2 := Finset.sdiff_subset
  have hpos : ∀ q ∈ canonicalRoughLowQ2Owners R, 0 < q := by
    intro q hq
    exact (mem_primesUpTo.mp (Finset.mem_erase.mp (hsub hq)).2).1.pos
  have hbudget :
      (∑ q ∈ canonicalRoughLowQ2Owners R, (1 : ℝ) / (q : ℝ) ^ 2) ≤
        (1565172113 / 7214407200 : ℝ) := by
    calc
      _ ≤ ∑ q ∈ (primesUpTo (R - 1)).erase 2,
          (1 : ℝ) / (q : ℝ) ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro q _hq _hnot
        positivity
      _ ≤ (1565172113 / 7214407200 : ℝ) :=
        oddPrimeOwnerReciprocalSquareBudgetReal_le_compositeGap (R - 1)
  have hframe := stableFarCriticalQ2Synthesis_energy_le_reciprocalSquareBudget
    tau (canonicalRoughLowQ2Owners R) (lowOwnerRawMertensAmplitude R) hpos
  simp only [norm_sq_lowOwnerRawMertensAmplitude] at hframe
  change ‖lowOwnerCriticalMertensSynthesis R tau‖ ^ 2 ≤
    (∑ q ∈ canonicalRoughLowQ2Owners R, (1 : ℝ) / (q : ℝ) ^ 2) *
      canonicalRoughLowQ2DaughterEnergy R at hframe
  exact hframe.trans (mul_le_mul_of_nonneg_right hbudget
    (canonicalRoughLowQ2DaughterEnergy_nonneg R))

/-- Sharp fixed-constant Young inequality behind the frame-only obstruction.
Equality is possible in the scalar abstraction when the frame is saturated and
`v` is antiparallel to `u` with the extremal norm ratio. -/
theorem norm_sub_sq_sub_twoPointTwoFive_energy_le_compositeGap
    (u v : ℂ) (E : ℝ)
    (hv : ‖v‖ ^ 2 ≤
      (1565172113 / 7214407200 : ℝ) * E) :
    ‖u - v‖ ^ 2 - (9 / 4 : ℝ) * E ≤
      (16232416200 / 14667244087 : ℝ) * ‖u‖ ^ 2 := by
  have ht := norm_sub_le u v
  have hu := norm_nonneg u
  have hv0 := norm_nonneg v
  have huv := norm_nonneg (u - v)
  have hsq : ‖u - v‖ ^ 2 ≤ (‖u‖ + ‖v‖) ^ 2 := by
    nlinarith
  nlinarith [sq_nonneg
    (14667244087 * ‖v‖ - 1565172113 * ‖u‖)]

/-- Literal CORR-4 specialization of the sharp frame-only inverse inequality.

Writing `C_R` for the square-endpoint correlation, `U_R` for the genuine
odd-prime daughter synthesis, `E_R` for its diagonal energy and
`B_R = C_R - U_R` for the complete physical remainder, this is
`|B_R|² - (9/4)E_R ≤ λ₇ |C_R|²`.
It is unconditional but supplies no all-root upper bound for `C_R`. -/
theorem lowOwnerPhysicalRemainder_excess_le_endpointCorrelation
    (R : ℕ) (hR : 56 ≤ R) :
    ‖lowOwnerPhysicalAmplitudeRemainder R 0‖ ^ 2 -
        (9 / 4 : ℝ) * canonicalRoughLowQ2DaughterEnergy R ≤
      (16232416200 / 14667244087 : ℝ) *
        ‖squareRootCanonicalRoughCorrelation R‖ ^ 2 := by
  have hid :=
    squareRootCanonicalRoughCorrelation_eq_criticalSynthesis_add_physicalRemainder
      R hR 0
  have hrearrange :
      lowOwnerPhysicalAmplitudeRemainder R 0 =
        squareRootCanonicalRoughCorrelation R -
          lowOwnerCriticalMertensSynthesis R 0 := by
    rw [hid]
    ring
  have hframe := lowOwnerCriticalSynthesis_energy_le_compositeGap R 0
  have hE := canonicalRoughLowQ2DaughterEnergy_nonneg R
  rw [hrearrange]
  exact norm_sub_sq_sub_twoPointTwoFive_energy_le_compositeGap
    (squareRootCanonicalRoughCorrelation R)
    (lowOwnerCriticalMertensSynthesis R 0)
    (canonicalRoughLowQ2DaughterEnergy R) hframe

/-- The reciprocal sharp constant `κ₇ = 1/λ₇`, useful when reading the
inverse inequality as a forced endpoint excursion. -/
theorem compositeGap_inverse_constants :
    (14667244087 / 16232416200 : ℝ) *
        (16232416200 / 14667244087 : ℝ) = 1 := by
  norm_num

#print axioms lowOwnerCriticalSynthesis_energy_le_compositeGap
#print axioms norm_sub_sq_sub_twoPointTwoFive_energy_le_compositeGap
#print axioms lowOwnerPhysicalRemainder_excess_le_endpointCorrelation
#print axioms compositeGap_inverse_constants

end RHLean.Proof
