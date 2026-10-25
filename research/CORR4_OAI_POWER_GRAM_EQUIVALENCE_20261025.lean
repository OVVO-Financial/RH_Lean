import Mathlib
import «research.CORR4_OAI_POWER_RENEWAL_20261025»
import «research.MERTENS_EXPONENT_ENVELOPES»

/-!
# CORR-4 power Gram: exact unconditional reverse direction

The full first-owner Gram power hypothesis is exactly equivalent to the
full original weighted physical remainder power hypothesis.

Any independently established all-integer Mertens power bound implies the
matching physical remainder/Gram bound. Its reverse strong induction is not
assumed here and will be handled separately. No proof holes are introduced.
-/

noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHLean.Proof
open RHLean.Analysis RHLean.Arithmetic
attribute [local instance] Classical.propDecidable

/-- Full physical unique-first-owner signed Co-minus-Div power bill. -/
def Corr4PowerFirstOwnerGram (A β : ℝ) : Prop :=
  ∀ R : ℕ, 56 ≤ R →
    2 * (∑ p ∈ primesUpTo (squareRootEndpoint R),
      lowOwnerZeroFrequencyFirstOwnerGram R p) ≤
        (9 / 4 : ℝ) * canonicalRoughLowQ2DaughterEnergy R +
          A * Real.rpow (R : ℝ) (4 * β) -
            lowOwnerZeroFrequencyMobiusDiagonal R

theorem corr4PowerFirstOwnerGram_iff_powerPhysicalRemainder
    (A β : ℝ) :
    Corr4PowerFirstOwnerGram A β ↔ Corr4PowerPhysicalRemainder A β := by
  constructor
  · intro h R hR
    have hsq :=
      norm_sq_lowOwnerPhysicalAmplitudeRemainder_zero_eq_diagonal_add_firstOwners
        R hR
    have hh := h R hR
    rw [hsq]
    linarith
  · intro h R hR
    have hsq :=
      norm_sq_lowOwnerPhysicalAmplitudeRemainder_zero_eq_diagonal_add_firstOwners
        R hR
    have hh := h R hR
    rw [hsq] at hh
    linarith

/-- Exponent conversion at the unchanged original square scale. -/
private theorem corr4_rpow_square_sq
    (R : ℕ) (β : ℝ) :
    (Real.rpow ((R : ℝ) ^ 2) β) ^ 2 =
      Real.rpow (R : ℝ) (4 * β) := by
  have hR : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have htwo :
      Real.rpow (R : ℝ) (2 : ℝ) = (R : ℝ) ^ (2 : ℕ) :=
    Real.rpow_natCast (R : ℝ) 2
  have hsq :
      Real.rpow ((R : ℝ) ^ 2) β =
        Real.rpow (R : ℝ) (2 * β) := by
    calc
      Real.rpow ((R : ℝ) ^ 2) β =
          Real.rpow (Real.rpow (R : ℝ) 2) β := by rw [htwo]
      _ = Real.rpow (R : ℝ) (2 * β) :=
        (Real.rpow_mul hR (2 : ℝ) β).symm
  rw [hsq]
  calc
    (Real.rpow (R : ℝ) (2 * β)) ^ 2 =
        Real.rpow (Real.rpow (R : ℝ) (2 * β)) 2 := by
          rw [Real.rpow_natCast]
    _ = Real.rpow (R : ℝ) ((2 * β) * 2) :=
      (Real.rpow_mul hR (2 * β) 2).symm
    _ = Real.rpow (R : ℝ) (4 * β) := by congr 1; ring

/-- Any actual all-integer Mertens bound gives the complete physical power
    remainder, with no new analytic assumption. -/
theorem corr4PowerPhysicalRemainder_of_mertensPowerBound
    {β : ℝ} (hβ : 0 ≤ β)
    (hM : MertensExponent.MertensPowerBound β) :
    ∃ A : ℝ, 0 ≤ A ∧ Corr4PowerPhysicalRemainder A β := by
  obtain ⟨C, hC, hbound⟩ := hM
  let A : ℝ := (2025 / 1814 : ℝ) * (2 * C) ^ 2
  refine ⟨A, by dsimp [A]; positivity, ?_⟩
  intro R hR
  have hcorr := roughCorrelation_norm_le_of_mertensPowerBound hβ hC hbound R hR
  have hX : (squareRootEndpoint R : ℝ) ≤ (R : ℝ) ^ 2 := by
    have hn : squareRootEndpoint R ≤ R ^ 2 := by
      unfold squareRootEndpoint
      omega
    exact_mod_cast hn
  have hp :
      Real.rpow (squareRootEndpoint R : ℝ) β ≤
        Real.rpow ((R : ℝ) ^ 2) β :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hX hβ
  have hpC :
      2 * C * Real.rpow (squareRootEndpoint R : ℝ) β ≤
        2 * C * Real.rpow ((R : ℝ) ^ 2) β :=
    mul_le_mul_of_nonneg_left hp (by positivity)
  have hnorm : 0 ≤ ‖squareRootCanonicalRoughCorrelation R‖ := norm_nonneg _
  have hpnonneg :
      0 ≤ 2 * C * Real.rpow ((R : ℝ) ^ 2) β :=
    mul_nonneg (by positivity) (Real.rpow_nonneg (sq_nonneg _) _)
  have hcorr2 :
      ‖squareRootCanonicalRoughCorrelation R‖ ^ 2 ≤
        (2 * C * Real.rpow ((R : ℝ) ^ 2) β) ^ 2 := by
    nlinarith
  have hphysical :=
    lowOwnerPhysicalRemainder_sq_le_twoPointTwoFive_daughter_add_correlation R hR
  have hfour := corr4_rpow_square_sq R β
  dsimp [A]
  nlinarith [sq_nonneg (Real.rpow ((R : ℝ) ^ 2) β)]

theorem corr4PowerFirstOwnerGram_of_mertensPowerBound
    {β : ℝ} (hβ : 0 ≤ β)
    (hM : MertensExponent.MertensPowerBound β) :
    ∃ A : ℝ, 0 ≤ A ∧ Corr4PowerFirstOwnerGram A β := by
  obtain ⟨A, hA, hB⟩ :=
    corr4PowerPhysicalRemainder_of_mertensPowerBound hβ hM
  exact ⟨A, hA,
    (corr4PowerFirstOwnerGram_iff_powerPhysicalRemainder A β).mpr hB⟩

#print axioms corr4PowerFirstOwnerGram_iff_powerPhysicalRemainder
#print axioms corr4PowerPhysicalRemainder_of_mertensPowerBound
#print axioms corr4PowerFirstOwnerGram_of_mertensPowerBound

end RHLean.Proof
