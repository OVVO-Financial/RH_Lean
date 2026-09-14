import Mathlib
import «research.LOW_OWNER_PHYSICAL_CENSUS_CORRELATION»

/-!
# Energy transfer between LOW-A correlation and the physical far census

The exact census normal form gives

  Corr_R = Census_R - E_R,
  ||E_R|| <= 8 R.

Hence existence of a fixed finite coefficient on the LOW-A correlation problem
is equivalent, up to a harmless universal factor two and a root-scale boundary
change, to existence of a fixed finite coefficient on the single signed
physical census.  This file records that transfer so subsequent analytic work
can stay entirely on the physical carrier without silently changing the target.

No finite coefficient is produced here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- LOW-A statement directly on the signed physical far census. -/
def LowOwnerPhysicalCensusQ2EnergyStatementWith (A C : ℝ) : Prop :=
  ∀ R : ℕ, ∀ K : ℝ,
    56 ≤ R →
    LowerMertensCriticalEnvelope R K →
    ‖lowOwnerPhysicalFarCensus R‖ ^ 2 ≤
      A * canonicalRoughLowQ2DaughterEnergy R + C * (R : ℝ) ^ 2 * K

private theorem lowerEnvelope_one_le_transfer
    {R : ℕ} {K : ℝ} (hR : 1 ≤ R)
    (hK : LowerMertensCriticalEnvelope R K) :
    1 ≤ K := by
  have h0 := hK.2 0 (by omega)
  have hm0 : mertensSummatoryInt 0 = 0 := by
    simp [mertensSummatoryInt]
  rw [hm0] at h0
  norm_num at h0
  exact h0

private theorem norm_add_sq_le_two_sum_sq (a b : ℂ) :
    ‖a + b‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  have htri : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
  have hnon : 0 ≤ ‖a + b‖ := norm_nonneg _
  have hsum : 0 ≤ ‖a‖ + ‖b‖ := by positivity
  have hsq : ‖a + b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := by
    nlinarith
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

/-- A physical-census estimate gives a correlation LOW-A estimate.  The factor
`2` is deliberately coarse; the point here is exact finite-A equivalence, not
the final factor-four optimization. -/
theorem physicalCensusQ2Energy_implies_correlationLowQ2Energy
    {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hphys : LowOwnerPhysicalCensusQ2EnergyStatementWith A C) :
    CanonicalRoughCorrelationLowQ2EnergyStatementWith
      (2 * A) (2 * C + 128) := by
  intro R K hR hK
  have hP := hphys R K hR hK
  have hroot := norm_frozenTopFarRoughRootCorrection_le_eight_root R hR
  have hrootSq :
      ‖frozenTopFarRoughRootCorrection R‖ ^ 2 ≤ 64 * (R : ℝ) ^ 2 := by
    have hn := norm_nonneg (frozenTopFarRoughRootCorrection R)
    have hR0 : 0 ≤ (R : ℝ) := by positivity
    nlinarith [sq_nonneg (8 * (R : ℝ) -
      ‖frozenTopFarRoughRootCorrection R‖)]
  have hK1 := lowerEnvelope_one_le_transfer (by omega) hK
  have hrootK :
      128 * (R : ℝ) ^ 2 ≤ 128 * (R : ℝ) ^ 2 * K := by
    have hR2 : 0 ≤ 128 * (R : ℝ) ^ 2 := by positivity
    nlinarith
  rw [squareRootCanonicalRoughCorrelation_eq_physicalFarCensus_sub_root R hR]
  have htwo := norm_add_sq_le_two_sum_sq
    (lowOwnerPhysicalFarCensus R)
    (-frozenTopFarRoughRootCorrection R)
  simp only [norm_neg] at htwo
  calc
    ‖lowOwnerPhysicalFarCensus R - frozenTopFarRoughRootCorrection R‖ ^ 2 ≤
        2 * (‖lowOwnerPhysicalFarCensus R‖ ^ 2 +
          ‖frozenTopFarRoughRootCorrection R‖ ^ 2) := by
            simpa [sub_eq_add_neg] using htwo
    _ ≤ 2 * ((A * canonicalRoughLowQ2DaughterEnergy R +
          C * (R : ℝ) ^ 2 * K) + 64 * (R : ℝ) ^ 2) := by
            gcongr
    _ ≤ (2 * A) * canonicalRoughLowQ2DaughterEnergy R +
          (2 * C + 128) * (R : ℝ) ^ 2 * K := by
            nlinarith

/-- Conversely, a correlation LOW-A estimate controls the same physical census
with the same universal factor-two loss. -/
theorem correlationLowQ2Energy_implies_physicalCensusQ2Energy
    {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hcorr : CanonicalRoughCorrelationLowQ2EnergyStatementWith A C) :
    LowOwnerPhysicalCensusQ2EnergyStatementWith
      (2 * A) (2 * C + 128) := by
  intro R K hR hK
  have hCorr := hcorr R K hR hK
  have hroot := norm_frozenTopFarRoughRootCorrection_le_eight_root R hR
  have hrootSq :
      ‖frozenTopFarRoughRootCorrection R‖ ^ 2 ≤ 64 * (R : ℝ) ^ 2 := by
    have hn := norm_nonneg (frozenTopFarRoughRootCorrection R)
    have hR0 : 0 ≤ (R : ℝ) := by positivity
    nlinarith [sq_nonneg (8 * (R : ℝ) -
      ‖frozenTopFarRoughRootCorrection R‖)]
  have hK1 := lowerEnvelope_one_le_transfer (by omega) hK
  have hrootK :
      128 * (R : ℝ) ^ 2 ≤ 128 * (R : ℝ) ^ 2 * K := by
    have hR2 : 0 ≤ 128 * (R : ℝ) ^ 2 := by positivity
    nlinarith
  have hrepr :=
    squareRootCanonicalRoughCorrelation_eq_physicalFarCensus_sub_root R hR
  have hsum :
      lowOwnerPhysicalFarCensus R =
        squareRootCanonicalRoughCorrelation R +
          frozenTopFarRoughRootCorrection R := by
    linear_combination hrepr
  rw [hsum]
  have htwo := norm_add_sq_le_two_sum_sq
    (squareRootCanonicalRoughCorrelation R)
    (frozenTopFarRoughRootCorrection R)
  calc
    ‖squareRootCanonicalRoughCorrelation R +
        frozenTopFarRoughRootCorrection R‖ ^ 2 ≤
      2 * (‖squareRootCanonicalRoughCorrelation R‖ ^ 2 +
        ‖frozenTopFarRoughRootCorrection R‖ ^ 2) := htwo
    _ ≤ 2 * ((A * canonicalRoughLowQ2DaughterEnergy R +
          C * (R : ℝ) ^ 2 * K) + 64 * (R : ℝ) ^ 2) := by
            gcongr
    _ ≤ (2 * A) * canonicalRoughLowQ2DaughterEnergy R +
          (2 * C + 128) * (R : ℝ) ^ 2 * K := by
            nlinarith

/-- Existence of some fixed finite LOW-A coefficient is therefore a coordinate-
invariant question between the correlation and the signed physical census. -/
theorem exists_correlationLowQ2Energy_iff_exists_physicalCensusQ2Energy :
    (∃ A C : ℝ, 0 ≤ A ∧ 0 ≤ C ∧
        CanonicalRoughCorrelationLowQ2EnergyStatementWith A C) ↔
      (∃ A C : ℝ, 0 ≤ A ∧ 0 ≤ C ∧
        LowOwnerPhysicalCensusQ2EnergyStatementWith A C) := by
  constructor
  · rintro ⟨A, C, hA, hC, hcorr⟩
    refine ⟨2 * A, 2 * C + 128, by positivity, by positivity, ?_⟩
    exact correlationLowQ2Energy_implies_physicalCensusQ2Energy hA hC hcorr
  · rintro ⟨A, C, hA, hC, hphys⟩
    refine ⟨2 * A, 2 * C + 128, by positivity, by positivity, ?_⟩
    exact physicalCensusQ2Energy_implies_correlationLowQ2Energy hA hC hphys

end RHLean.Proof
