
import Mathlib
import «research.GLOBAL_RETURNED_CORE_RECIPROCAL_PREFIX_FIRST_OWNER_ENERGY»
import «research.GLOBAL_RETURNED_CORE_ROOT_PREFIX_FIRST_OWNER_ENERGY»
import «research.GLOBAL_RETURNED_CORE_THRESHOLD_INCIDENCE_KERNEL»

/-!
# Threshold potential global energy

The finite threshold potential is the single scalar coordinate

  F_R = reciprocal-q2-prefix - root-prefix = AMP-weight - 1.

Its one-dimensional signed amplitude is therefore

  sum_n F_R(n) mu(n) = reciprocalColumn(R) - M(R-1).

This keeps every q-q' covariance term assembled and puts the root channel in the
same amplitude before squaring.  The q2 column costs at most one quarter of the
recursive daughter energy, while the predecessor Mertens square is controlled
by the live lower envelope.

Because subtracting the constant mode does not change a fresh-prime owner
difference, the complete fresh-prime four-corner of F_R is exactly the complete
fresh-prime four-corner of the actual AMP weight.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

def lowOwnerThresholdPotentialSignedSite (R n : ℕ) : ℝ :=
  lowOwnerThresholdPotential R n * realMoebiusStep n

theorem lowOwnerThresholdPotentialSignedSite_eq_prefix_sub_root
    (R n : ℕ) :
    lowOwnerThresholdPotentialSignedSite R n =
      lowOwnerReciprocalPrefixSignedSite R n -
        lowOwnerRootPrefixSignedSite R n := by
  unfold lowOwnerThresholdPotentialSignedSite
    lowOwnerThresholdPotential
    lowOwnerReciprocalPrefixSignedSite
    lowOwnerRootPrefixSignedSite
    lowOwnerRootPrefixWeight
  ring

theorem sum_lowOwnerThresholdPotentialSignedSite_eq_column_sub_mertensPred
    {R : ℕ} (hR : 2 ≤ R) :
    (∑ n ∈ lowOwnerNonzeroMobiusCarrier R,
      lowOwnerThresholdPotentialSignedSite R n) =
      lowOwnerReciprocalMertensColumnReal R -
        (mertensSummatoryInt (R - 1) : ℝ) := by
  simp_rw [lowOwnerThresholdPotentialSignedSite_eq_prefix_sub_root]
  rw [Finset.sum_sub_distrib,
    sum_lowOwnerReciprocalPrefixSignedSite_eq_column,
    sum_lowOwnerRootPrefixSignedSite_eq_mertensPred hR]

theorem lowOwnerThresholdPotential_emptyEnergy_eq_amplitude_sq
    {R : ℕ} (hR : 2 ≤ R) :
    lowOwnerRevealedPairMassWith R ∅
        (lowOwnerThresholdPotentialSignedSite R) =
      (lowOwnerReciprocalMertensColumnReal R -
        (mertensSummatoryInt (R - 1) : ℝ)) ^ 2 := by
  rw [lowOwnerRevealedPairMassWith_empty_eq_sum_sq]
  rw [sum_lowOwnerThresholdPotentialSignedSite_eq_column_sub_mertensPred hR]

theorem lowOwnerThresholdPotential_emptyEnergy_le_half_q2_add_eight_root
    {R : ℕ} {K : ℝ} (hR : 2 ≤ R)
    (hK : LowerMertensCriticalEnvelope R K) :
    lowOwnerRevealedPairMassWith R ∅
        (lowOwnerThresholdPotentialSignedSite R) ≤
      (1 / 2 : ℝ) * canonicalRoughLowQ2DaughterEnergy R +
        8 * (R : ℝ) * K := by
  rw [lowOwnerThresholdPotential_emptyEnergy_eq_amplitude_sq hR]
  have hcol :=
    lowOwnerReciprocalMertensColumnReal_sq_le_quarter_lowQ2DaughterEnergy R
  have hroot :=
    mertensPred_sq_le_four_root_mul_lowerEnvelope hR hK
  have hquad :
      (lowOwnerReciprocalMertensColumnReal R -
          (mertensSummatoryInt (R - 1) : ℝ)) ^ 2 ≤
        2 * lowOwnerReciprocalMertensColumnReal R ^ 2 +
          2 * (mertensSummatoryInt (R - 1) : ℝ) ^ 2 := by
    nlinarith [sq_nonneg
      (lowOwnerReciprocalMertensColumnReal R +
        (mertensSummatoryInt (R - 1) : ℝ))]
  nlinarith

theorem sum_lowOwnerThresholdPotential_firstOwnerMass_le_half_q2_add_eight_root
    {R : ℕ} {K : ℝ} (hR : 2 ≤ R)
    (hK : LowerMertensCriticalEnvelope R K) :
    (∑ p ∈ primesUpTo (squareRootEndpoint R),
      lowOwnerGlobalFirstOwnerPairMassWith R p
        (lowOwnerThresholdPotentialSignedSite R)) ≤
      (1 / 2 : ℝ) * canonicalRoughLowQ2DaughterEnergy R +
        8 * (R : ℝ) * K := by
  exact
    (sum_lowOwnerGlobalFirstOwnerPairMassWith_le_emptyEnergy
      R (lowOwnerThresholdPotentialSignedSite R)).trans
      (lowOwnerThresholdPotential_emptyEnergy_le_half_q2_add_eight_root hR hK)

theorem sum_lowOwnerThresholdPotential_cellMass_le_quarter_q2_add_four_root
    {R : ℕ} {K : ℝ} (hR : 2 ≤ R)
    (hK : LowerMertensCriticalEnvelope R K) :
    (∑ p ∈ primesUpTo (squareRootEndpoint R),
      ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
        lowOwnerFirstOwnerCellGramWith R p sig
          (lowOwnerThresholdPotentialSignedSite R)) ≤
      (1 / 4 : ℝ) * canonicalRoughLowQ2DaughterEnergy R +
        4 * (R : ℝ) * K := by
  have hfirst :=
    sum_lowOwnerThresholdPotential_firstOwnerMass_le_half_q2_add_eight_root
      hR hK
  have hrewrite :
      (∑ p ∈ primesUpTo (squareRootEndpoint R),
        lowOwnerGlobalFirstOwnerPairMassWith R p
          (lowOwnerThresholdPotentialSignedSite R)) =
        2 * (∑ p ∈ primesUpTo (squareRootEndpoint R),
          ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
            lowOwnerFirstOwnerCellGramWith R p sig
              (lowOwnerThresholdPotentialSignedSite R)) := by
    calc
      (∑ p ∈ primesUpTo (squareRootEndpoint R),
        lowOwnerGlobalFirstOwnerPairMassWith R p
          (lowOwnerThresholdPotentialSignedSite R)) =
        ∑ p ∈ primesUpTo (squareRootEndpoint R),
          2 * (∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
            lowOwnerFirstOwnerCellGramWith R p sig
              (lowOwnerThresholdPotentialSignedSite R)) := by
          apply Finset.sum_congr rfl
          intro p hp
          exact lowOwnerGlobalFirstOwnerPairMassWith_eq_two_sum_cells
            (mem_primesUpTo.mp hp).1
            (lowOwnerThresholdPotentialSignedSite R)
      _ = 2 * (∑ p ∈ primesUpTo (squareRootEndpoint R),
          ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
            lowOwnerFirstOwnerCellGramWith R p sig
              (lowOwnerThresholdPotentialSignedSite R)) := by
          rw [Finset.mul_sum]
  rw [hrewrite] at hfirst
  nlinarith

theorem lowOwnerThresholdPotentialFourCorner_eq_actualAMPFourCorner
    {R p a b : ℕ}
    (hp : p.Prime) (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b) :
    weightedMoebiusFreshPrimeFourCornerMass
        (lowOwnerThresholdPotential R) p a b =
      weightedMoebiusFreshPrimeFourCornerMass
        (lowOwnerZeroFrequencyMobiusWeight R) p a b := by
  rw [weightedMoebiusFreshPrimeFourCornerMass_eq_ownerDifferences
      (lowOwnerThresholdPotential R) hp hpa hpb,
    weightedMoebiusFreshPrimeFourCornerMass_eq_ownerDifferences
      (lowOwnerZeroFrequencyMobiusWeight R) hp hpa hpb]
  rw [lowOwnerThresholdPotential_sub_mul hp.one_le,
    lowOwnerZeroFrequencyMobiusWeight_sub_mul hp.one_le,
    lowOwnerThresholdPotential_sub_mul hp.one_le,
    lowOwnerZeroFrequencyMobiusWeight_sub_mul hp.one_le]

theorem lowOwnerThresholdPotentialFourCorner_eq_crossingProduct
    {R p a b : ℕ}
    (hp : p.Prime) (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b) :
    weightedMoebiusFreshPrimeFourCornerMass
        (lowOwnerThresholdPotential R) p a b =
      postRootZeroTargetPairExcess (a, b) *
        (lowOwnerDaughterCrossingWeight R p a -
          lowOwnerRootCrossingIndicator R p a) *
        (lowOwnerDaughterCrossingWeight R p b -
          lowOwnerRootCrossingIndicator R p b) := by
  rw [lowOwnerThresholdPotentialFourCorner_eq_actualAMPFourCorner hp hpa hpb]
  exact lowOwnerZeroFrequencyFreshPrimeFourCorner_eq_crossingProduct hp hpa hpb

end RHLean.Proof
