import Mathlib
import «research.GLOBAL_RETURNED_CORE_RECIPROCAL_PREFIX_FIRST_OWNER_ENERGY»
import «research.GLOBAL_RETURNED_CORE_POST789_DIAGONAL_SUBTRACTED_CONTROL»

/-!
# Exact reciprocal-prefix / far-tail split of the signed cell telescope

The zero-frequency AMP site is the sum of two literal signed sites:

  AMP = reciprocal q^2 prefix + far tail.

Because the first-owner cell Gram is bilinear, every signed cell telescope
splits exactly into

  2 * reciprocal-prefix cell Gram + 2 * far-tail/mixed cell mass.

The reciprocal-prefix part is already controlled globally by the new
first-owner Fubini at coefficient 1/8 before the factor two, hence 1/4 in
FinalStokes currency.  No estimate is made on the far-tail/mixed remainder in
this file.

Consequently the full RH consumer now needs only a 3/2 q^2-energy bound on that
single signed remainder (plus C R^2 K).  This isolates the genuinely unresolved
endpoint correlation after the recursive q^2 energy has already been paid.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Signed far-tail site on the common Mobius clock. -/
def lowOwnerFarTailSignedSite (R n : ℕ) : ℝ :=
  lowOwnerFarTailWeight R n * realMoebiusStep n

/-- The actual AMP site is exactly reciprocal prefix plus far tail. -/
theorem lowOwnerZeroFrequencyMobiusSite_eq_prefix_add_farTail
    (R n : ℕ) :
    lowOwnerZeroFrequencyMobiusSite R n =
      lowOwnerReciprocalPrefixSignedSite R n +
        lowOwnerFarTailSignedSite R n := by
  unfold lowOwnerZeroFrequencyMobiusSite
    lowOwnerZeroFrequencyMobiusWeight
    lowOwnerReciprocalPrefixSignedSite
    lowOwnerFarTailSignedSite
  ring

/-- The part of one oriented first-owner cell Gram containing at least one
far-tail factor.  It contains both prefix/tail cross terms and the tail/tail
term, with all signs retained. -/
def lowOwnerFirstOwnerPrefixTailMixedCell
    (R p : ℕ) (sig : Finset ℕ) : ℝ :=
  ∑ ab ∈ (lowOwnerFirstOwnerBaseFiber R p sig).product
      (lowOwnerFirstOwnerChildFiber R p sig),
    (lowOwnerReciprocalPrefixSignedSite R ab.1 *
        lowOwnerFarTailSignedSite R ab.2 +
      lowOwnerFarTailSignedSite R ab.1 *
        lowOwnerReciprocalPrefixSignedSite R ab.2 +
      lowOwnerFarTailSignedSite R ab.1 *
        lowOwnerFarTailSignedSite R ab.2)

/-- **Exact cell split.**

No inequality is used: the original AMP cell Gram is one reciprocal-prefix
cell Gram plus the signed far-tail/mixed remainder. -/
theorem lowOwnerFirstOwnerCellGram_eq_prefix_add_tailMixed
    (R p : ℕ) (sig : Finset ℕ) :
    lowOwnerFirstOwnerCellGram R p sig =
      lowOwnerFirstOwnerCellGramWith R p sig
        (lowOwnerReciprocalPrefixSignedSite R) +
      lowOwnerFirstOwnerPrefixTailMixedCell R p sig := by
  rw [lowOwnerFirstOwnerCellGram_eq_sum_product]
  unfold lowOwnerFirstOwnerCellGramWith
    lowOwnerFirstOwnerPrefixTailMixedCell
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ab _hab
  rw [lowOwnerZeroFrequencyMobiusSite_eq_prefix_add_farTail,
    lowOwnerZeroFrequencyMobiusSite_eq_prefix_add_farTail]
  ring

/-- Globally assembled reciprocal-prefix oriented cell mass. -/
def lowOwnerReciprocalPrefixRawCellMass (R : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo (squareRootEndpoint R),
    ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
      lowOwnerFirstOwnerCellGramWith R p sig
        (lowOwnerReciprocalPrefixSignedSite R)

/-- Globally assembled signed remainder containing at least one far-tail
factor.  Chronology and signatures remain fully assembled. -/
def lowOwnerPrefixTailMixedRawCellMass (R : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo (squareRootEndpoint R),
    ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
      lowOwnerFirstOwnerPrefixTailMixedCell R p sig

/-- Global ordinary cell mass splits exactly into prefix and tail/mixed pieces. -/
theorem sum_lowOwnerFirstOwnerCellGram_eq_prefix_add_tailMixed
    (R : ℕ) :
    (∑ p ∈ primesUpTo (squareRootEndpoint R),
      ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
        lowOwnerFirstOwnerCellGram R p sig) =
      lowOwnerReciprocalPrefixRawCellMass R +
        lowOwnerPrefixTailMixedRawCellMass R := by
  unfold lowOwnerReciprocalPrefixRawCellMass
    lowOwnerPrefixTailMixedRawCellMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _hp
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro sig _hsig
  exact lowOwnerFirstOwnerCellGram_eq_prefix_add_tailMixed R p sig

/-- **Exact signed-cell split.**

The full signed-cell assembly is twice the reciprocal-prefix raw cell mass plus
twice the far-tail/mixed raw cell mass. -/
theorem sum_lowOwnerFirstOwnerSignedCellTelescope_eq_prefix_add_tailMixed
    (R : ℕ) :
    (∑ p ∈ primesUpTo (squareRootEndpoint R),
      ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
        lowOwnerFirstOwnerSignedCellTelescope R p sig) =
      2 * lowOwnerReciprocalPrefixRawCellMass R +
        2 * lowOwnerPrefixTailMixedRawCellMass R := by
  have hsigned :
      (∑ p ∈ primesUpTo (squareRootEndpoint R),
        ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
          lowOwnerFirstOwnerSignedCellTelescope R p sig) =
        2 * (∑ p ∈ primesUpTo (squareRootEndpoint R),
          ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
            lowOwnerFirstOwnerCellGram R p sig) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro sig _hsig
    exact
      (two_mul_lowOwnerFirstOwnerCellGram_eq_completeTelescope_sub_clippedCross
        (mem_primesUpTo.mp hp).1).symm
  rw [hsigned, sum_lowOwnerFirstOwnerCellGram_eq_prefix_add_tailMixed]
  ring

/-- The reciprocal-prefix part of FinalStokes costs only one quarter of the
recursive q^2 daughter energy after the signed-cell factor two. -/
theorem two_mul_lowOwnerReciprocalPrefixRawCellMass_le_quarter_q2Energy
    (R : ℕ) :
    2 * lowOwnerReciprocalPrefixRawCellMass R ≤
      (1 / 4 : ℝ) * canonicalRoughLowQ2DaughterEnergy R := by
  have h :=
    sum_lowOwnerReciprocalPrefix_cellMass_le_eighth_q2Energy R
  unfold lowOwnerReciprocalPrefixRawCellMass
  nlinarith

/-- Quantitative target left after the reciprocal-prefix contribution has been
paid.  The coefficient 3/2 is sufficient because prefix already costs 1/4,
giving the final admissible 7/4. -/
def LowOwnerPrefixTailMixedQ2EnergyBound (B C : ℝ) : Prop :=
  ∀ R : ℕ, ∀ K : ℝ,
    56 ≤ R →
    LowerMertensCriticalEnvelope R K →
    2 * lowOwnerPrefixTailMixedRawCellMass R ≤
      B * canonicalRoughLowQ2DaughterEnergy R +
        C * (R : ℝ) ^ 2 * K

/-- **Prefix extraction reduces the final-Stokes target from 7/4 to 3/2.** -/
theorem finalStokesQ2EnergyBound_of_prefixTailMixedThreeHalves
    {C : ℝ}
    (hTail : LowOwnerPrefixTailMixedQ2EnergyBound (3 / 2) C) :
    LowOwnerFinalStokesQ2EnergyBound (7 / 4) C := by
  intro R K hR hK
  have hprefix :=
    two_mul_lowOwnerReciprocalPrefixRawCellMass_le_quarter_q2Energy R
  have htail := hTail R K hR hK
  have hsplit :=
    sum_lowOwnerFirstOwnerSignedCellTelescope_eq_prefix_add_tailMixed R
  rw [sum_lowOwnerFirstOwnerSignedCellTelescope_eq_finalStokesBoundary
    (R := R) (by omega : 2 ≤ R)] at hsplit
  rw [hsplit]
  nlinarith

/-- **New name-locked RH seam.**

After exact q^2-prefix extraction, a 3/2 recursive bound on the single
far-tail/mixed signed cell remainder closes the existing CORR-4 consumer. -/
theorem riemannHypothesis_of_prefixTailMixedThreeHalves
    {C : ℝ} (hC : 0 ≤ C)
    (hTail : LowOwnerPrefixTailMixedQ2EnergyBound (3 / 2) C) :
    RiemannHypothesis := by
  have hFinal :=
    finalStokesQ2EnergyBound_of_prefixTailMixedThreeHalves hTail
  exact
    riemannHypothesis_of_canonicalRoughCorrelationFourQ2Energy
      (correlationFour_of_finalStokesQ2EnergyBound
        (B := 7 / 4) (C := C)
        (by norm_num) (by norm_num) hC hFinal)

end RHLean.Proof
