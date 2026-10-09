import Mathlib
import «research.VF_MID_FIRST_BAD_ACTIVE_RAW_PARENT_SPLICE»
import «research.VF_MID_ENDPOINT_TRIGGER_DICTIONARY»
import «research.VF_MID_FIRST_BAD_PAYMENT_V2_KERNEL»

/-!
# Actual prime admissibility certificate: established structural rules

This theorem bundles arithmetic rules that the real prime-counting function
ALREADY satisfies, from previously proved main-branch lemmas. It never
introduces a false all-state contraction or assumes the RH-scale bound.

Crucial status distinction:

* vfV2ActualPrime_verifiedStructuralRules : proved from existing arithmetic.
* VFMidActualPrimeSignedOwnerEscapeRule : Prop, NOT proved here.
* vfV2ActualPrime_noFirstBad_of_signedOwnerEscapeRule : proved CONDITIONAL
  consumer of that new named arithmetic Prop; the signed rule is the SAME
  existing production Sector Six budget, not an alternative RH axiom.

The entire need for a true quantitative arithmetic theorem is exposed by
this separation. A generic monotone unit-step function can satisfy the
algebraic finite laws without satisfying the signed sector-six rule.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Structural admissibility of actual primes that was ALREADY proved in
independent modules and requires no unproved RH-strength distribution input. -/
structure VFMidActualPrimeVerifiedStructuralRules : Prop where
  odd_population :
    ∀ R : ℕ, (vfMidOddCandidateSeats R).card = R
  vf_reference_exact :
    ∀ R : ℕ, 2 ≤ R →
      (∑ _n ∈ vfMidOddCandidateSeats R,
        vfMidOddFractionalPrimeSeatWeight R) = vfMidBandMass R
  prime_sites_exact :
    ∀ R : ℕ, 2 ≤ R →
      (vfMidOddCandidateSeats R).filter Nat.Prime =
        vfMidSquareWheelPrimes R
  prime_composite_population :
    ∀ R : ℕ, 2 ≤ R →
      (vfMidSquareBandPrefixCompositeSurvivors 2 R).card +
        vfMidIntegerBlockPrimeSupply R = R
  signed_vf_minus_prime :
    ∀ R : ℕ, 2 ≤ R →
      (∑ n ∈ vfMidOddCandidateSeats R, vfMidOddSignedSeatCharge R n) =
        vfMidOddCompositeTrackingDefect R
  least_prime_owner_partition :
    ∀ R : ℕ, 2 ≤ R →
      vfMidOddCompositeTrackingDefect R =
        (∑ p ∈ vfMidSquareBandLateOwnerPrimes 2 R,
          ((vfMidSquareBandCompositeOwner R p).card : ℝ)) -
          vfMidOddFractionalCompositeReference R
  restricted_mobius_affine_decoder :
    ∀ (A R n : ℕ), 3 ≤ A → A ≤ R →
      (R + 1) ^ 2 ≤ (A + 1) ^ 3 →
        n ∈ vfMidSquarePrefixWheelSurvivors A R →
      vfMidOddSignedSeatCharge R n =
        vfMidCubeSeatAffineCenter R + (1 / 2 : ℝ) * realMoebiusStep n
  history_once :
    ∀ (A B : ℕ), 3 ≤ A → A ≤ B → B ≤ 2 * A →
      vfMidActualPrimeEndpointDefect B =
        vfMidActualPrimeEndpointDefect A -
          vfMidFrozenAffineRunPhysicalCharge A B
  original_anchored_mass :
    ∀ R : ℕ,
      vfMidFirstBadZeroTargetTotalMass R =
        (|vfMidActualPrimeEndpointDefect R| +
          ∑ n ∈ vfMidOddCandidateSeats R,
            |vfMidOddSignedSeatCharge R n|) ^ 2
  full_weighted_codiv_ledger :
    ∀ R : ℕ, 3 ≤ R →
      vfMidFirstBadAnchoredCoDivExcess R =
        vfMidActiveGlobalResidualExcess R +
          ∑ p ∈ primesUpTo (squareRootEndpoint (R + 1)),
            ∑ sig ∈ lowOwnerFirstOwnerSignatureSet (R + 1) p,
              vfMidActiveWeightedCellExcess R p sig
  active_owner_returned_weld :
    ∀ (R p : ℕ) (sig : Finset ℕ), 3 ≤ R → p.Prime →
      lowOwnerFirstOwnerCellGramWith
        (R + 1) p sig (vfMidOneBlockActivePhysicalSite R) =
        vfMidActiveScaledReturnedClippedCellMass R p sig
  first_bad_forces_above_half :
    ∀ R : ℕ, 8 ≤ R →
      VFMidActualPrimeFirstBadAt (2 : ℝ) (R + 1) →
      (1 / 2 : ℝ) < vfMidFirstBadNNSNormalizedCovariance R

/-- ACTUAL PRIMES SATISFY every field of the verified structural certificate.
No field is an escape estimate and no inference from density alone is made. -/
theorem vfV2ActualPrime_verifiedStructuralRules :
    VFMidActualPrimeVerifiedStructuralRules := by
  exact {
    odd_population := vfMidOddCandidateSeats_card
    vf_reference_exact := fun R hR =>
      vfMidOddFractionalPrimeSeatWeight_sum R hR
    prime_sites_exact := fun R hR =>
      vfMidOddCandidateSeats_filter_prime R hR
    prime_composite_population := fun R hR =>
      vfMidOddActualComposite_card_add_primeSupply R hR
    signed_vf_minus_prime := fun R hR =>
      vfMidOddSignedSeatCharge_sum R hR
    least_prime_owner_partition := fun R hR =>
      vfMidOddCompositeTrackingDefect_eq_ownerCensus_sub_reference R hR
    restricted_mobius_affine_decoder := fun A R n hA hAR hc hn =>
      vfMidOddSignedSeatCharge_eq_affineCenter_add_half_moebius_of_cube
        hA hAR hc hn
    history_once := fun A B hA hAB hBA =>
      vfMidActualPrimeEndpointDefect_eq_anchor_sub_frozenAffineRun
        hA hAB hBA
    original_anchored_mass := vfMidFirstBadZeroTargetTotalMass_eq
    full_weighted_codiv_ledger := fun R hR =>
      vfMidFirstBadAnchoredCoDivExcess_eq_activeResidual_add_weightedCells hR
    active_owner_returned_weld := fun R p sig hR hp =>
      vfMidActiveCellGram_eq_scaledReturnedClippedCellMass hR hp
    first_bad_forces_above_half := fun R hR hfirst =>
      vfMidActualPrimeFirstBadAt_two_succ_nnsNormalized_gt_half hR hfirst
  }

/-- The six original incomplete raw-parent sectors, with the SIGNED source
vfMidActiveReturnedRawParentFiberMass and no new square or absolute value.
This definition only abbreviates the already-compiled #912 physical ledger. -/
def vfV2ActualSixSectorSignedMass (R : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo (squareRootEndpoint (R + 1)),
    ∑ sig ∈ lowOwnerFirstOwnerSignatureSet (R + 1) p,
      ∑ r ∈ lowOwnerRevealedPrimesAbove (R + 1) p,
        ((∑ parent ∈
            lowOwnerFirstOwnerIncompleteFirstClipLeftSet
              (R + 1) p sig r,
            vfMidActiveReturnedRawParentFiberMass R p sig r parent) +
         (∑ parent ∈
            lowOwnerFirstOwnerIncompleteFirstClipRightSet
              (R + 1) p sig r,
            vfMidActiveReturnedRawParentFiberMass R p sig r parent) +
         (∑ parent ∈
            lowOwnerFirstOwnerIncompleteNextClipLeftSet
              (R + 1) p sig r,
            vfMidActiveReturnedRawParentFiberMass R p sig r parent) +
         (∑ parent ∈
            lowOwnerFirstOwnerIncompleteNextClipRightSet
              (R + 1) p sig r,
            vfMidActiveReturnedRawParentFiberMass R p sig r parent) +
         (∑ parent ∈
            lowOwnerFirstOwnerIncompleteReturnedClipLeftSet
              (R + 1) p sig r,
            vfMidActiveReturnedRawParentFiberMass R p sig r parent) +
         ∑ parent ∈
            lowOwnerFirstOwnerIncompleteReturnedClipRightSet
              (R + 1) p sig r,
            vfMidActiveReturnedRawParentFiberMass R p sig r parent)

/-- SINGLE MISSING arithmetic admissibility rule:
after the exact signed weighted reassembly, the original root/exclusion
residual plus the six incomplete boundary sectors is NONPOSITIVE, specifically
under actual first badness. THIS IS NOT AN AXIOM OR AN ESTABLISHED THEOREM.
The geometric fantasy walls, PNT Möbius densities, and the rules above do
NOT presently prove this statement. -/
def VFMidActualPrimeSignedOwnerEscapeRule : Prop :=
  ∀ (R : ℕ), 8 ≤ R →
    VFMidActualPrimeFirstBadAt (2 : ℝ) (R + 1) →
      vfMidActiveGlobalResidualExcess R +
        2 * vfV2ActualSixSectorSignedMass R ≤ 0

/-- The existing terminal Sector Six consumer needs EXACTLY the signed rule
above. This theorem is conditional and DOES NOT prove that rule. -/
theorem vfV2ActualPrime_noFirstBad_of_signedOwnerEscapeRule
    (h : VFMidActualPrimeSignedOwnerEscapeRule)
    {R : ℕ} (hR : 8 ≤ R)
    (hfirst : VFMidActualPrimeFirstBadAt (2 : ℝ) (R + 1)) :
    False := by
  exact vfMidActualPrimeFirstBadAt_two_succ_false_of_activeSixBoundaryBudget
    hR hfirst (h R hR hfirst)

/-- The arithmetic rule cannot simply be omitted from the proof interface.
It is precisely the remaining first-bad directional owner-correlation
constraint; verifying finite values cannot establish its universal quantifier. -/
theorem vfV2ActualPrime_admissibilityStatus :
    VFMidActualPrimeVerifiedStructuralRules ∧
      (VFMidActualPrimeSignedOwnerEscapeRule →
        ∀ R : ℕ, 8 ≤ R →
          ¬ VFMidActualPrimeFirstBadAt (2 : ℝ) (R + 1)) := by
  exact ⟨vfV2ActualPrime_verifiedStructuralRules,
    fun h R hR hfirst =>
      vfV2ActualPrime_noFirstBad_of_signedOwnerEscapeRule h hR hfirst⟩

end RHLean.Analysis
