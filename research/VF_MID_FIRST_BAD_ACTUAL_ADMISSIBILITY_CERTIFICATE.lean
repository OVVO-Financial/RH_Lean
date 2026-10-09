import Mathlib
import «research.VF_MID_FIRST_BAD_ACTIVE_RAW_PARENT_SPLICE»
import «research.VF_MID_ENDPOINT_TRIGGER_DICTIONARY»
import «research.VF_MID_FIRST_BAD_PAYMENT_V2_KERNEL»
import «research.VF_MID_FLOOR_LI_TRANSPORT_CANCELLATION»

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


/-! ## Genuine localized rough-Mobius decoder, not asymptotic density

The physical prime/composite source in any finite frozen-wheel run under
the cubic-depth condition can be written exactly as a signed Mobius
imbalance on the ACTUAL survivors of that frozen wheel. This is the
correct localized population on which a future quantitative sign
estimate must act; the unrestricted density of μ(n)=±1 is insufficient
to bound these rough filtered sums. -/

/-- For every actual finite run satisfying the depth-two restriction,
the historical prime-minus-VF error is EXACTLY the centered restricted
rough-Mobius balance. The frozen survivor count stays on the original
arithmetic wheel; no artificial prime jumps or proxy counts enter.
This is a TRUE arithmetic identity, not the missing estimate. -/
theorem vfV2ActualPrimeFrozenRunMobiusDecoder
    {A B : ℕ} (hA : 3 ≤ A) (hAB : A ≤ B)
    (hcube : ∀ r ∈ Finset.Ico A B, (r + 1) ^ 2 ≤ (A + 1) ^ 3) :
    (∑ r ∈ Finset.Ico A B,
      ((vfMidIntegerBlockPrimeSupply r : ℝ) - vfMidBandMass r)) =
    ∑ r ∈ Finset.Ico A B,
      (((((vfMidSquarePrefixWheelSurvivors A r).card : ℝ) -
        vfMidSquareBandPrefixSurvivorMobiusMassReal A r) / 2) -
        vfMidBandMass r) := by
  apply Finset.sum_congr rfl
  intro r hr
  have hAr : A ≤ r := (Finset.mem_Ico.mp hr).1
  have hz :=
    two_mul_vfMidIntegerBlockPrimeSupply_eq_prefixSurvivors_sub_mobiusMass_of_cube
      hA hAr (hcube r hr)
  have hreal :
      (2 : ℝ) * (vfMidIntegerBlockPrimeSupply r : ℝ) =
        ((vfMidSquarePrefixWheelSurvivors A r).card : ℝ) -
          vfMidSquareBandPrefixSurvivorMobiusMassReal A r := by
    rw [vfMidSquareBandPrefixSurvivorMobiusMassReal_eq_cast]
    exact_mod_cast hz
  linarith

/-- The localized signed Mobius deviation equals TWICE the actual
prime-minus-VF run deviation, with the deterministic frozen-wheel
population adjustment retained. This does NOT assert a bound on
the deviation and therefore cannot be substituted for the Sector Six
signed capacity inequality. -/
theorem vfV2ActualPrimeFrozenRunMobiusDeviation
    {A B : ℕ} (hA : 3 ≤ A) (hAB : A ≤ B)
    (hcube : ∀ r ∈ Finset.Ico A B, (r + 1) ^ 2 ≤ (A + 1) ^ 3) :
    (∑ r ∈ Finset.Ico A B,
        (((vfMidSquarePrefixWheelSurvivors A r).card : ℝ) -
          vfMidSquareBandPrefixSurvivorMobiusMassReal A r -
            2 * vfMidBandMass r)) =
      2 * (∑ r ∈ Finset.Ico A B,
        ((vfMidIntegerBlockPrimeSupply r : ℝ) - vfMidBandMass r)) := by
  have h := vfV2ActualPrimeFrozenRunMobiusDecoder hA hAB hcube
  calc
    _ = ∑ r ∈ Finset.Ico A B,
          2 * ((((vfMidSquarePrefixWheelSurvivors A r).card : ℝ) -
             vfMidSquareBandPrefixSurvivorMobiusMassReal A r) / 2 -
               vfMidBandMass r) := by
      apply Finset.sum_congr rfl
      intro r _hr
      ring
    _ = 2 * (∑ r ∈ Finset.Ico A B,
          ((((vfMidSquarePrefixWheelSurvivors A r).card : ℝ) -
             vfMidSquareBandPrefixSurvivorMobiusMassReal A r) / 2 -
               vfMidBandMass r)) := by
      rw [Finset.mul_sum]
    _ = _ := by rw [h]

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


/-- Logical honesty audit. Once the compiled first-bad consumer is available,
the signed owner rule as quantified above is EQUIVALENT to having no
first-bad successor above the base. The reverse implication is vacuous.
Consequently the rule CANNOT be listed as independently established
admissibility, and a genuine arithmetic proof of its signed budget is
indispensable. -/
theorem vfV2ActualPrime_signedOwnerRule_iff_noFirstBad :
    VFMidActualPrimeSignedOwnerEscapeRule ↔
      ∀ R : ℕ, 8 ≤ R →
        ¬ VFMidActualPrimeFirstBadAt (2 : ℝ) (R + 1) := by
  constructor
  · intro h R hR hfirst
    exact vfV2ActualPrime_noFirstBad_of_signedOwnerEscapeRule
      h hR hfirst
  · intro h R hR hfirst
    exact (h R hR hfirst).elim



/-! ## Actual-prime specialization of age and prospective signed flux

The finite population here is the ORIGINAL odd physical square carrier,
filtered by GENUINE prime factors q>R.  Each composite site is charged
ONCE and belongs to exactly one age class via a selected genuine parent.
No floor-Li event is a physical site; no old prime charge is duplicated.
These theorems deliberately do NOT establish the first-bad Sector Six sign. -/

/-- Only actual composite odd seats possessing a genuine prime factor q>R.
The strict q<n guard excludes prime n=q; q is never a floor-Li event. -/
def vfV2ActualHighPrimeOddCompositeSites (R : ℕ) : Finset ℕ :=
  (vfMidOddCandidateSeats R).filter fun n =>
    ∃ q : ℕ, q.Prime ∧ R < q ∧ q ∣ n ∧ q < n

/-- A representative TRUE high-prime ancestor for each physical composite.
The choice cannot create a second physical site or an additional charge. -/
noncomputable def vfV2ActualHighPrimeParent (R n : ℕ) : ℕ :=
  if h : ∃ q : ℕ, q.Prime ∧ R < q ∧ q ∣ n ∧ q < n
  then Classical.choose h
  else 0

theorem vfV2ActualHighPrimeParent_genuine
    {R n : ℕ} (hn : n ∈ vfV2ActualHighPrimeOddCompositeSites R) :
    (vfV2ActualHighPrimeParent R n).Prime ∧
      R < vfV2ActualHighPrimeParent R n ∧
      vfV2ActualHighPrimeParent R n ∣ n ∧
      vfV2ActualHighPrimeParent R n < n := by
  have hex : ∃ q : ℕ, q.Prime ∧ R < q ∧ q ∣ n ∧ q < n :=
    (Finset.mem_filter.mp hn).2
  unfold vfV2ActualHighPrimeParent
  rw [dif_pos hex]
  exact Classical.choose_spec hex

/-- On the strict original physical square band, the chosen genuine high
prime is the UNIQUE prime q>R dividing that site.  The earlier choice is
therefore intrinsic, not a statistical owner assumption. -/
theorem vfV2ActualHighPrimeParent_unique_on_band
    {R n q : ℕ}
    (hn : n ∈ vfV2ActualHighPrimeOddCompositeSites R)
    (hband : R ^ 2 < n ∧ n < (R + 1) ^ 2)
    (hqPrime : q.Prime) (hq : R < q) (hqn : q ∣ n) :
    vfV2ActualHighPrimeParent R n = q := by
  have hchosen := vfV2ActualHighPrimeParent_genuine hn
  exact vfV2HighPrimeFactorUniqueOnOpenSquare hband
    hchosen.1 hqPrime hchosen.2.1 hq hchosen.2.2.1 hqn

/-- Physical high-prime owner-age cohorts reassemble the ACTUAL current
odd-composite sites, never the historical negative prime q charges. -/
theorem vfV2ActualHighPrimeAgeNativeMass_sum (R : ℕ) :
    (∑ bucket : Fin 4,
      vfV2AgeCohortNativeMass R
        (vfV2ActualHighPrimeOddCompositeSites R)
        (fun n => Nat.sqrt (vfV2ActualHighPrimeParent R n))
        (fun _ => vfMidOddFractionalPrimeSeatWeight R) bucket) =
      ∑ n ∈ vfV2ActualHighPrimeOddCompositeSites R,
        vfMidOddFractionalPrimeSeatWeight R := by
  exact vfV2AgeCohortNativeMass_sum R
    (vfV2ActualHighPrimeOddCompositeSites R)
    (fun n => Nat.sqrt (vfV2ActualHighPrimeParent R n))
    (fun _ => vfMidOddFractionalPrimeSeatWeight R)

/-- The genuine physical flux endpoint E_R is the integer actual-prime
count minus the deterministic integer floor-Li count at R^2. -/
def vfV2ActualSquareFloorLiError (R : ℕ) : ℝ :=
  (vfMidPrimeFloorLiBacklog R : ℝ)

/-- Actual signed block flux equals P_R-F_R, not a proxy owner census. -/
theorem vfV2ActualSquareFloorLiFlux_eq_trueBlockCorrection (R : ℕ) :
    vfV2BlockFlux vfV2ActualSquareFloorLiError R =
      (vfMidFloorLiActualBlockCorrection R : ℝ) := by
  unfold vfV2BlockFlux vfV2ActualSquareFloorLiError
  exact_mod_cast
    (vfMidFloorLiActualBlockCorrection_eq_backlog_increment R).symm

/-- The DELAYED response is the sum of genuine actual-minus-floor-Li block
corrections at R+1,...,R+h, so block R is demonstrably excluded. -/
theorem vfV2ActualDelayedFlux_eq_genuineFutureCorrections
    (R horizon : ℕ) (orientation : ℝ) :
    vfV2DelayedOrientedFlux vfV2ActualSquareFloorLiError
        orientation R horizon =
      orientation *
        (∑ r ∈ Finset.Ico (R + 1) (R + 1 + horizon),
          (vfMidFloorLiActualBlockCorrection r : ℝ)) := by
  rw [vfV2DelayedFlux_eq_futureBlockSum]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  exact vfV2ActualSquareFloorLiFlux_eq_trueBlockCorrection r

/-- Exact correspondence between the original ACTUAL prime endpoint defect,
the integer signed count backlog and the deterministic floor-Li VF bridge. -/
theorem vfV2ActualDefect_eq_backlog_plus_deterministicBridge (R : ℕ) :
    vfMidActualPrimeEndpointDefect R =
      vfV2ActualSquareFloorLiError R + vfMidFloorLiVFBridge R := by
  exact vfMidPrimeError_sq_eq_floorLiBacklog_add_bridge R

/-- The precise future-oriented moving wall identity, in native actual pi
and VF currency.  It still gives no sign inequality for a hypothetical first
bad. -/
theorem vfV2ActualDelayedMovingWallIdentity
    (R horizon : ℕ) (orientation : ℝ) :
    ((2 : ℝ) * vfMidSyntheticRadialScale (R + 1 + horizon) -
       orientation * vfMidActualPrimeEndpointDefect (R + 1 + horizon)) -
      ((2 : ℝ) * vfMidSyntheticRadialScale (R + 1) -
       orientation * vfMidActualPrimeEndpointDefect (R + 1)) =
    ((2 : ℝ) * vfMidSyntheticRadialScale (R + 1 + horizon) -
       2 * vfMidSyntheticRadialScale (R + 1)) -
      vfV2DelayedOrientedFlux vfV2ActualSquareFloorLiError
        orientation R horizon -
      orientation *
        (vfMidFloorLiVFBridge (R + 1 + horizon) -
          vfMidFloorLiVFBridge (R + 1)) := by
  exact vfV2DelayedMovingWallClearance
    (W := fun t => 2 * vfMidSyntheticRadialScale t)
    (D := vfMidActualPrimeEndpointDefect)
    (E := vfV2ActualSquareFloorLiError)
    (b := vfMidFloorLiVFBridge) orientation R horizon
    (vfV2ActualDefect_eq_backlog_plus_deterministicBridge (R + 1))
    (vfV2ActualDefect_eq_backlog_plus_deterministicBridge (R + 1 + horizon))

/-! ### The actual observational coordinates, with no future information -/

/-- Historical absolute occupancy relative to the ORIGINAL K=2 VF wall.
This is a descriptive score; it does NOT imply a uniform future drift. -/
def vfV2ActualWallOccupancy (R : ℕ) : ℝ :=
  |vfMidActualPrimeEndpointDefect R| /
    ((2 : ℝ) * vfMidSyntheticRadialScale R)

theorem vfV2ActualWallOccupancy_nonneg
    {R : ℕ} (hR : 2 ≤ R) :
    0 ≤ vfV2ActualWallOccupancy R := by
  have hw : 0 < vfMidSyntheticRadialScale R :=
    vfMidSyntheticRadialScale_pos hR
  unfold vfV2ActualWallOccupancy
  positivity

/-- Empirical occupancy classification uses the past (R-span,...,R-1)
only, with a score determined by ACTUAL pi and VF. -/
def vfV2ActualPastOnlyHighOccupancy (R span : ℕ) : Prop :=
  vfV2PastOnlyHighOccupancy vfV2ActualWallOccupancy R span

def vfV2ActualPastOnlyLowOccupancy (R span : ℕ) : Prop :=
  vfV2PastOnlyLowOccupancy vfV2ActualWallOccupancy R span

/-- The current sign of the ACTUAL historical endpoint defect is frozen
before evaluating future flux.  Its value is -1 or +1, not a fitted
expectation or an unknown future prime property. -/
def vfV2ActualHistoricalOrientation (R : ℕ) : ℝ :=
  if vfMidActualPrimeEndpointDefect R < 0 then -1 else 1

theorem vfV2ActualHistoricalOrientation_neg
    {R : ℕ} (hneg : vfMidActualPrimeEndpointDefect R < 0) :
    vfV2ActualHistoricalOrientation R = -1 := by
  simp [vfV2ActualHistoricalOrientation, hneg]

/-- The strictly delayed oriented observation studied numerically:
the *current* original physical square block is excluded, and the orientation
is fixed using the historical defect at R. -/
def vfV2ActualStrictDelayedFlux (R horizon : ℕ) : ℝ :=
  vfV2DelayedOrientedFlux vfV2ActualSquareFloorLiError
    (vfV2ActualHistoricalOrientation R) R horizon

theorem vfV2ActualStrictDelayedFlux_eq_truePrimeBlockSum
    (R horizon : ℕ) :
    vfV2ActualStrictDelayedFlux R horizon =
      vfV2ActualHistoricalOrientation R *
        (∑ r ∈ Finset.Ico (R + 1) (R + 1 + horizon),
          (vfMidFloorLiActualBlockCorrection r : ℝ)) := by
  exact vfV2ActualDelayedFlux_eq_genuineFutureCorrections
    R horizon (vfV2ActualHistoricalOrientation R)

/-- This is the original production conclusion with the SAME original
signed Sector Six premise, not a hypothetical age-feedback substitute. -/
theorem vfV2ActualOccurrencePreservingReturn_closes_firstBad
    {R : ℕ} (hR : 8 ≤ R)
    (hfirst : VFMidActualPrimeFirstBadAt (2 : ℝ) (R + 1))
    (hreturn : vfMidActiveGlobalResidualExcess R +
      2 * vfV2ActualSixSectorSignedMass R ≤ 0) :
    False := by
  exact vfMidActualPrimeFirstBadAt_two_succ_false_of_activeSixBoundaryBudget
    hR hfirst hreturn


end RHLean.Analysis
