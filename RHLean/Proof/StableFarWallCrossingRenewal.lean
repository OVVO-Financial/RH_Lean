import RHLean.Proof.StableFarWallOwnedCensus
import RHLean.Proof.StableFarPrimeWallTransport

/-!
# Crossing survivors are genuine lower-cofactor stable-wall occurrences

After the exact census of #672, a strict `q^2` crossing is represented by a
true product `(q, d*p)`, where `p` is the original far prime and `d` is the
cofactor left after stripping the fresh low prime `q`.

This file records the next signed-reassembly fact without taking a norm:
forgetting the stripped owner does not create an artificial arithmetic object.
The lower state `(d,p)` is itself a literal member of the original stable far
wall, and its native physical weight is the opposite of the crossing product's
Möbius weight.

The owner tag is deliberately retained in the sum.  Different crossing owners
may descend to the same lower stable-wall state, so no injectivity across owners
is asserted or used.  This is the renewal form needed for any subsequent
frontier cancellation: every surviving crossing is an actual signed return to
the same physical wall, with exact multiplicity.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- The stable-wall state reached after forgetting only the crossing owner tag. -/
def lowWheelFarPrimeCrossingStableState
    (x : ℕ × ℕ) : LowWheelFullTaggedPhysicalState :=
  (∅, (canonicalCofactor x.2, canonicalLargestPrimeFactor x.2))

/-- Every strict crossing product returns to a literal state of the original
stable far wall.  No owner multiplicity is forgotten by this membership
statement. -/
theorem lowWheelFarPrimeCrossingStableState_mem
    {R : ℕ} (hR : 2 ≤ R) {x : ℕ × ℕ}
    (hx : x ∈ lowWheelFarPrimeCrossingProductCarrier R) :
    lowWheelFarPrimeCrossingStableState x ∈ stableFarWallCarrier R := by
  rcases Finset.mem_image.mp hx with ⟨t, htCross, rfl⟩
  have ht : t ∈ lowWheelFarPrimeLowCofactorTriples R :=
    (Finset.mem_filter.mp htCross).1
  rcases lowWheelFarPrimeLowCofactorTriple_data ht with
    ⟨hq, hqR, hd1, hp, hpR, hdsq, hdq, hcut⟩
  have hcoords := lowWheelFarPrimeProduct_coordinates ht
  have hq1 : 1 ≤ t.1 := hq.one_le
  have hdpCut : t.2.1 * t.2.2 ≤ squareRootEndpoint R := by
    have hle : t.2.1 * t.2.2 ≤ t.1 * (t.2.1 * t.2.2) :=
      Nat.mul_le_mul_right (t.2.1 * t.2.2) hq1
    exact hle.trans (by simpa [Nat.mul_assoc] using hcut)
  have hRpos : 0 < R := by omega
  have hXlt : squareRootEndpoint R < R * R := by
    unfold squareRootEndpoint
    have hne : R ^ 2 ≠ 0 := pow_ne_zero 2 (Nat.ne_of_gt hRpos)
    simpa [pow_two] using Nat.pred_lt hne
  have hpGeR : R ≤ t.2.2 := by omega
  have hdR : t.2.1 < R := by
    by_contra hnot
    have hRd : R ≤ t.2.1 := Nat.le_of_not_gt hnot
    have hR2 : R * R ≤ t.2.1 * t.2.2 := Nat.mul_le_mul hRd hpGeR
    exact (Nat.not_lt_of_ge (hR2.trans hdpCut)) hXlt
  apply (mem_stableFarWallCarrier_iff_primeInsertion hR).2
  change
    (∅ : Finset ℕ) = ∅ ∧
      (canonicalLargestPrimeFactor (t.2.1 * t.2.2)).Prime ∧
      R + 8 ≤ canonicalLargestPrimeFactor (t.2.1 * t.2.2) ∧
      canonicalLargestPrimeFactor (t.2.1 * t.2.2) ≤ squareRootEndpoint R ∧
      canonicalCofactor (t.2.1 * t.2.2) ∈ Finset.Ico 1 R ∧
      Squarefree (canonicalCofactor (t.2.1 * t.2.2)) ∧
      canonicalCofactor (t.2.1 * t.2.2) *
          canonicalLargestPrimeFactor (t.2.1 * t.2.2) ≤ squareRootEndpoint R
  rw [hcoords.1, hcoords.2]
  refine ⟨rfl, hp, hpR, ?_, Finset.mem_Ico.mpr ⟨hd1, hdR⟩, hdsq, hdpCut⟩
  exact hpR.trans (by
    have hle : t.2.2 ≤ t.2.1 * t.2.2 := by
      simpa using Nat.mul_le_mul_right t.2.2 hd1
    exact hle.trans hdpCut)

/-- Pointwise renewal sign: the returned stable-wall occurrence has exactly the
opposite weight of the crossing product. -/
theorem lowWheelFarPrimeCrossingStableState_weight_eq_neg_product
    {R : ℕ} (hR : 2 ≤ R) {x : ℕ × ℕ}
    (hx : x ∈ lowWheelFarPrimeCrossingProductCarrier R) :
    lowWheelFullTaggedPhysicalWeight
        (lowWheelFarPrimeCrossingStableState x) =
      -canonicalMoebiusWeight x.2 := by
  have hmem := lowWheelFarPrimeCrossingStableState_mem hR hx
  have hweight := stableFarWall_singleInsertion_weight hR hmem
  unfold lowWheelFarPrimeCrossingStableState at hweight
  simpa using hweight

/-- **Exact crossing-renewal mass identity.**  Every crossing survivor is the
negative of a genuine lower stable-wall occurrence.  The sum is still indexed
by the tagged crossing carrier, so repeated owners landing on the same lower
state remain repeated occurrences rather than being silently collapsed. -/
theorem lowWheelFarPrimeCrossingProductMass_eq_neg_stableRenewalMass
    {R : ℕ} (hR : 2 ≤ R) :
    (∑ x ∈ lowWheelFarPrimeCrossingProductCarrier R,
        canonicalMoebiusWeight x.2) =
      -∑ x ∈ lowWheelFarPrimeCrossingProductCarrier R,
        lowWheelFullTaggedPhysicalWeight
          (lowWheelFarPrimeCrossingStableState x) := by
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  have h := lowWheelFarPrimeCrossingStableState_weight_eq_neg_product hR hx
  linear_combination -h

/-- The four-term #672 boundary in renewal form: all strict crossing mass is now
shown on the literal stable far wall, while the already-owned terminal product
population remains explicit.  This is still a signed identity, not an estimate. -/
theorem lowWheelFarWall_remainingBoundary_eq_neg_stableRenewal_sub_terminal
    {R : ℕ} (hR : 2 ≤ R) :
    lowWheelFarPrimeUnitFaceMass R - lowWheelFarPrimeQ2CrossingMass R -
        lowWheelCanonicalRepeatedTerminalInternalMateLedger R -
        lowWheelFrozenCofactorTopImageLedger R =
      -(∑ x ∈ lowWheelFarPrimeCrossingProductCarrier R,
          lowWheelFullTaggedPhysicalWeight
            (lowWheelFarPrimeCrossingStableState x)) -
        ∑ n ∈ lowWheelFarWallTerminalProducts R,
          canonicalMoebiusWeight n := by
  rw [lowWheelFarWall_remainingBoundary_eq_signed_products R,
    lowWheelFarPrimeCrossingProductMass_eq_neg_stableRenewalMass hR]

end RHLean.Proof
