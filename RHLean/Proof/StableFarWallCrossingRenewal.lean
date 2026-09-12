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
open FrozenCofactorTopBottom LowWheelCanonicalDowncrossOwnership

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
  have hlpf :
      canonicalLargestPrimeFactor (t.2.1 * t.2.2) = t.2.2 := by
    simpa [lowWheelFarPrimeProductKey] using hcoords.1
  have hcofactor :
      canonicalCofactor (t.2.1 * t.2.2) = t.2.1 := by
    simpa [lowWheelFarPrimeProductKey] using hcoords.2
  have hq1 : 1 ≤ t.1 := hq.one_le
  have hdpCut : t.2.1 * t.2.2 ≤ squareRootEndpoint R := by
    have hle : t.2.1 * t.2.2 ≤ t.1 * (t.2.1 * t.2.2) := by
      simpa using Nat.mul_le_mul_right (t.2.1 * t.2.2) hq1
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
  rw [hlpf, hcofactor]
  refine ⟨rfl, hp, hpR, ?_, Finset.mem_Ico.mpr ⟨hd1, hdR⟩, hdsq, hdpCut⟩
  have hle : t.2.2 ≤ t.2.1 * t.2.2 := by
    simpa using Nat.mul_le_mul_right t.2.2 hd1
  exact hle.trans hdpCut

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
  have hxgt : 1 < x.2 := by
    rcases Finset.mem_image.mp hx with ⟨t, htCross, htx⟩
    have ht := (Finset.mem_filter.mp htCross).1
    have hfar := (lowWheelFarPrimeProduct_geometry ht).2.1
    have hfarx : R + 8 ≤ x.2 := by
      simpa [htx] using hfar
    omega
  have hprod := canonicalCofactor_mul_largestPrimeFactor hxgt
  unfold lowWheelFarPrimeCrossingStableState at hweight
  rw [hprod] at hweight
  exact hweight

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
  rw [lowWheelFarPrimeCrossingStableState_weight_eq_neg_product hR hx]
  ring

/-- The descended triples may be regrouped by every possible prime owner below
`R` without losing an occurrence.  This is finite Fubini only. -/
theorem lowWheelFarPrimeQ2DescendedMass_eq_ownerFibers (R : ℕ) :
    lowWheelFarPrimeQ2DescendedMass R =
      ∑ q ∈ primesUpTo (R - 1),
        ∑ t ∈ lowWheelFarPrimeQ2DescendedOwnerTriples R q,
          canonicalMoebiusWeight t.2.1 := by
  let S := lowWheelFarPrimeQ2DescendedTriples R
  let O := primesUpTo (R - 1)
  let owner : ℕ × (ℕ × ℕ) → ℕ := Prod.fst
  have hmaps : ∀ t ∈ S, owner t ∈ O := by
    intro t ht
    have hdata := lowWheelFarPrimeLowCofactorTriple_data
      (Finset.mem_filter.mp ht).1
    exact mem_primesUpTo.mpr ⟨hdata.1, Nat.le_pred_of_lt hdata.2.1⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := S) (t := O) (g := owner) hmaps
    (fun t => canonicalMoebiusWeight t.2.1)
  have hraw :
      (∑ t ∈ S, canonicalMoebiusWeight t.2.1) =
        ∑ q ∈ O,
          ∑ t ∈ S with owner t = q,
            canonicalMoebiusWeight t.2.1 := hfiber.symm
  unfold lowWheelFarPrimeQ2DescendedMass
  change (∑ t ∈ S, canonicalMoebiusWeight t.2.1) =
    ∑ q ∈ O,
      ∑ t ∈ lowWheelFarPrimeQ2DescendedOwnerTriples R q,
        canonicalMoebiusWeight t.2.1
  rw [hraw]
  apply Finset.sum_congr rfl
  intro q hq
  rfl

/-- **Global descended-child identification.**  The complete stripped descended
mass is exactly the sum of the literal far-prime high-transport slices at every
q² child cutoff. -/
theorem lowWheelFarPrimeQ2DescendedMass_eq_sum_childFarSlices (R : ℕ) :
    lowWheelFarPrimeQ2DescendedMass R =
      ∑ q ∈ primesUpTo (R - 1),
        ∑ dp ∈ lowWheelFarPrimeQ2ChildFarSlice R q,
          canonicalMoebiusWeight dp.1 := by
  rw [lowWheelFarPrimeQ2DescendedMass_eq_ownerFibers R]
  apply Finset.sum_congr rfl
  intro q hq
  have hdata := mem_primesUpTo.mp hq
  have hRpos : 0 < R := by
    have := hdata.1.two_le
    omega
  have hqR : q < R := Nat.lt_of_le_pred hRpos hdata.2
  exact lowWheelFarPrimeQ2DescendedOwner_mass_eq_childFarSlice hdata.1 hqR

/-- Reattaching the original far prime reverses the child-far sign, so the true
descended product packet is the negative of the global child high-transport
slice sum. -/
theorem lowWheelFarPrimeDescendedProductMass_eq_neg_sum_childFarSlices
    (R : ℕ) :
    (∑ x ∈ lowWheelFarPrimeDescendedProductCarrier R,
        canonicalMoebiusWeight x.2) =
      -∑ q ∈ primesUpTo (R - 1),
        ∑ dp ∈ lowWheelFarPrimeQ2ChildFarSlice R q,
          canonicalMoebiusWeight dp.1 := by
  have hprod := lowWheelFarPrimeQ2DescendedMass_eq_neg_productMass R
  have hchild := lowWheelFarPrimeQ2DescendedMass_eq_sum_childFarSlices R
  rw [hchild] at hprod
  have hneg := congrArg Neg.neg hprod
  simpa using hneg.symm

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

/-- **Complete post-#672 residual in renewal normal form.**  The old hard far
residual is now the genuine descended q² product packet minus the literal
stable-wall renewal occurrences minus the terminal product carrier.  Every
crossing-owner multiplicity is still present in the middle sum, and no norm has
been taken. -/
theorem lowWheelFrozenTopFarResidual_eq_descended_sub_stableRenewal_sub_terminal
    (R : ℕ) (hR : 56 ≤ R) :
    lowWheelFrozenTopFarResidual R =
      (∑ x ∈ lowWheelFarPrimeDescendedProductCarrier R,
        canonicalMoebiusWeight x.2) -
      (∑ x ∈ lowWheelFarPrimeCrossingProductCarrier R,
        lowWheelFullTaggedPhysicalWeight
          (lowWheelFarPrimeCrossingStableState x)) -
      ∑ n ∈ lowWheelFarWallTerminalProducts R,
        canonicalMoebiusWeight n := by
  rw [lowWheelFrozenTopFarResidual_eq_descended_add_crossing_sub_terminal R hR,
    lowWheelFarPrimeCrossingProductMass_eq_neg_stableRenewalMass (by omega)]
  ring

/-- The same hard residual with its descended term rewritten ownerwise as the
literal lower-scale child far-transport slices from #671. -/
theorem lowWheelFrozenTopFarResidual_eq_neg_childFarSlices_sub_stableRenewal_sub_terminal
    (R : ℕ) (hR : 56 ≤ R) :
    lowWheelFrozenTopFarResidual R =
      -(∑ q ∈ primesUpTo (R - 1),
        ∑ dp ∈ lowWheelFarPrimeQ2ChildFarSlice R q,
          canonicalMoebiusWeight dp.1) -
      (∑ x ∈ lowWheelFarPrimeCrossingProductCarrier R,
        lowWheelFullTaggedPhysicalWeight
          (lowWheelFarPrimeCrossingStableState x)) -
      ∑ n ∈ lowWheelFarWallTerminalProducts R,
        canonicalMoebiusWeight n := by
  rw [lowWheelFrozenTopFarResidual_eq_descended_sub_stableRenewal_sub_terminal R hR,
    lowWheelFarPrimeDescendedProductMass_eq_neg_sum_childFarSlices R]

end RHLean.Proof
