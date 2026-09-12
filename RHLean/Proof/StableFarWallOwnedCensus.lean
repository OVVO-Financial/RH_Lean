import RHLean.Proof.StableFarWallSignedReassembly

/-!
# The unit face and both owned images on one arithmetic carrier

The internal terminal mate and frozen top image have the true Möbius weight
of their original ordered Euler-cut child.  Those children are injective
across both populations, not merely within either image.  All their primes
are at most the root, so they are disjoint from the far unit primes.

Thus `UnitFace - InternalMate - TopImage` is the negative Möbius mass of one
literal disjoint integer carrier.  Combining it with the true crossing
products gives the joint signed boundary census before any norm.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis
open FrozenCofactorTopBottom LowWheelCanonicalDowncrossOwnership

attribute [local instance] Classical.propDecidable

/-- The ordered-cut bridge also includes frozen terminal sources. -/
theorem lowWheelCanonicalRepeatedFrozen_mem_orderedEulerCutCarrier
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenPart R) :
    y ∈ orderedEulerCutCarrier R := by
  have hrepeated := (Finset.mem_filter.mp hy).1
  have hshape := (Finset.mem_filter.mp hy).2
  have htagged := (Finset.mem_filter.mp hrepeated).1
  rcases mem_lowWheelCanonicalTaggedDowncrossCarrier.mp htagged with ⟨ht, hx⟩
  have hp := (lowWheelCanonicalDowncrossPart_adjacent_shell hx).1
  have hquot : y.2.2 / lowWheelCanonicalDowncrossPivot y.2 = 1 := by
    change y.2.2 / lowWheelTaggedDowncrossPivot y = 1
    rw [hshape.1]
    exact Nat.div_self hp.pos
  have hparent :
      LowWheelCanonicalDowncrossOwnership.lowWheelCanonicalDowncrossParent y.1 y.2 =
        primeFaceProduct y.1 := by
    unfold LowWheelCanonicalDowncrossOwnership.lowWheelCanonicalDowncrossParent
    rw [hquot, Nat.mul_one]
  apply mem_orderedEulerCutCarrier.mpr
  refine ⟨ht, mem_lowWheelCanonicalDowncrossOrientedPart.mpr ⟨hx, ?_⟩⟩
  intro r hr
  rw [hparent] at hr
  have hrData := Nat.mem_primeFactors.mp hr
  have hrDvd : r ∣ y.1.prod id := by simpa [primeFaceProduct] using hrData.2.1
  rcases (Prime.dvd_finset_prod_iff hrData.1.prime id).mp hrDvd with ⟨s, hs, hrs⟩
  have hsPrime := prime_of_mem_primesUpTo ((Finset.mem_powerset.mp ht) hs)
  have heq : r = s := (Nat.prime_dvd_prime_iff_eq hrData.1 hsPrime).mp hrs
  subst r
  exact hshape.2 s hs

/-- Original sources of the two owned physical images. -/
def lowWheelFrozenTopFarOwnedSources (R : ℕ) : Finset LowWheelTaggedDowncrossState :=
  lowWheelCanonicalRepeatedTerminalInternalPart R ∪
    lowWheelCanonicalRepeatedFrozenCofactorPart R

theorem lowWheelFrozenTopFarOwnedSources_disjoint (R : ℕ) :
    Disjoint (lowWheelCanonicalRepeatedTerminalInternalPart R)
      (lowWheelCanonicalRepeatedFrozenCofactorPart R) := by
  rw [Finset.disjoint_left]
  intro y hi hc
  have hone := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
  have hgt := (Finset.mem_filter.mp hc).2
  omega

theorem lowWheelFrozenTopFarOwnedSource_mem_orderedEulerCutCarrier
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelFrozenTopFarOwnedSources R) :
    y ∈ orderedEulerCutCarrier R := by
  apply lowWheelCanonicalRepeatedFrozen_mem_orderedEulerCutCarrier
  rcases Finset.mem_union.mp hy with hi | hc
  · exact (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1
  · exact (Finset.mem_filter.mp hc).1

/-- The two images share one multiplicity-free child-integer carrier. -/
def lowWheelFrozenTopFarOwnedProducts (R : ℕ) : Finset ℕ :=
  (lowWheelFrozenTopFarOwnedSources R).image orderedEulerCutChildInteger

theorem lowWheelFrozenTopFarOwnedProducts_sum
    {M : Type*} [AddCommMonoid M] (R : ℕ) (f : ℕ → M) :
    (∑ n ∈ lowWheelFrozenTopFarOwnedProducts R, f n) =
      ∑ y ∈ lowWheelFrozenTopFarOwnedSources R, f (orderedEulerCutChildInteger y) := by
  unfold lowWheelFrozenTopFarOwnedProducts
  apply Finset.sum_image
  intro a ha b hb hab
  exact orderedEulerCutChildInteger_injective_on_carrier
    (lowWheelFrozenTopFarOwnedSource_mem_orderedEulerCutCarrier ha)
    (lowWheelFrozenTopFarOwnedSource_mem_orderedEulerCutCarrier hb) hab

theorem lowWheelFrozenTopFarOwnedSources_mass_eq_neg_products (R : ℕ) :
    (∑ y ∈ lowWheelFrozenTopFarOwnedSources R, lowWheelTaggedDowncrossWeight y) =
      -∑ n ∈ lowWheelFrozenTopFarOwnedProducts R, canonicalMoebiusWeight n := by
  rw [lowWheelFrozenTopFarOwnedProducts_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro y hy
  have h := orderedEulerCutChildWeight_eq_neg
    (orderedEulerCutShape_of_mem_carrier
      (lowWheelFrozenTopFarOwnedSource_mem_orderedEulerCutCarrier hy))
  change orderedEulerCutWeight y = -canonicalMoebiusWeight (orderedEulerCutChildInteger y)
  rw [h, neg_neg]

/-- Exact joint parity and no-multiplicity completion of both owned images. -/
theorem lowWheelInternalMate_add_topImage_eq_ownedProductMass (R : ℕ) :
    lowWheelCanonicalRepeatedTerminalInternalMateLedger R +
        lowWheelFrozenCofactorTopImageLedger R =
      ∑ n ∈ lowWheelFrozenTopFarOwnedProducts R, canonicalMoebiusWeight n := by
  have hi := sum_lowWheelCanonicalRepeatedTerminalInternal_add_mate_eq_zero R
  have ht := lowWheelFrozenCofactorTopImageLedger_eq_neg R
  unfold lowWheelCanonicalFrozenCofactorLedger at ht
  have hs := lowWheelFrozenTopFarOwnedSources_mass_eq_neg_products R
  unfold lowWheelFrozenTopFarOwnedSources at hs
  rw [Finset.sum_union (lowWheelFrozenTopFarOwnedSources_disjoint R)] at hs
  linear_combination hi + ht - hs

/-- Every owned product is smooth through the original inclusive root. -/
theorem lowWheelFrozenTopFarOwnedProduct_largestPrime_le_root
    {R n : ℕ} (hn : n ∈ lowWheelFrozenTopFarOwnedProducts R) :
    canonicalLargestPrimeFactor n ≤ R := by
  rcases Finset.mem_image.mp hn with ⟨y, hy, rfl⟩
  rcases Finset.mem_union.mp hy with hi | hc
  · have hterminal := (Finset.mem_filter.mp hi).1
    have hg := lowWheelCanonicalRepeatedTerminalBoundary_geometry hterminal
    have hs := orderedEulerCutShape_of_mem_carrier
      (lowWheelFrozenTopFarOwnedSource_mem_orderedEulerCutCarrier
        (Finset.mem_union_left _ hi))
    have hpred : y.1 ∈ (primesUpTo (y.2.2 - 1)).powerset := by
      apply Finset.mem_powerset.mpr
      intro r hr
      have hd := hs.2.2.2.2.1 r hr
      exact mem_primesUpTo.mpr ⟨hd.1, by omega⟩
    have hnot : y.2.2 ∉ y.1 := by
      intro h
      exact (Nat.lt_irrefl _) (hs.2.2.2.2.1 _ h).2
    have hchild : orderedEulerCutChildInteger y =
        primeFaceProduct (insert y.2.2 y.1) := by
      simp [orderedEulerCutChildInteger, orderedEulerCutHighCofactor,
        orderedEulerCutPivot, orderedEulerCutLowProduct, hg.1,
        primeFaceProduct, hnot]
    rw [hchild, canonicalLargestPrimeFactor_insert_freshPrime hs.1 hpred]
    have hle := (Finset.mem_filter.mp hi).2
    exact hg.2.1.trans_le hle
  · rw [← lowWheelFrozenCofactorTopPrime_eq_childLargest hc]
    exact (lowWheelFrozenCofactorTopPrime_lt_root hc).le

/-- Far unit primes, without their redundant cofactor-one tag. -/
def lowWheelFarPrimeUnitProducts (R : ℕ) : Finset ℕ :=
  (lowWheelFarPrimeUnitPairSet R).image Prod.snd

theorem lowWheelFarPrimeUnitProduct_prime_far
    {R p : ℕ} (hp : p ∈ lowWheelFarPrimeUnitProducts R) :
    p.Prime ∧ R + 8 ≤ p := by
  rcases Finset.mem_image.mp hp with ⟨⟨c,p⟩, hcp, rfl⟩
  have hd := mem_lowWheelFarPrimePairSet.mp
    (mem_lowWheelFarPrimeSquarefreePairSet.mp (Finset.mem_filter.mp hcp).1).1
  exact ⟨hd.2.2.1, (Finset.mem_Icc.mp hd.2.1).1⟩

theorem lowWheelFarPrimeUnitFaceMass_eq_neg_productMass (R : ℕ) :
    lowWheelFarPrimeUnitFaceMass R =
      -∑ p ∈ lowWheelFarPrimeUnitProducts R, canonicalMoebiusWeight p := by
  unfold lowWheelFarPrimeUnitFaceMass lowWheelFarPrimeUnitProducts
  rw [Finset.sum_image]
  · rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro cp hcp
    have hc1 := (Finset.mem_filter.mp hcp).2
    have hp := (mem_lowWheelFarPrimePairSet.mp
      (mem_lowWheelFarPrimeSquarefreePairSet.mp (Finset.mem_filter.mp hcp).1).1).2.2.1
    simp [canonicalMoebiusWeight, hc1, ArithmeticFunction.moebius_apply_prime hp]
  · intro a ha b hb hab
    exact Prod.ext ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm) hab

theorem lowWheelFarPrimeUnitProducts_disjoint_owned (R : ℕ) :
    Disjoint (lowWheelFarPrimeUnitProducts R) (lowWheelFrozenTopFarOwnedProducts R) := by
  rw [Finset.disjoint_left]
  intro p hp ho
  have hd := lowWheelFarPrimeUnitProduct_prime_far hp
  have hl := lowWheelFrozenTopFarOwnedProduct_largestPrime_le_root ho
  have hfac : canonicalLargestPrimeFactor p = p := by
    have h := canonicalLargestPrimeFactor_mul_prime_eq_of_rough
      (by norm_num : 0 < (1 : ℕ)) hd.1 (by
        simpa [canonicalLargestPrimeFactor] using hd.1.one_lt)
    simpa using h
  rw [hfac] at hl
  omega

/-- The disjoint arithmetic census of the unit face and both owned images. -/
def lowWheelFarWallTerminalProducts (R : ℕ) : Finset ℕ :=
  lowWheelFarPrimeUnitProducts R ∪ lowWheelFrozenTopFarOwnedProducts R

/-- Three physical terms reassemble into one true Möbius carrier. -/
theorem lowWheelFarPrimeUnit_sub_internalMate_sub_top_eq_neg_terminalMass (R : ℕ) :
    lowWheelFarPrimeUnitFaceMass R -
        lowWheelCanonicalRepeatedTerminalInternalMateLedger R -
        lowWheelFrozenCofactorTopImageLedger R =
      -∑ n ∈ lowWheelFarWallTerminalProducts R, canonicalMoebiusWeight n := by
  rw [sub_sub, lowWheelInternalMate_add_topImage_eq_ownedProductMass,
    lowWheelFarPrimeUnitFaceMass_eq_neg_productMass]
  unfold lowWheelFarWallTerminalProducts
  rw [Finset.sum_union (lowWheelFarPrimeUnitProducts_disjoint_owned R)]
  ring

/-- **Joint boundary reassembly.** All four previously separate nonrecursive
terms are now the signed difference of crossing products and terminal products.
The square-owner tag on crossing products is still present. -/
theorem lowWheelFarWall_remainingBoundary_eq_signed_products (R : ℕ) :
    lowWheelFarPrimeUnitFaceMass R - lowWheelFarPrimeQ2CrossingMass R -
        lowWheelCanonicalRepeatedTerminalInternalMateLedger R -
        lowWheelFrozenCofactorTopImageLedger R =
      (∑ x ∈ lowWheelFarPrimeCrossingProductCarrier R, canonicalMoebiusWeight x.2) -
        ∑ n ∈ lowWheelFarWallTerminalProducts R, canonicalMoebiusWeight n := by
  have h := lowWheelFarPrimeUnit_sub_internalMate_sub_top_eq_neg_terminalMass R
  rw [lowWheelFarPrimeQ2CrossingMass_eq_neg_productMass]
  linear_combination h

/-- The complete hard residual with the descended packet still attached. -/
theorem lowWheelFrozenTopFarResidual_eq_descended_add_crossing_sub_terminal
    (R : ℕ) (hR : 56 ≤ R) :
    lowWheelFrozenTopFarResidual R =
      (∑ x ∈ lowWheelFarPrimeDescendedProductCarrier R, canonicalMoebiusWeight x.2) +
      (∑ x ∈ lowWheelFarPrimeCrossingProductCarrier R, canonicalMoebiusWeight x.2) -
        ∑ n ∈ lowWheelFarWallTerminalProducts R, canonicalMoebiusWeight n := by
  have h := lowWheelFarWall_remainingBoundary_eq_signed_products R
  rw [lowWheelFrozenTopFarResidual_eq_unit_sub_descended_sub_crossing_sub_owned R hR,
    lowWheelFarPrimeQ2DescendedMass_eq_neg_productMass]
  linear_combination h

/-- The integer homes on which the remaining four populations can interact. -/
def lowWheelFarWallBoundaryProductHomes (R : ℕ) : Finset ℕ :=
  (lowWheelFarPrimeCrossingProductCarrier R).image Prod.snd ∪
    lowWheelFarWallTerminalProducts R

/-- All crossing owners at a fixed integer, with their exact multiplicity. -/
def lowWheelFarWallCrossingMultiplicity (R n : ℕ) : ℕ :=
  ((lowWheelFarPrimeCrossingProductCarrier R).filter fun x => x.2 = n).card

/-- Signed incidence after reassembling the crossing and terminal occurrences.
This is an integer difference, not truncated natural subtraction. -/
def lowWheelFarWallBoundaryCoefficient (R n : ℕ) : ℤ :=
  (lowWheelFarWallCrossingMultiplicity R n : ℤ) -
    if n ∈ lowWheelFarWallTerminalProducts R then 1 else 0

/-- Finite Fubini at the integer homes retains every crossing owner. -/
theorem lowWheelFarPrimeCrossingProduct_sum_eq_multiplicity (R : ℕ) :
    (∑ x ∈ lowWheelFarPrimeCrossingProductCarrier R, canonicalMoebiusWeight x.2) =
      ∑ n ∈ lowWheelFarWallBoundaryProductHomes R,
        (lowWheelFarWallCrossingMultiplicity R n : ℂ) * canonicalMoebiusWeight n := by
  have hf := Finset.sum_fiberwise_of_maps_to
    (s := lowWheelFarPrimeCrossingProductCarrier R)
    (t := lowWheelFarWallBoundaryProductHomes R) (g := Prod.snd)
    (fun x hx => Finset.mem_union_left _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩))
    (fun x => canonicalMoebiusWeight x.2)
  rw [← hf]
  apply Finset.sum_congr rfl
  intro n _hn
  calc
    (∑ x ∈ lowWheelFarPrimeCrossingProductCarrier R with x.2 = n,
        canonicalMoebiusWeight x.2) =
      ∑ _x ∈ (lowWheelFarPrimeCrossingProductCarrier R).filter (fun x => x.2 = n),
        canonicalMoebiusWeight n := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [(Finset.mem_filter.mp hx).2]
    _ = _ := by simp [lowWheelFarWallCrossingMultiplicity]

private theorem terminalProducts_sum_eq_indicator (R : ℕ) :
    (∑ n ∈ lowWheelFarWallTerminalProducts R, canonicalMoebiusWeight n) =
      ∑ n ∈ lowWheelFarWallBoundaryProductHomes R,
        if n ∈ lowWheelFarWallTerminalProducts R then canonicalMoebiusWeight n else 0 := by
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext n
    simp [lowWheelFarWallBoundaryProductHomes]
  · intro n _hn
    rfl

/-- **Signed reassembly before energy.**  The four-term boundary is one
Möbius sum whose integer coefficient has already subtracted every terminal
occurrence from its full crossing-owner fibre.  No norm, sign assumption,
unproved multiplicity-one substitution, or boundary estimate is used. -/
theorem lowWheelFarWall_remainingBoundary_eq_coefficient_sum (R : ℕ) :
    lowWheelFarPrimeUnitFaceMass R - lowWheelFarPrimeQ2CrossingMass R -
        lowWheelCanonicalRepeatedTerminalInternalMateLedger R -
        lowWheelFrozenCofactorTopImageLedger R =
      ∑ n ∈ lowWheelFarWallBoundaryProductHomes R,
        (lowWheelFarWallBoundaryCoefficient R n : ℂ) * canonicalMoebiusWeight n := by
  rw [lowWheelFarWall_remainingBoundary_eq_signed_products,
    lowWheelFarPrimeCrossingProduct_sum_eq_multiplicity, terminalProducts_sum_eq_indicator,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  by_cases hn : n ∈ lowWheelFarWallTerminalProducts R
  · simp [lowWheelFarWallBoundaryCoefficient, hn, sub_mul]
  · simp [lowWheelFarWallBoundaryCoefficient, hn]

/-- Crossing products cannot also be either old owned image: they retain a
prime strictly beyond the inclusive root wheel. -/
theorem lowWheelFarPrimeCrossingProduct_not_owned
    {R : ℕ} {x : ℕ × ℕ}
    (hx : x ∈ lowWheelFarPrimeCrossingProductCarrier R) :
    x.2 ∉ lowWheelFrozenTopFarOwnedProducts R := by
  rcases Finset.mem_image.mp hx with ⟨t, ht, rfl⟩
  intro ho
  have hfar := (lowWheelFarPrimeProduct_geometry (Finset.mem_filter.mp ht).1).2.2.2
  have hlow := lowWheelFrozenTopFarOwnedProduct_largestPrime_le_root ho
  omega

/-- The exact complement census: on a crossing fibre the subtracted terminal
occurrence is a unit far prime, and never an internal or top-image occurrence. -/
theorem lowWheelFarPrimeCrossingProduct_mem_terminal_iff_unit
    {R : ℕ} {x : ℕ × ℕ}
    (hx : x ∈ lowWheelFarPrimeCrossingProductCarrier R) :
    x.2 ∈ lowWheelFarWallTerminalProducts R ↔ x.2 ∈ lowWheelFarPrimeUnitProducts R := by
  change x.2 ∈ lowWheelFarPrimeUnitProducts R ∪ lowWheelFrozenTopFarOwnedProducts R ↔ _
  simp only [Finset.mem_union, lowWheelFarPrimeCrossingProduct_not_owned hx, or_false]

/-- A concrete regression against silently replacing a crossing-owner fibre
by one occurrence: owners 3 and 5 both represent the same far prime 23. -/
theorem lowWheelFarWallCrossingMultiplicity_twelve_twentyThree_ge_two :
    2 ≤ lowWheelFarWallCrossingMultiplicity 12 23 := by
  have hmem (q : ℕ) (hq : q = 3 ∨ q = 5) :
      (q,23) ∈ lowWheelFarPrimeCrossingProductCarrier 12 := by
    have htr : (q,(1,23)) ∈ lowWheelFarPrimeLowCofactorTriples 12 := by
      apply lowWheelFarPrimeLowCofactorTriple_mem_of_data
      all_goals rcases hq with rfl | rfl <;>
        norm_num [canonicalLargestPrimeFactor, squareRootEndpoint]
    apply Finset.mem_image.mpr
    refine ⟨(q,(1,23)), Finset.mem_filter.mpr ⟨htr, ?_⟩, rfl⟩
    rcases hq with rfl | rfl <;> norm_num [squareRootEndpoint]
  have hsub : ({(3,23),(5,23)} : Finset (ℕ × ℕ)) ⊆
      (lowWheelFarPrimeCrossingProductCarrier 12).filter (fun x => x.2 = 23) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨hmem 3 (Or.inl rfl), rfl⟩
    · exact Finset.mem_filter.mpr ⟨hmem 5 (Or.inr rfl), rfl⟩
  have hcard := Finset.card_le_card hsub
  norm_num only [Finset.card_insert_of_notMem (by decide : (3,23) ∉ ({(5,23)} : Finset (ℕ × ℕ))),
    Finset.card_singleton] at hcard
  exact hcard

end RHLean.Proof
