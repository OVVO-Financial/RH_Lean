import Mathlib
import RHLean.Proof.SquareRootLowPrimeCombinedTaggedElevenPushforward
import RHLean.Proof.SquareRootLowPrimeGoRootFloorTerminalSplit
import RHLean.Proof.LowWheelCanonicalRepeatedFrozenCofactorMate
import RHLean.Proof.LowWheelFrozenSecondContactRoughPrefix

/-!
# Source-side normal form of the old physical residual

This file is structural.  It takes no norm and introduces no estimate.
It rewrites the opaque far set-difference residual in the source/partner
coordinates already used by the saturated second-contact and RoughPrefix
machinery, then performs the six finite population comparisons required by
#646 in one common tagged currency.
-/

noncomputable section

open scoped BigOperators ArithmeticFunction.Moebius

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis
open FrozenCofactorTopBottom
open CanonicalGapAncestryBridge

attribute [local instance] Classical.propDecidable

/-- The one-shot product-one mate used by the RoughPrefix source-scale
cancellation and the frozen top image used in the old residual are different
physical images of the same frozen source ledger, hence have exactly the same
signed mass. -/
theorem lowWheelCanonicalRepeatedFrozenProductOneMateLedger_eq_topImageLedger
    (R : ℕ) :
    lowWheelCanonicalRepeatedFrozenProductOneMateLedger R =
      lowWheelFrozenCofactorTopImageLedger R := by
  have hprod :=
    sum_lowWheelCanonicalRepeatedFrozenCofactor_add_productOneMate_eq_zero R
  have htop := lowWheelFrozenCofactorTopImageLedger_eq_neg R
  change lowWheelCanonicalFrozenCofactorLedger R +
      lowWheelCanonicalRepeatedFrozenProductOneMateLedger R = 0 at hprod
  linear_combination hprod - htop

/-- **Exact source-side normal form of the old hard physical residual.**
After the full far Othello cancellation, the residual is one stable far packet
plus the source-side frozen-cofactor and internal-terminal ledgers, together
with the literal at-most-seven near internal mate strip.  No term is bounded or
dropped. -/
theorem lowWheelFrozenTopFarPhysicalResidualLedger_eq_sourceNormalForm
    {R : ℕ} (hR : 6 ≤ R) :
    lowWheelFrozenTopFarPhysicalResidualLedger R =
      (∑ z ∈ lowWheelFarTaggedPhysicalStableCarrier R,
        lowWheelFullTaggedPhysicalWeight z) +
      lowWheelCanonicalFrozenCofactorLedger R +
      lowWheelCanonicalRepeatedTerminalInternalLedger R +
      lowWheelCanonicalRepeatedTerminalInternalMateNearLedger R := by
  have hfar := lowWheelFarTaggedPhysicalLedger_eq_residual_add_farMate_add_top R hR
  have hstable := lowWheelFarTaggedPhysicalLedger_eq_stable R
  have hsplit := lowWheelCanonicalRepeatedTerminalInternalMateLedger_eq_near_add_far R
  have hinter := lowWheelCanonicalRepeatedTerminalInternalLedger_eq_neg_mateLedger R
  have htop := lowWheelFrozenCofactorTopImageLedger_eq_neg R
  linear_combination -hfar + hstable + hsplit - htop - hinter

/-- The same normal form with the frozen top image written as the historical
product-one mate used by RoughPrefix.  This makes the sign comparison explicit:
the old residual contains the *negative* of that mate ledger. -/
theorem lowWheelFrozenTopFarPhysicalResidualLedger_eq_stable_sub_mates
    {R : ℕ} (hR : 6 ≤ R) :
    lowWheelFrozenTopFarPhysicalResidualLedger R =
      (∑ z ∈ lowWheelFarTaggedPhysicalStableCarrier R,
        lowWheelFullTaggedPhysicalWeight z) -
      lowWheelCanonicalRepeatedTerminalInternalMateFarLedger R -
      lowWheelCanonicalRepeatedFrozenProductOneMateLedger R := by
  have hfar := lowWheelFarTaggedPhysicalLedger_eq_residual_add_farMate_add_top R hR
  have hstable := lowWheelFarTaggedPhysicalLedger_eq_stable R
  have htop :=
    lowWheelCanonicalRepeatedFrozenProductOneMateLedger_eq_topImageLedger R
  linear_combination -hfar + hstable + htop

/-- Combined #643/#645 interior in the source-side normal form.  The full-face
Go source remains signed together with the old source sectors; no boundary or
energy interpretation is inserted. -/
theorem oldResidual_add_fullFaceDefect_eq_sourceNormalForm_add_defect
    {R : ℕ} (hR : 6 ≤ R) :
    lowWheelFrozenTopFarPhysicalResidualLedger R +
        ((squareRootLowPrimeGoFullFaceDefectSourceMass R : ℤ) : ℂ) =
      (∑ z ∈ lowWheelFarTaggedPhysicalStableCarrier R,
        lowWheelFullTaggedPhysicalWeight z) +
      lowWheelCanonicalFrozenCofactorLedger R +
      lowWheelCanonicalRepeatedTerminalInternalLedger R +
      lowWheelCanonicalRepeatedTerminalInternalMateNearLedger R +
      ((squareRootLowPrimeGoFullFaceDefectSourceMass R : ℤ) : ℂ) := by
  rw [lowWheelFrozenTopFarPhysicalResidualLedger_eq_sourceNormalForm hR]

/-! ## Common currency for the six finite comparisons -/

/-- One common tagged currency for the #646 population comparison. -/
inductive CombinedResidualAtom (R : ℕ) where
  | seed (s : SourceIndex (squareRootEndpoint R))
  | uniqueRoot (y : LowWheelTaggedDowncrossState)
  | repeatedTerminal (y : LowWheelTaggedDowncrossState)
  | nearStrip (z : LowWheelFullTaggedPhysicalState)
  | stableFar (z : LowWheelFullTaggedPhysicalState)
  deriving DecidableEq

/-- Signed weight attached to the common currency.  No absolute value is taken. -/
noncomputable def combinedResidualAtomWeight {R : ℕ} : CombinedResidualAtom R → ℂ
  | .seed s => ((sourceGeneration (squareRootEndpoint R) 1 s : ℤ) : ℂ)
  | .uniqueRoot y => lowWheelTaggedDowncrossWeight y
  | .repeatedTerminal y => lowWheelTaggedDowncrossWeight y
  | .nearStrip z => lowWheelFullTaggedPhysicalWeight z
  | .stableFar z => lowWheelFullTaggedPhysicalWeight z

/-- Arithmetic high-product key used only to compare populations of different
Lean types.  For a canonical seed this is its represented source product. -/
def combinedResidualAtomHighProduct {R : ℕ} : CombinedResidualAtom R → ℕ
  | .seed s => sourceProduct s
  | .uniqueRoot y => lowWheelTaggedHighProduct y
  | .repeatedTerminal y => lowWheelTaggedHighProduct y
  | .nearStrip z => lowWheelTaggedHighProduct z
  | .stableFar z => lowWheelTaggedHighProduct z

/-! ## Lemma 1: deep Go is one canonical seed, not an extra copy -/

/-- **Lemma 1.**  Every deep full-face defect has exactly one saturated
`SourceIndex` with the same `(q,r*d)` coordinates, and its physical source
weight is exactly generation one at that seed.  Thus the deep Go occurrence is
an alias of one seed in source coordinates, not a second additive seed. -/
theorem deepDefect_sourceIndex_eq_canonicalSeed
    {R r q d : ℕ}
    (hz : ((r, q), d) ∈ squareRootLowPrimeGoFullFaceDefectSaturatedIncidences R) :
    ∃! s : SourceIndex (squareRootEndpoint R),
      s ∈ lowWheelFrozenSecondContactCanonicalSeeds R ∧
      sourcePrime s = q ∧
      sourceCore s = r * d ∧
      lowWheelFullTaggedPhysicalWeight
          (squareRootLowPrimeGoFullFaceDefectSourceTag ((r, q), d)) =
        ((sourceGeneration (squareRootEndpoint R) 1 s : ℤ) : ℂ) := by
  rcases squareRootLowPrimeGoFullFaceDefectSaturated_exists_canonicalSeed hz with
    ⟨s, hs, hsq, hsc, _hgen⟩
  have hzFull :=
    (mem_squareRootLowPrimeGoFullFaceDefectSaturatedIncidences.mp hz).1
  rcases squareRootLowPrimeGoFullFaceDefect_depthOneAncestry hzFull with
    ⟨parent, t, _hpq, _hpd, htq, htc, _htrans, _hsmooth, _hparent, hweight⟩
  have hts : t = s := by
    apply Prod.ext
    · apply Fin.ext
      simpa [sourcePrime] using htq.trans hsq.symm
    · apply Fin.ext
      simpa [sourceCore] using htc.trans hsc.symm
  subst t
  refine ⟨s, ⟨hs, hsq, hsc, hweight⟩, ?_⟩
  intro u hu
  apply Prod.ext
  · apply Fin.ext
    simpa [sourcePrime] using hu.2.1.trans hsq.symm
  · apply Fin.ext
    simpa [sourceCore] using hu.2.2.1.trans hsc.symm

/-- Deep Go seeds, now literally a subset of the canonical saturated seed
carrier rather than a separately added physical ledger. -/
noncomputable def deepGoCanonicalSeedCarrier (R : ℕ) :
    Finset (SourceIndex (squareRootEndpoint R)) :=
  (lowWheelFrozenSecondContactCanonicalSeeds R).filter fun s =>
    ∃ z ∈ squareRootLowPrimeGoFullFaceDefectSaturatedIncidences R,
      sourcePrime s = z.1.2 ∧ sourceCore s = z.1.1 * z.2

/-- The deep-Go seed image cannot leave the canonical saturated carrier. -/
theorem deepGoCanonicalSeedCarrier_subset (R : ℕ) :
    deepGoCanonicalSeedCarrier R ⊆ lowWheelFrozenSecondContactCanonicalSeeds R := by
  intro s hs
  exact (Finset.mem_filter.mp hs).1

/-! ## Lemma 2: split the remaining canonical cofactor seeds exactly -/

/-- Canonical saturated seeds not already named by a deep Go incidence. -/
noncomputable def otherCofactorSeeds (R : ℕ) :
    Finset (SourceIndex (squareRootEndpoint R)) :=
  lowWheelFrozenSecondContactCanonicalSeeds R \ deepGoCanonicalSeedCarrier R

/-- **Lemma 2.**  In the common `SourceIndex` currency there is no additive
`deep + frozen` double count: the saturated seed population is exactly the
union of the deep-Go image and its literal finite complement. -/
theorem frozenCofactorSeeds_eq_deepGo_union_otherCofactorSeeds (R : ℕ) :
    lowWheelFrozenSecondContactCanonicalSeeds R =
      deepGoCanonicalSeedCarrier R ∪ otherCofactorSeeds R := by
  ext s
  constructor
  · intro hs
    by_cases hd : s ∈ deepGoCanonicalSeedCarrier R
    · exact Finset.mem_union.mpr (Or.inl hd)
    · exact Finset.mem_union.mpr (Or.inr <|
        Finset.mem_sdiff.mpr ⟨hs, hd⟩)
  · intro hs
    rcases Finset.mem_union.mp hs with hd | ho
    · exact deepGoCanonicalSeedCarrier_subset R hd
    · exact (Finset.mem_sdiff.mp ho).1

/-- The two seed classes in Lemma 2 are disjoint. -/
theorem deepGoCanonicalSeeds_disjoint_otherCofactorSeeds (R : ℕ) :
    Disjoint (deepGoCanonicalSeedCarrier R) (otherCofactorSeeds R) := by
  rw [Finset.disjoint_left]
  intro s hd ho
  exact (Finset.mem_sdiff.mp ho).2 hd

/-- Every `other` seed still satisfies the exact saturated window; there is no
unnamed same-scale seed class hidden in the complement. -/
theorem otherCofactorSeed_mem_saturatedWindow
    {R : ℕ} {s : SourceIndex (squareRootEndpoint R)}
    (hs : s ∈ otherCofactorSeeds R) :
    SourceAdmissible s ∧
      sourcePrime s < R ∧
      max R
          (squareRootEndpoint R /
            (sourcePrime s * sourcePrime s)) < sourceCore s ∧
      sourceCore s ≤ squareRootEndpoint R / sourcePrime s := by
  exact mem_lowWheelFrozenSecondContactCanonicalSeeds_iff.mp
    (Finset.mem_sdiff.mp hs).1

/-! ## Lemma 3: RoughPrefix partners are an existing finite subpopulation -/

/-- Frozen cofactor sources whose source scale is represented by at least one
actual second-contact source.  These are exactly the source fibres used by the
RoughPrefix cancellation. -/
def lowWheelFrozenSecondContactMatchingSourceCarrier (R : ℕ) :
    Finset LowWheelTaggedDowncrossState :=
  (lowWheelCanonicalRepeatedFrozenCofactorPart R).filter fun y =>
    lowWheelFrozenSecondContactSourceScale y ∈
      lowWheelFrozenSecondContactSourceScaleSet R

/-- The corresponding one-shot historical product-one mates. -/
def lowWheelFrozenSecondContactMatchingProductOneMateCarrier (R : ℕ) :
    Finset LowWheelTaggedCofactorQuotientState :=
  (lowWheelFrozenSecondContactMatchingSourceCarrier R).image
    lowWheelCanonicalRepeatedFrozenProductOneMate

/-- Same RoughPrefix partner population written as the union of its fixed-scale
transport fibres. -/
def lowWheelFrozenSecondContactRoughPrefixPartnerCarrier (R : ℕ) :
    Finset LowWheelTaggedCofactorQuotientState :=
  (lowWheelFrozenSecondContactSourceScaleSet R).biUnion fun A =>
    lowWheelFrozenSourceScaleTransportCarrier R A

/-- **Lemma 3.**  The RoughPrefix partner census is exact: the scale-by-scale
transport union is the image of the matching frozen sources, that image is a
subpopulation of the already-existing global product-one mate image, and every
genuine second-contact source is in the matching source population. -/
theorem roughPrefixPartners_are_already_existing_population (R : ℕ) :
    lowWheelFrozenSecondContactRoughPrefixPartnerCarrier R =
        lowWheelFrozenSecondContactMatchingProductOneMateCarrier R ∧
    lowWheelFrozenSecondContactMatchingProductOneMateCarrier R ⊆
        lowWheelCanonicalRepeatedFrozenProductOneMateImage R ∧
    lowWheelCanonicalRepeatedFrozenSecondContactPart R ⊆
        lowWheelFrozenSecondContactMatchingSourceCarrier R := by
  constructor
  · ext z
    constructor
    · intro hz
      rcases Finset.mem_biUnion.mp hz with ⟨A, hA, hzA⟩
      rcases Finset.mem_image.mp hzA with ⟨y, hyA, rfl⟩
      have hyData := Finset.mem_filter.mp hyA
      apply Finset.mem_image.mpr
      refine ⟨y, Finset.mem_filter.mpr ⟨hyData.1, ?_⟩, rfl⟩
      simpa [hyData.2] using hA
    · intro hz
      rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
      have hyData := Finset.mem_filter.mp hy
      apply Finset.mem_biUnion.mpr
      refine ⟨lowWheelFrozenSecondContactSourceScale y, hyData.2, ?_⟩
      apply Finset.mem_image.mpr
      exact ⟨y, Finset.mem_filter.mpr ⟨hyData.1, rfl⟩, rfl⟩
  constructor
  · intro z hz
    rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
    exact Finset.mem_image.mpr ⟨y, (Finset.mem_filter.mp hy).1, rfl⟩
  · intro y hy
    apply Finset.mem_filter.mpr
    refine ⟨(Finset.mem_filter.mp hy).1, ?_⟩
    unfold lowWheelFrozenSecondContactSourceScaleSet
    exact Finset.mem_image.mpr ⟨y, hy, rfl⟩

/-! ## Lemma 4: root floor is exactly unique-root or repeated terminal -/

/-- Root-floor defect incidences whose literal downcross source has a unique
root parent. -/
def squareRootLowPrimeGoRootFloorUniqueIncidences (R : ℕ) :
    Finset SquareRootLowPrimeGoFullFaceDefectIncidence :=
  (squareRootLowPrimeGoFullFaceDefectRootFloorIncidences R).filter fun z =>
    squareRootLowPrimeGoFullFaceDefectSourceTag z ∈
      lowWheelCanonicalDowncrossUniqueParentPart R

/-- Root-floor defect incidences whose literal downcross source is an internal
repeated-terminal state. -/
def squareRootLowPrimeGoRootFloorRepeatedTerminalIncidences (R : ℕ) :
    Finset SquareRootLowPrimeGoFullFaceDefectIncidence :=
  (squareRootLowPrimeGoFullFaceDefectRootFloorIncidences R).filter fun z =>
    squareRootLowPrimeGoFullFaceDefectSourceTag z ∈
      lowWheelCanonicalRepeatedTerminalInternalPart R

/-- **Lemma 4.**  The root-floor incidence population is exhausted by the two
existing root constructors, and no root-floor incidence has a canonical seed
with the same `(q,r*d)` coordinates. -/
theorem rootFloor_population_eq_unique_union_repeated_and_disjoint_seed
    {R : ℕ} (hR : 2 ≤ R) :
    squareRootLowPrimeGoFullFaceDefectRootFloorIncidences R =
        squareRootLowPrimeGoRootFloorUniqueIncidences R ∪
          squareRootLowPrimeGoRootFloorRepeatedTerminalIncidences R ∧
    (∀ r q d,
      ((r, q), d) ∈ squareRootLowPrimeGoFullFaceDefectRootFloorIncidences R →
      ¬ ∃ s : SourceIndex (squareRootEndpoint R),
        s ∈ lowWheelFrozenSecondContactCanonicalSeeds R ∧
        sourcePrime s = q ∧ sourceCore s = r * d) := by
  constructor
  · ext z
    rcases z with ⟨⟨r, q⟩, d⟩
    constructor
    · intro hz
      rcases squareRootLowPrimeGoFullFaceDefectRootFloorSource_unique_or_internalTerminal
          hR hz with hu | ht
      · exact Finset.mem_union.mpr <| Or.inl <|
          Finset.mem_filter.mpr ⟨hz, hu⟩
      · exact Finset.mem_union.mpr <| Or.inr <|
          Finset.mem_filter.mpr ⟨hz, ht⟩
    · intro hz
      rcases Finset.mem_union.mp hz with hu | ht
      · exact (Finset.mem_filter.mp hu).1
      · exact (Finset.mem_filter.mp ht).1
  · intro r q d hz
    exact squareRootLowPrimeGoFullFaceDefectRootFloor_no_matching_canonicalSeed hz

/-- The two root-floor classes are disjoint before any sum is taken. -/
theorem rootFloorUnique_disjoint_repeatedTerminal (R : ℕ) :
    Disjoint (squareRootLowPrimeGoRootFloorUniqueIncidences R)
      (squareRootLowPrimeGoRootFloorRepeatedTerminalIncidences R) := by
  rw [Finset.disjoint_left]
  intro z hu ht
  have hyU := (Finset.mem_filter.mp hu).2
  have hyT := (Finset.mem_filter.mp ht).2
  have hterminal := (Finset.mem_filter.mp hyT).1
  have hfrozen := (Finset.mem_filter.mp hterminal).1
  have hrepeated := (Finset.mem_filter.mp hfrozen).1
  exact (Finset.disjoint_left.mp
    (lowWheelCanonicalDowncrossUnique_disjoint_repeated R)) hyU hrepeated

/-! ## Lemma 5: unique root is a named incomplete boundary -/

/-- The incomplete boundary in the common tagged currency.  It contains only
root-floor unique occurrences, root-floor repeated internal terminals, and the
already-named seven-integer near physical strip. -/
def taggedElevenIncompleteBoundaryAtoms (R : ℕ) :
    Finset (CombinedResidualAtom R) :=
  (squareRootLowPrimeGoRootFloorUniqueIncidences R).image
      (fun z => CombinedResidualAtom.uniqueRoot
        (squareRootLowPrimeGoFullFaceDefectSourceTag z)) ∪
    ((squareRootLowPrimeGoRootFloorRepeatedTerminalIncidences R).image
        (fun z => CombinedResidualAtom.repeatedTerminal
          (squareRootLowPrimeGoFullFaceDefectSourceTag z)) ∪
      (lowWheelCanonicalRepeatedTerminalInternalMateNearImage R).image
        (fun z => CombinedResidualAtom.nearStrip z))

/-- **Lemma 5.**  A unique-parent root-floor incidence is literally an
incomplete-boundary atom and its parent coordinate is supported at scale `R`.
No same-scale far leakage is asserted. -/
theorem uniqueParentRoot_is_incompleteBoundary
    {R r q d : ℕ} (hR : 2 ≤ R)
    (hz : ((r, q), d) ∈ squareRootLowPrimeGoRootFloorUniqueIncidences R) :
    CombinedResidualAtom.uniqueRoot
        (squareRootLowPrimeGoFullFaceDefectSourceTag ((r, q), d)) ∈
          taggedElevenIncompleteBoundaryAtoms R ∧
      lowWheelCanonicalDowncrossParent
          (squareRootLowPrimeGoFullFaceDefectSourceTag ((r, q), d)) ≤ R := by
  have hzRoot := (Finset.mem_filter.mp hz).1
  constructor
  · unfold taggedElevenIncompleteBoundaryAtoms
    apply Finset.mem_union.mpr
    left
    exact Finset.mem_image.mpr ⟨((r, q), d), hz, rfl⟩
  · exact lowWheelCanonicalDowncrossParent_le_root
      (squareRootLowPrimeGoFullFaceDefectRootFloorSource_mem_downcross hR hzRoot)

/-! ## Lemma 6: stable far is either accounted or the named wall -/

/-- Literal arithmetic integers in the RoughPrefix square-residual output.
The outer source scale is retained in the product `A*c`; no absolute values are
taken and no multiplicity is collapsed in any weighted statement. -/
def lowWheelFrozenSecondContactSquareResidualIntegerCarrier (R : ℕ) : Finset ℕ :=
  (lowWheelFrozenSecondContactSourceScaleSet R).biUnion fun A =>
    (lowWheelFrozenSourceSquareResidual (canonicalLargestPrimeFactor A)
      (squareRootEndpoint R / A)).image fun c => A * c

/-- High products already named by canonical seeds. -/
def combinedCanonicalSeedHighProducts (R : ℕ) : Finset ℕ :=
  (lowWheelFrozenSecondContactCanonicalSeeds R).image sourceProduct

/-- High products of the historical RoughPrefix partner population. -/
def combinedRoughPrefixPartnerHighProducts (R : ℕ) : Finset ℕ :=
  (lowWheelFrozenSecondContactRoughPrefixPartnerCarrier R).image
    lowWheelTaggedHighProduct

/-- High products of the root-floor unique boundary. -/
def combinedRootFloorUniqueHighProducts (R : ℕ) : Finset ℕ :=
  (squareRootLowPrimeGoRootFloorUniqueIncidences R).image fun z =>
    lowWheelTaggedHighProduct (squareRootLowPrimeGoFullFaceDefectSourceTag z)

/-- High products of the repeated internal root-floor boundary. -/
def combinedRootFloorRepeatedHighProducts (R : ℕ) : Finset ℕ :=
  (squareRootLowPrimeGoRootFloorRepeatedTerminalIncidences R).image fun z =>
    lowWheelTaggedHighProduct (squareRootLowPrimeGoFullFaceDefectSourceTag z)

/-- High products in the literal near internal-terminal mate strip. -/
def combinedNearStripHighProducts (R : ℕ) : Finset ℕ :=
  (lowWheelCanonicalRepeatedTerminalInternalMateNearImage R).image
    lowWheelTaggedHighProduct

/-- Every arithmetic high product already accounted for by Lemmas 1--5 or by
the actual RoughPrefix square-residual output. -/
def combinedAccountedHighProducts (R : ℕ) : Finset ℕ :=
  combinedCanonicalSeedHighProducts R ∪
    combinedRoughPrefixPartnerHighProducts R ∪
    combinedRootFloorUniqueHighProducts R ∪
    combinedRootFloorRepeatedHighProducts R ∪
    combinedNearStripHighProducts R ∪
    lowWheelFrozenSecondContactSquareResidualIntegerCarrier R

/-- Stable-far states whose invariant high product is already represented by
the named populations. -/
def stableFarAccountedCarrier (R : ℕ) : Finset LowWheelFullTaggedPhysicalState :=
  (lowWheelFarTaggedPhysicalStableCarrier R).filter fun z =>
    lowWheelTaggedHighProduct z ∈ combinedAccountedHighProducts R

/-- **The only allowed wall constructor.**  These are literal stable-far states
whose invariant high product is absent from every population named above. -/
def stableFarWallCarrier (R : ℕ) : Finset LowWheelFullTaggedPhysicalState :=
  (lowWheelFarTaggedPhysicalStableCarrier R).filter fun z =>
    lowWheelTaggedHighProduct z ∉ combinedAccountedHighProducts R

/-- Stable far splits exactly into accounted states and the named wall. -/
theorem stableFar_eq_accounted_union_wall (R : ℕ) :
    lowWheelFarTaggedPhysicalStableCarrier R =
      stableFarAccountedCarrier R ∪ stableFarWallCarrier R := by
  ext z
  by_cases h : lowWheelTaggedHighProduct z ∈ combinedAccountedHighProducts R
  · simp [stableFarAccountedCarrier, stableFarWallCarrier, h]
  · simp [stableFarAccountedCarrier, stableFarWallCarrier, h]

/-- The two sides of the stable-far split are disjoint. -/
theorem stableFarAccounted_disjoint_wall (R : ℕ) :
    Disjoint (stableFarAccountedCarrier R) (stableFarWallCarrier R) := by
  rw [Finset.disjoint_left]
  intro z ha hw
  exact (Finset.mem_filter.mp hw).2 (Finset.mem_filter.mp ha).2

/-- **Lemma 6.**  The final census has exactly the three permitted outcomes:
`6a` stable far is empty; `6b` every stable-far high product is already in the
named assembly/RoughPrefix image; or `6c` there is a concrete stable-far wall
state.  The third branch names the constructor and stops--it is not converted
into a norm or a new residual ledger. -/
theorem stableFar_empty_or_accounted_or_wall (R : ℕ) :
    lowWheelFarTaggedPhysicalStableCarrier R = ∅ ∨
      (stableFarWallCarrier R = ∅ ∧
        lowWheelFarTaggedPhysicalStableCarrier R = stableFarAccountedCarrier R) ∨
      ∃ z,
        z ∈ lowWheelFarTaggedPhysicalStableCarrier R ∧
        z ∈ stableFarWallCarrier R ∧
        lowWheelTaggedHighProduct z ∉ combinedAccountedHighProducts R := by
  by_cases hs : lowWheelFarTaggedPhysicalStableCarrier R = ∅
  · exact Or.inl hs
  · right
    by_cases hw : stableFarWallCarrier R = ∅
    · left
      refine ⟨hw, ?_⟩
      rw [stableFar_eq_accounted_union_wall R, hw, Finset.union_empty]
    · right
      have hne : (stableFarWallCarrier R).Nonempty := Finset.nonempty_iff_ne_empty.mpr hw
      rcases hne with ⟨z, hz⟩
      exact ⟨z, (Finset.mem_filter.mp hz).1, hz, (Finset.mem_filter.mp hz).2⟩

end RHLean.Proof