import Mathlib
import RHLean.Proof.CanonicalGapAncestryBridge
import RHLean.Proof.LowWheelFrozenSecondContactGlobalTelescope
import RHLean.Proof.SquareRootLowPrimeTSectorQ2Renormalization

/-!
# Arithmetic scale and sign of frozen second-contact flux

These declarations depend on the completed transport development and therefore
live downstream of it. The foundational UniformResidualBound module cannot
import them without creating a cycle through MobiusRenewalTelescope.
-/

noncomputable section

open scoped BigOperators ArithmeticFunction.Moebius

namespace RHLean.Proof

open RHLean.Arithmetic
open CanonicalGapAncestryBridge

attribute [local instance] Classical.propDecidable

/-- The #627 predecessor face is literally the source scale times the canonical
cofactor left after stripping the second-contact owner. -/
theorem lowWheelFrozenSecondContact_parentFaceProduct_eq_sourceScale_mul_canonicalCofactor
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R) :
    primeFaceProduct (lowWheelFrozenSecondContactParentFace y) =
      lowWheelFrozenSecondContactSourceScale y * canonicalCofactor y.2.1 := by
  have hyFrozen := (Finset.mem_filter.mp hy).1
  have hcgt :=
    (lowWheelCanonicalRepeatedFrozenCofactor_source_data hyFrozen).2.2.2.2.1
  have hfactor :
      canonicalCofactor y.2.1 * lowWheelFrozenCofactorTopPrime y = y.2.1 := by
    simpa [lowWheelFrozenCofactorTopPrime] using
      (canonicalCofactor_mul_largestPrimeFactor hcgt)
  have heq :
      lowWheelFrozenCofactorTopPrime y *
          primeFaceProduct (lowWheelFrozenSecondContactParentFace y) =
        lowWheelFrozenCofactorTopPrime y *
          (lowWheelFrozenSecondContactSourceScale y * canonicalCofactor y.2.1) := by
    calc
      lowWheelFrozenCofactorTopPrime y *
          primeFaceProduct (lowWheelFrozenSecondContactParentFace y) =
        primeFaceProduct (lowWheelCanonicalRepeatedFrozenProductOneFace y) :=
          lowWheelFrozenSecondContact_owner_mul_parentFaceProduct hyFrozen
      _ = y.2.1 * lowWheelTaggedDowncrossPivot y * primeFaceProduct y.1 :=
          lowWheelCanonicalRepeatedFrozenProductOneFace_product hyFrozen
      _ = lowWheelFrozenCofactorTopPrime y *
          (lowWheelFrozenSecondContactSourceScale y * canonicalCofactor y.2.1) := by
        conv_lhs => rw [← hfactor]
        unfold lowWheelFrozenSecondContactSourceScale
        ac_rfl
  have hqpos : 0 < lowWheelFrozenCofactorTopPrime y :=
    (lowWheelFrozenCofactorTopPrime_data hyFrozen).1.pos
  exact Nat.mul_left_cancel hqpos heq

/-- After stripping the second-contact owner, the source sign is exactly the
product of the source-scale Möbius sign and the stripped-cofactor Möbius sign. -/
theorem lowWheelFrozenSecondContact_sourceWeight_eq_scale_mul_canonicalCofactor
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R) :
    canonicalMoebiusWeight y.2.1 * (booleanCubeSign y.1 : ℂ) =
      canonicalMoebiusWeight (lowWheelFrozenSecondContactSourceScale y) *
        canonicalMoebiusWeight (canonicalCofactor y.2.1) := by
  have hyFrozen := (Finset.mem_filter.mp hy).1
  rcases lowWheelCanonicalRepeatedFrozenCofactor_source_data hyFrozen with
    ⟨_hk, _hpPrime, _hpNotC, hsq, _hcgt, _hcR⟩
  rcases lowWheelFrozenCofactorTopPrime_data hyFrozen with
    ⟨hqPrime, hqDvd, _hpq⟩
  have hstrip :
      canonicalMoebiusWeight (canonicalCofactor y.2.1) =
        -canonicalMoebiusWeight y.2.1 := by
    simpa [canonicalCofactor, lowWheelFrozenCofactorTopPrime] using
      (canonicalMoebiusWeight_div_prime hqPrime hsq hqDvd)
  calc
    canonicalMoebiusWeight y.2.1 * (booleanCubeSign y.1 : ℂ) =
        -(canonicalMoebiusWeight (lowWheelFrozenSecondContactSourceScale y) *
          canonicalMoebiusWeight y.2.1) :=
      lowWheelFrozenSecondContactSource_weight_eq_neg_scale_mul_cofactor hy
    _ = canonicalMoebiusWeight (lowWheelFrozenSecondContactSourceScale y) *
        canonicalMoebiusWeight (canonicalCofactor y.2.1) := by
      rw [hstrip]
      ring

/-- The source scale remembers its first root-crossing coordinate intrinsically:
its canonical largest prime is exactly the frozen pivot. -/
theorem lowWheelFrozenSecondContact_sourceScale_largestPrime
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R) :
    canonicalLargestPrimeFactor (lowWheelFrozenSecondContactSourceScale y) =
      lowWheelTaggedDowncrossPivot y := by
  have hyFrozen := (Finset.mem_filter.mp hy).1
  have hsource := lowWheelCanonicalRepeatedFrozenCofactor_source_data hyFrozen
  have hfrozen := (Finset.mem_filter.mp hyFrozen).1
  have hrepeated := (Finset.mem_filter.mp hfrozen).1
  have htagged := (Finset.mem_filter.mp hrepeated).1
  have ht := (mem_lowWheelCanonicalTaggedDowncrossCarrier.mp htagged).1
  have htPred :
      y.1 ∈ (primesUpTo (lowWheelTaggedDowncrossPivot y - 1)).powerset := by
    apply Finset.mem_powerset.mpr
    intro r hr
    have hrPrime := prime_of_mem_primesUpTo ((Finset.mem_powerset.mp ht) hr)
    have hrLt := lowWheelCanonicalRepeatedFrozenCofactor_facePrime_lt_pivot hyFrozen hr
    exact mem_primesUpTo.mpr ⟨hrPrime, by omega⟩
  have hmax := canonicalLargestPrimeFactor_insert_freshPrime hsource.2.1 htPred
  rw [lowWheelFrozenSecondContactSourceScale_eq_insertPivotFaceProduct hy]
  exact hmax

/-- Square-dilated daughter cutoff attached to one second-contact owner. -/
def lowWheelFrozenSecondContactFluxChildCutoff (B q : ℕ) : ℕ :=
  B / (q * q)

/-- A square-dilated daughter cutoff is always weakly below its parent scale. -/
theorem lowWheelFrozenSecondContactFluxChildCutoff_le
    {B q : ℕ} :
    lowWheelFrozenSecondContactFluxChildCutoff B q ≤ B := by
  unfold lowWheelFrozenSecondContactFluxChildCutoff
  exact Nat.div_le_self _ _

/-! ## Canonical ancestry congestion on the saturated #629 window

The original collision-defect-chain interface bounded the number of charged
steps pointwise.  That is too strong.  The canonical parent is unique, but many
higher sources can coalesce onto the same lower parent edge.  The scale carried
by a second-contact owner is nevertheless intrinsically `q^-2`, exactly the
weight used by `sum_primeOwner_squareDilatedCutoffs_le_parent` and by the
physical complete-period first-moment bound.

The declarations below therefore expose raw edge multiplicity for diagnostics
but make the weighted aggregate the arithmetic proof target.  No Mertens or RH
conclusion is asserted here.
-/

/-- Iterate the deterministic canonical ancestry parent.  `none` is absorbing. -/
noncomputable def canonicalAncestryParentIterate {B : ℕ} :
    ℕ → SourceIndex B → Option (SourceIndex B)
  | 0, s => some s
  | d + 1, s => (canonicalAncestryParentIterate d s).bind sourceParent

@[simp] theorem canonicalAncestryParentIterate_zero {B : ℕ}
    (s : SourceIndex B) :
    canonicalAncestryParentIterate 0 s = some s := rfl

/-- The saturated #629 owner window written directly on the canonical `(q,c)`
carrier.  It is the arithmetic form

`max R (X_R/q^2) < c <= X_R/q`, with `q<R` and `P+(c)<q` supplied by
`SourceAdmissible`. -/
noncomputable def lowWheelFrozenSecondContactCanonicalSeeds (R : ℕ) :
    Finset (SourceIndex (squareRootEndpoint R)) :=
  Finset.univ.filter fun s =>
    SourceAdmissible s ∧
      sourcePrime s < R ∧
      max R
          (squareRootEndpoint R /
            (sourcePrime s * sourcePrime s)) < sourceCore s ∧
      sourceCore s ≤ squareRootEndpoint R / sourcePrime s

/-- Literal membership criterion for the canonical saturated seed carrier. -/
theorem mem_lowWheelFrozenSecondContactCanonicalSeeds_iff
    {R : ℕ} {s : SourceIndex (squareRootEndpoint R)} :
    s ∈ lowWheelFrozenSecondContactCanonicalSeeds R ↔
      SourceAdmissible s ∧
        sourcePrime s < R ∧
        max R
            (squareRootEndpoint R /
              (sourcePrime s * sourcePrime s)) < sourceCore s ∧
        sourceCore s ≤ squareRootEndpoint R / sourcePrime s := by
  simp [lowWheelFrozenSecondContactCanonicalSeeds]

/-- Number of saturated seeds whose canonical trajectory visits one smooth child.
Because `sourceParent` is a function, the child uniquely determines the edge.
The depth range `B+1` is the certified nilpotence height of the bounded source
flow. -/
noncomputable def canonicalAncestryChargeMultiplicity {B : ℕ}
    (seeds : Finset (SourceIndex B)) (child : SourceIndex B) : ℕ :=
  ∑ d ∈ Finset.range (B + 1),
    (seeds.filter fun seed =>
      canonicalAncestryParentIterate d seed = some child).card

/-- Natural square-scale weight of a canonical edge with owner `q`. -/
def canonicalAncestryOwnerSquareWeight {B : ℕ}
    (child : SourceIndex B) : ℚ :=
  (1 : ℚ) / (sourcePrime child : ℚ) ^ 2

/-- Global ancestry congestion after applying the intrinsic `q^-2` owner scale.
Roots contribute zero because they do not carry a parent edge. -/
noncomputable def canonicalAncestryWeightedCongestion {B : ℕ}
    (seeds : Finset (SourceIndex B)) : ℚ :=
  ∑ child : SourceIndex B,
    if sourceParent child = none then 0
    else
      (canonicalAncestryChargeMultiplicity seeds child : ℚ) *
        canonicalAncestryOwnerSquareWeight child

/-- The weighted congestion specialized to the actual saturated second-contact
seed window. -/
noncomputable def lowWheelFrozenSecondContactCanonicalWeightedCongestion
    (R : ℕ) : ℚ :=
  canonicalAncestryWeightedCongestion
    (lowWheelFrozenSecondContactCanonicalSeeds R)

/-- Strong form suggested by the finite diagnostic.  This is deliberately a
named statement, not a theorem: proving it is the new arithmetic packing seam. -/
def LowWheelFrozenSecondContactCanonicalWeightedLinearBoundStatement : Prop :=
  ∃ C : ℚ, 0 ≤ C ∧ ∀ R : ℕ,
    lowWheelFrozenSecondContactCanonicalWeightedCongestion R ≤ C * (R : ℚ)

/-- RH-scale form allowing the polylogarithmic loss that the proof program can
afford.  Unlike the discarded maximum-multiplicity target, this controls the
aggregate only after the intrinsic `q^-2` scale weight has been applied. -/
def LowWheelFrozenSecondContactCanonicalWeightedPolylogBoundStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ, ∀ R : ℕ,
    ((lowWheelFrozenSecondContactCanonicalWeightedCongestion R : ℚ) : ℝ) ≤
      C * (R : ℝ) *
        (Real.log (((R + 2 : ℕ) : ℝ)) + 1) ^ k

end RHLean.Proof