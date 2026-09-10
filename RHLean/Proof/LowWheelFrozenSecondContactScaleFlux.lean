import Mathlib
import RHLean.Analysis.SquareRootBornSmoothReciprocalForm
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

/-! ## Exact reciprocal-coordinate / Go-daughter intertwining

The unified reciprocal form uses `roughCofactorMobiusPrefixMass q B`.  The Go
wall was developed independently as a frozen predecessor-cube residual.  At the
square-dilated cutoff these are not merely analogous: they are exactly the same
Möbius population.  This is the missing coordinate splice between the
reciprocal transform and the `q^2` daughter carrier.
-/

/-- **Exact q² daughter identification.**  The complex cast of the literal Go
square residual is the rough lower-scale Möbius prefix at the identical
`X/q²` cutoff used by the unified reciprocal transform.  Nonsquarefree
cofactors may be omitted on the Go side because their Möbius weight is zero. -/
theorem squareRootLowPrimeGoWallSquareResidual_cast_eq_roughCofactorMobiusPrefixMass
    {q X : ℕ} (hq : q.Prime) :
    (((squareRootLowPrimeGoWallSquareResidual q X : ℤ) : ℂ)) =
      roughCofactorMobiusPrefixMass q (X / (q * q)) := by
  rw [squareRootLowPrimeGoWallSquareResidual_eq_smoothCofactorSum hq]
  push_cast
  unfold squareRootLowPrimeGoSmoothCofactors
    roughCofactorMobiusPrefixMass
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro c hc
  by_cases hrough : canonicalLargestPrimeFactor c < q
  · rw [if_pos hrough]
    by_cases hsq : Squarefree c
    · simp [hsq, hrough, canonicalMoebiusWeight]
    · have hmu : μ c = 0 :=
        ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
      simp [hsq, hrough, canonicalMoebiusWeight, hmu]
  · simp [hrough, canonicalMoebiusWeight]

/-- **One-strip reciprocal/Go intertwining.**  After casting the exact Go strip
to the common complex carrier, its only non-boundary term is literally the
rough Möbius daughter at `X/q²`.  Hence consecutive strips telescope their two
moving boundary states while all surviving arithmetic content is already on
the lower-scale coordinate used by the reciprocal transform. -/
theorem squareRootLowPrimeGoWallStripMass_cast_eq_boundaryDiff_add_roughDaughter
    {ell q X : ℕ} (hq : q.Prime)
    (hpred : primesUpTo (q - 1) = primesUpTo ell) :
    (((squareRootLowPrimeGoWallStripMass ell q X : ℤ) : ℂ)) =
      (((squareRootLowPrimeGoWallBoundaryState q X : ℤ) : ℂ)) -
        (((squareRootLowPrimeGoWallBoundaryState ell X : ℤ) : ℂ)) +
          roughCofactorMobiusPrefixMass q (X / (q * q)) := by
  rw [squareRootLowPrimeGoWallStripMass_eq_boundaryDiff_add_squareResidual
    hq hpred]
  push_cast
  rw [squareRootLowPrimeGoWallSquareResidual_cast_eq_roughCofactorMobiusPrefixMass hq]

/-! ## The #629 collision fibre becomes bounded after q^-2 scaling

`lowWheelFrozenSecondContactChildOwnerColumn_eq_signed_fibers` shows that the
raw coefficient of a reassembled face is the cardinality of
`lowWheelFrozenSecondContactOldOwnerFiber`.  All old owners in that fibre have
the same sign, so the cardinality itself cannot be cancelled locally.

The q-square descent changes the correct coefficient.  Retaining the intrinsic
owner weight `q^-2` turns the same fibre into a sub-sum of the already compiled
prime-owner reciprocal-square budget.  Consequently every collision fibre has
weighted mass at most one, regardless of its raw cardinality.
-/

/-- Reciprocal-square mass of the exact old-owner collision fibre from #629. -/
def lowWheelFrozenSecondContactOldOwnerReciprocalSquareMass
    (R r d : ℕ) : ℚ :=
  ∑ q ∈ lowWheelFrozenSecondContactOldOwnerFiber R r d,
    (1 : ℚ) / (q : ℚ) ^ 2

/-- Every old-owner collision fibre is literally a subfamily of the ambient
prime-owner schedule. -/
theorem lowWheelFrozenSecondContactOldOwnerFiber_subset_primesUpTo
    (R r d : ℕ) :
    lowWheelFrozenSecondContactOldOwnerFiber R r d ⊆ primesUpTo (R - 1) := by
  intro q hq
  exact (Finset.mem_filter.mp hq).1

/-- The reciprocal-square mass of one collision fibre is no larger than the
complete prime-owner reciprocal-square budget. -/
theorem lowWheelFrozenSecondContactOldOwnerReciprocalSquareMass_le_budget
    (R r d : ℕ) :
    lowWheelFrozenSecondContactOldOwnerReciprocalSquareMass R r d ≤
      primeOwnerReciprocalSquareBudget (R - 1) := by
  unfold lowWheelFrozenSecondContactOldOwnerReciprocalSquareMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (lowWheelFrozenSecondContactOldOwnerFiber_subset_primesUpTo R r d)
  intro q _hq hnot
  positivity

/-- **Weighted collision-fibre contraction.**  Arbitrarily large raw old-owner
multiplicity costs at most unit mass after the natural `q^-2` scale is retained.
This is finite and elementary; no prime density estimate is used. -/
theorem lowWheelFrozenSecondContactOldOwnerReciprocalSquareMass_le_one
    (R r d : ℕ) :
    lowWheelFrozenSecondContactOldOwnerReciprocalSquareMass R r d ≤ 1 := by
  exact (lowWheelFrozenSecondContactOldOwnerReciprocalSquareMass_le_budget R r d).trans
    (primeOwnerReciprocalSquareBudget_le_one (R - 1))

/-- The same fact in the literal daughter-cutoff units used by the q-square
renormalization: restricting to any one collision fibre cannot exceed one
parent-scale budget. -/
theorem sum_oldOwnerFiber_squareDilatedCutoffs_le_parent
    (R r d X : ℕ) :
    (∑ q ∈ lowWheelFrozenSecondContactOldOwnerFiber R r d,
      ((X / (q * q) : ℕ) : ℚ)) ≤ (X : ℚ) := by
  calc
    (∑ q ∈ lowWheelFrozenSecondContactOldOwnerFiber R r d,
        ((X / (q * q) : ℕ) : ℚ)) ≤
      ∑ q ∈ primesUpTo (R - 1), ((X / (q * q) : ℕ) : ℚ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (lowWheelFrozenSecondContactOldOwnerFiber_subset_primesUpTo R r d)
        intro q _hq hnot
        positivity
    _ ≤ (X : ℚ) := sum_primeOwner_squareDilatedCutoffs_le_parent (R - 1) X

/-- **Collision-safe subcriticality.**  Even if arbitrarily many old owners
coalesce onto one #629 reassembled face, retaining their `q^-2` daughter scales
before applying the exact prime-11 weight-one energy factor leaves a strict
contraction for every positive parent scale. -/
theorem elevenWeighted_sum_oldOwnerFiber_squareDilatedCutoffs_lt_parent
    (R r d X : ℕ) (hX : 0 < X) :
    elevenWeightOneEnergyFactor *
        (∑ q ∈ lowWheelFrozenSecondContactOldOwnerFiber R r d,
          ((X / (q * q) : ℕ) : ℚ)) <
      (X : ℚ) := by
  have hsum := sum_oldOwnerFiber_squareDilatedCutoffs_le_parent R r d X
  have hXq : (0 : ℚ) < (X : ℚ) := by exact_mod_cast hX
  calc
    elevenWeightOneEnergyFactor *
          (∑ q ∈ lowWheelFrozenSecondContactOldOwnerFiber R r d,
            ((X / (q * q) : ℕ) : ℚ)) ≤
        elevenWeightOneEnergyFactor * (X : ℚ) :=
      mul_le_mul_of_nonneg_left hsum elevenWeightOneEnergyFactor_nonneg
    _ < 1 * (X : ℚ) :=
      mul_lt_mul_of_pos_right
        (elevenWeightOneEnergyFactor_lt_three_quarters.trans (by norm_num)) hXq
    _ = (X : ℚ) := by ring

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
