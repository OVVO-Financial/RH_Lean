import Mathlib
import RHLean.Proof.LowWheelFrozenSecondContactScaleFlux

/-!
# Exact rough-prefix fibre of the existing physical transport

At a represented source scale `A`, the complete frozen cofactor fibre is the
nonunit squarefree `P+(A)`-rough prefix at `B = X_R / A`. Its second-contact
subfibre is cut out by `B < P+(c)*c`; the complementary square residual obeys
`P+(c)*c <= B` and hence lies below `B/2`.

The full prefix has an opposite-weight mate in the existing physical transport
carrier. We identify that actual subledger and retain an arbitrary test function
of the physical integer, so the cancellation preserves every integer fibre and
all multiplicities. The unit cofactor is excluded on both sides.
-/

noncomputable section

open scoped BigOperators ArithmeticFunction.Moebius

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Full frozen cofactor fibre, before imposing the second-contact wall. -/
def lowWheelFrozenCofactorSourceScaleFiber (R A : ℕ) :
    Finset LowWheelTaggedDowncrossState :=
  (lowWheelCanonicalRepeatedFrozenCofactorPart R).filter fun y =>
    lowWheelFrozenSecondContactSourceScale y = A

/-- Independent nonunit rough prefix. Squarefreeness removes only zero weights. -/
def lowWheelFrozenSourceRoughPrefix (p B : ℕ) : Finset ℕ :=
  (Finset.Icc 2 B).filter fun c => Squarefree c ∧ RoughAbove p c

/-- Complement of the second-contact shell in the full rough prefix. -/
def lowWheelFrozenSourceSquareResidual (p B : ℕ) : Finset ℕ :=
  (lowWheelFrozenSourceRoughPrefix p B).filter fun c =>
    canonicalLargestPrimeFactor c * c ≤ B

/-- Literal product-one subcarrier of the already-defined physical transport. -/
def lowWheelFrozenSourceScaleTransportCarrier (R A : ℕ) :
    Finset LowWheelTaggedCofactorQuotientState :=
  (lowWheelFrozenCofactorSourceScaleFiber R A).image
    lowWheelCanonicalRepeatedFrozenProductOneMate

private theorem frozenSource_scale_eq_insert
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    lowWheelFrozenSecondContactSourceScale y =
      primeFaceProduct (insert (lowWheelTaggedDowncrossPivot y) y.1) := by
  have hpNot : lowWheelTaggedDowncrossPivot y ∉ y.1 := by
    intro hp
    exact (Nat.lt_irrefl _)
      (lowWheelCanonicalRepeatedFrozenCofactor_facePrime_lt_pivot hy hp)
  simp [lowWheelFrozenSecondContactSourceScale, primeFaceProduct, hpNot]

private theorem frozenSource_scale_largestPrime
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    canonicalLargestPrimeFactor (lowWheelFrozenSecondContactSourceScale y) =
      lowWheelTaggedDowncrossPivot y := by
  have hs := lowWheelCanonicalRepeatedFrozenCofactor_source_data hy
  have ho := orderedEulerCutShape_of_mem_carrier
    (lowWheelCanonicalRepeatedFrozenCofactor_mem_orderedEulerCutCarrier hy)
  have ht : y.1 ∈ (primesUpTo (lowWheelTaggedDowncrossPivot y - 1)).powerset := by
    apply Finset.mem_powerset.mpr
    intro r hr
    have hp := (ho.2.2.2.2.1 r hr).1
    have hlt := lowWheelCanonicalRepeatedFrozenCofactor_facePrime_lt_pivot hy hr
    exact mem_primesUpTo.mpr ⟨hp, by omega⟩
  rw [frozenSource_scale_eq_insert hy]
  exact canonicalLargestPrimeFactor_insert_freshPrime hs.2.1 ht

private theorem frozenSource_productOne_eq_scale_mul_cofactor
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    primeFaceProduct (lowWheelCanonicalRepeatedFrozenProductOneFace y) =
      lowWheelFrozenSecondContactSourceScale y * y.2.1 := by
  rw [lowWheelCanonicalRepeatedFrozenProductOneFace_product hy]
  unfold lowWheelFrozenSecondContactSourceScale
  ring

private theorem frozenSource_child_eq_scale_mul_cofactor
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    orderedEulerCutChildInteger y =
      lowWheelFrozenSecondContactSourceScale y * y.2.1 := by
  rw [lowWheelFrozenSecondContact_child_eq_owner_mul_parentProduct hy,
    lowWheelFrozenSecondContact_owner_mul_parentFaceProduct hy]
  exact frozenSource_productOne_eq_scale_mul_cofactor hy

private theorem frozenSource_weight_eq
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    lowWheelTaggedDowncrossWeight y =
      -(canonicalMoebiusWeight (lowWheelFrozenSecondContactSourceScale y) *
        canonicalMoebiusWeight y.2.1) := by
  have hs := lowWheelCanonicalRepeatedFrozenCofactor_source_data hy
  have ho := orderedEulerCutShape_of_mem_carrier
    (lowWheelCanonicalRepeatedFrozenCofactor_mem_orderedEulerCutCarrier hy)
  have hpNot : lowWheelTaggedDowncrossPivot y ∉ y.1 := by
    intro hp
    exact (Nat.lt_irrefl _)
      (lowWheelCanonicalRepeatedFrozenCofactor_facePrime_lt_pivot hy hp)
  have hprime : ∀ r ∈ insert (lowWheelTaggedDowncrossPivot y) y.1, r.Prime := by
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact hs.2.1
    · exact (ho.2.2.2.2.1 r hr).1
  have hmu : μ (lowWheelFrozenSecondContactSourceScale y) =
      -booleanCubeSign y.1 := by
    rw [frozenSource_scale_eq_insert hy,
      moebius_primeFaceProduct_eq_booleanCubeSign _ hprime]
    simp [booleanCubeSign, Finset.card_insert_of_notMem hpNot, pow_succ]
  simp only [lowWheelTaggedDowncrossWeight, canonicalMoebiusWeight, hmu,
    Int.cast_neg]
  ring

/-- A represented source scale is above the old root. -/
theorem lowWheelFrozenSourceScale_root_lt
    {R A : ℕ} (hA : A ∈ lowWheelFrozenSecondContactSourceScaleSet R) :
    R < A := by
  rcases Finset.mem_image.mp hA with ⟨y, hy, hyA⟩
  have h := lowWheelCanonicalRepeatedFrozenCofactor_facePivot_crosses_root
    (Finset.mem_filter.mp hy).1
  change R < lowWheelFrozenSecondContactSourceScale y at h
  simpa [hyA] using h

/-- Its reciprocal cutoff is strictly below the old root. -/
theorem lowWheelFrozenSourceScale_cutoff_lt_root
    {R A : ℕ} (hA : A ∈ lowWheelFrozenSecondContactSourceScaleSet R) :
    squareRootEndpoint R / A < R := by
  rcases Finset.mem_image.mp hA with ⟨y, hy, hyA⟩
  have h := (lowWheelFrozenSecondContact_source_lowerScaleExit hy).2.2
  change squareRootEndpoint R / lowWheelFrozenSecondContactSourceScale y < R at h
  simpa [hyA] using h

/-- The actual full source fibre exhausts the independently defined rough
prefix. The reverse direction reconstructs an ordered physical cut. -/
theorem lowWheelFrozenCofactorSourceScaleFiber_image_eq_roughPrefix
    {R A : ℕ} (hA : A ∈ lowWheelFrozenSecondContactSourceScaleSet R) :
    (lowWheelFrozenCofactorSourceScaleFiber R A).image (fun y => y.2.1) =
      lowWheelFrozenSourceRoughPrefix (canonicalLargestPrimeFactor A)
        (squareRootEndpoint R / A) := by
  have hApos : 0 < A := (Nat.zero_le R).trans_lt (lowWheelFrozenSourceScale_root_lt hA)
  have hBR := lowWheelFrozenSourceScale_cutoff_lt_root hA
  ext c
  constructor
  · rintro hc
    rcases Finset.mem_image.mp hc with ⟨y, hyF, rfl⟩
    rcases Finset.mem_filter.mp hyF with ⟨hy, hyA⟩
    have hs := lowWheelCanonicalRepeatedFrozenCofactor_source_data hy
    have hp : canonicalLargestPrimeFactor A = lowWheelTaggedDowncrossPivot y := by
      rw [← hyA]
      exact frozenSource_scale_largestPrime hy
    have hrough : RoughAbove (canonicalLargestPrimeFactor A) y.2.1 := by
      intro q hq
      rw [hp]
      exact lowWheelCanonicalRepeatedFrozenCofactor_pivot_lt_primeFactor hy hq
    have hprod := lowWheelFrozenProductOneFace_le_endpoint hy
    rw [frozenSource_productOne_eq_scale_mul_cofactor hy, hyA] at hprod
    have hcB : y.2.1 ≤ squareRootEndpoint R / A := by
      apply (Nat.le_div_iff_mul_le hApos).2
      simpa [Nat.mul_comm] using hprod
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hcB⟩,
      hs.2.2.2.1, hrough⟩
  · intro hc
    rcases Finset.mem_filter.mp hc with ⟨hcI, hcsq, hcrough⟩
    rcases Finset.mem_Icc.mp hcI with ⟨hc2, hcB⟩
    rcases Finset.mem_image.mp hA with ⟨y, hySecond, hyA⟩
    have hy := (Finset.mem_filter.mp hySecond).1
    have hs := lowWheelCanonicalRepeatedFrozenCofactor_source_data hy
    have ho := orderedEulerCutShape_of_mem_carrier
      (lowWheelCanonicalRepeatedFrozenCofactor_mem_orderedEulerCutCarrier hy)
    let p := lowWheelTaggedDowncrossPivot y
    let z : LowWheelTaggedDowncrossState := (y.1, (c, p))
    have hp : canonicalLargestPrimeFactor A = p := by
      rw [← hyA]
      exact frozenSource_scale_largestPrime hy
    have hrough : RoughAbove p c := by simpa [hp] using hcrough
    have hcOne : 1 ≤ c :=
      (show 1 ≤ 2 by norm_num).trans hc2
    have hzShape : OrderedEulerCutShape z := by
      refine ⟨hs.2.1, hcOne, hcsq,
        RoughAbove.not_dvd hs.2.1 hcOne hrough, ?_, hrough⟩
      intro q hq
      exact ⟨(ho.2.2.2.2.1 q hq).1,
        lowWheelCanonicalRepeatedFrozenCofactor_facePrime_lt_pivot hy hq⟩
    have hpivot : lowWheelTaggedDowncrossPivot z = p :=
      orderedEulerCutShape_canonicalPivot hzShape
    have hzA : lowWheelFrozenSecondContactSourceScale z = A := by
      change lowWheelTaggedDowncrossPivot z * primeFaceProduct y.1 = A
      rw [hpivot]
      exact hyA
    have hzChild : orderedEulerCutChildInteger z ≤ squareRootEndpoint R := by
      change c * (p * primeFaceProduct y.1) ≤ squareRootEndpoint R
      have hbase : p * primeFaceProduct y.1 = A := hyA
      rw [hbase]
      exact (Nat.le_div_iff_mul_le hApos).1 hcB
    have hzSqrt := (orderedEulerCutChild_le_endpoint_iff hzShape).1 hzChild
    have hzBirth : orderedEulerCutBirthRoot z ≤ R := by
      change max (primeFaceProduct y.1)
        (max (c + 1) (Nat.sqrt (orderedEulerCutChildInteger z) + 1)) ≤ R
      exact max_le
        (lowWheelCanonicalRepeatedFrozenCofactor_faceProduct_le_root hy)
        (max_le (by omega) (by omega))
    have hzDeath : R < orderedEulerCutDeathRoot z := by
      change R < p * primeFaceProduct y.1
      exact lowWheelCanonicalRepeatedFrozenCofactor_facePivot_crosses_root hy
    have hzOrdered : z ∈ orderedEulerCutCarrier R :=
      mem_orderedEulerCutCarrier_iff_shape_lifetime.mpr
        ⟨hzShape, hzBirth, hzDeath⟩
    have hzFrozen := orderedEulerCut_mem_frozenCofactor_of_one_lt hzOrdered
      (by change 1 < c; omega)
    exact Finset.mem_image.mpr ⟨z, Finset.mem_filter.mpr ⟨hzFrozen, hzA⟩, rfl⟩

/-- Saturation at fixed `A`, including the exact strict second-contact wall. -/
theorem lowWheelFrozenSecondContactSourceScaleCofactors_eq_roughPrefix_filter
    {R A : ℕ} (hA : A ∈ lowWheelFrozenSecondContactSourceScaleSet R) :
    lowWheelFrozenSecondContactSourceScaleCofactors R A =
      (lowWheelFrozenSourceRoughPrefix (canonicalLargestPrimeFactor A)
        (squareRootEndpoint R / A)).filter fun c =>
          squareRootEndpoint R / A < canonicalLargestPrimeFactor c * c := by
  have hApos : 0 < A := (Nat.zero_le R).trans_lt (lowWheelFrozenSourceScale_root_lt hA)
  ext c
  constructor
  · intro hc
    rcases Finset.mem_image.mp hc with ⟨y, hyF, rfl⟩
    rcases mem_lowWheelFrozenSecondContactSourceScaleFiber.mp hyF with ⟨hy, hyA⟩
    have hfull : y.2.1 ∈ (lowWheelFrozenCofactorSourceScaleFiber R A).image
        (fun z => z.2.1) :=
      Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hy).1, hyA⟩, rfl⟩
    rw [lowWheelFrozenCofactorSourceScaleFiber_image_eq_roughPrefix hA] at hfull
    have hwall := (lowWheelFrozenSecondContact_source_lowerScaleExit hy).2.1
    change squareRootEndpoint R / lowWheelFrozenSecondContactSourceScale y <
      canonicalLargestPrimeFactor y.2.1 * y.2.1 at hwall
    rw [hyA] at hwall
    exact Finset.mem_filter.mpr ⟨hfull, hwall⟩
  · intro hc
    rcases Finset.mem_filter.mp hc with ⟨hfull, hwall⟩
    rw [← lowWheelFrozenCofactorSourceScaleFiber_image_eq_roughPrefix hA] at hfull
    rcases Finset.mem_image.mp hfull with ⟨y, hyF, rfl⟩
    rcases Finset.mem_filter.mp hyF with ⟨hy, hyA⟩
    have hwallX := (Nat.div_lt_iff_lt_mul hApos).1 hwall
    have hySecond : y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R := by
      apply Finset.mem_filter.mpr
      refine ⟨hy, ?_⟩
      change squareRootEndpoint R < canonicalLargestPrimeFactor y.2.1 *
        primeFaceProduct (lowWheelCanonicalRepeatedFrozenProductOneFace y)
      rw [frozenSource_productOne_eq_scale_mul_cofactor hy, hyA]
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hwallX
    exact Finset.mem_image.mpr ⟨y,
      mem_lowWheelFrozenSecondContactSourceScaleFiber.mpr ⟨hySecond, hyA⟩, rfl⟩

/-- The full prefix is exactly the second-contact fibre plus the square
residual, with all signs or other cofactor weights preserved. -/
theorem lowWheelFrozenSourceRoughPrefix_sum_eq_secondContact_add_residual
    {R A : ℕ} (hA : A ∈ lowWheelFrozenSecondContactSourceScaleSet R)
    (g : ℕ → ℂ) :
    (∑ c ∈ lowWheelFrozenSourceRoughPrefix (canonicalLargestPrimeFactor A)
        (squareRootEndpoint R / A), g c) =
      (∑ c ∈ lowWheelFrozenSecondContactSourceScaleCofactors R A, g c) +
        ∑ c ∈ lowWheelFrozenSourceSquareResidual (canonicalLargestPrimeFactor A)
          (squareRootEndpoint R / A), g c := by
  rw [lowWheelFrozenSecondContactSourceScaleCofactors_eq_roughPrefix_filter hA]
  symm
  simpa only [lowWheelFrozenSourceSquareResidual, Nat.not_lt] using
    (Finset.sum_filter_add_sum_filter_not
      (lowWheelFrozenSourceRoughPrefix (canonicalLargestPrimeFactor A)
        (squareRootEndpoint R / A))
      (fun c => squareRootEndpoint R / A < canonicalLargestPrimeFactor c * c) g)

/-- The complementary square residual has genuine half-scale support. -/
theorem lowWheelFrozenSourceSquareResidual_subset_halfScale (p B : ℕ) :
    lowWheelFrozenSourceSquareResidual p B ⊆ Finset.Icc 1 (B / 2) := by
  intro c hc
  rcases Finset.mem_filter.mp hc with ⟨hcFull, hcontact⟩
  have hcI := (Finset.mem_filter.mp hcFull).1
  have hc2 := (Finset.mem_Icc.mp hcI).1
  have hq2 := (canonicalLargestPrimeFactor_prime (by omega : 1 < c)).two_le
  have htwo : 2 * c ≤ B := (Nat.mul_le_mul_right c hq2).trans hcontact
  exact Finset.mem_Icc.mpr ⟨by omega,
    (Nat.le_div_iff_mul_le (by norm_num : 0 < (2 : ℕ))).2
      (by simpa [Nat.mul_comm] using htwo)⟩

end RHLean.Proof