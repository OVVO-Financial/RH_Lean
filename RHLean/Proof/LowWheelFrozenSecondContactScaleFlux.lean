import Mathlib
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

end RHLean.Proof