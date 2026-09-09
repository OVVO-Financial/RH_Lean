import Mathlib
import RHLean.Proof.LowWheelCanonicalRepeatedFrozenFactorGeometry
import RHLean.Proof.SquareRootLowPrimeGoCrossingMateLedger
import RHLean.Proof.LowWheelSurvivorFloorExpansion
import RHLean.Arithmetic.PrimeFaceProductUniqueness

/-!
# Global reassembly of the frozen whole-cofactor product-one mate

`LowWheelCanonicalRepeatedFrozenFactorGeometry` constructs, for every frozen
nontrivial-cofactor source `y=(t,(c,p))`, the physical opposite-sign mate

`(insert p (t ∪ squarefreePrimeFace c), (1,1))`.

This file proves that the map loses no multiplicity.  The final face remembers
the pivot as its unique first root crossing: all old face primes are below the
pivot, all cofactor primes are above it, `P(t) <= R`, and `R < p*P(t)`.
If two sources with pivots `p<q` had the same final face, then
`insert p t_p ⊆ t_q`, forcing

`R < p*P(t_p) <= P(t_q) <= R`,

a contradiction.  Equal pivots then recover the lower face and upper cofactor
prime face by filtering the final face below and above the pivot.

Consequently the complete frozen `c>1` ledger cancels exactly against a literal
product-one subledger of the already-existing physical transport carrier.
No norm, root-factorization hypothesis, or asymptotic estimate appears.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- The frozen old face is still below the root. -/
theorem lowWheelCanonicalRepeatedFrozenCofactor_faceProduct_le_root
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    primeFaceProduct y.1 ≤ R := by
  have hfrozen := (Finset.mem_filter.mp hy).1
  have hrepeated := (Finset.mem_filter.mp hfrozen).1
  have htagged := (Finset.mem_filter.mp hrepeated).1
  have htag := mem_lowWheelCanonicalTaggedDowncrossCarrier.mp htagged
  have hshell := lowWheelCanonicalDowncrossPart_adjacent_shell htag.2
  rcases hshell with ⟨_hpPrime, _hpNotC, _hpDvdK, hdown, _hup⟩
  have hdata := lowWheelCanonicalRepeatedFrozenCofactor_source_data hy
  have hpPos : 0 < lowWheelTaggedDowncrossPivot y := hdata.2.1.pos
  change primeFaceProduct y.1 *
      (y.2.2 / lowWheelTaggedDowncrossPivot y) ≤ R at hdown
  rw [hdata.1, Nat.div_self hpPos, Nat.mul_one] at hdown
  exact hdown

/-- Adjoining the frozen pivot to the old face crosses the root. -/
theorem lowWheelCanonicalRepeatedFrozenCofactor_facePivot_crosses_root
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    R < lowWheelTaggedDowncrossPivot y * primeFaceProduct y.1 := by
  have hfrozen := (Finset.mem_filter.mp hy).1
  have hrepeated := (Finset.mem_filter.mp hfrozen).1
  have htagged := (Finset.mem_filter.mp hrepeated).1
  have htag := mem_lowWheelCanonicalTaggedDowncrossCarrier.mp htagged
  have hshell := lowWheelCanonicalDowncrossPart_adjacent_shell htag.2
  rcases hshell with ⟨hpRaw, _hpNotC, _hpDvdK, _hdown, hup⟩
  have hp : (lowWheelTaggedDowncrossPivot y).Prime := by
    simpa [lowWheelTaggedDowncrossPivot] using hpRaw
  have hdata := lowWheelCanonicalRepeatedFrozenCofactor_source_data hy
  change R < primeFaceProduct y.1 *
      (lowWheelTaggedDowncrossPivot y *
        (y.2.2 / lowWheelTaggedDowncrossPivot y)) at hup
  rw [hdata.1, Nat.div_self hp.pos, Nat.mul_one] at hup
  simpa [Nat.mul_comm] using hup

/-- The original Boolean face can be recovered from the product-one face by
keeping precisely the primes below the frozen pivot. -/
theorem lowWheelCanonicalRepeatedFrozenProductOneFace_filter_lt_pivot
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    (lowWheelCanonicalRepeatedFrozenProductOneFace y).filter
        (fun q => q < lowWheelTaggedDowncrossPivot y) = y.1 := by
  ext q
  constructor
  · intro hq
    rcases Finset.mem_filter.mp hq with ⟨hqFace, hqLt⟩
    unfold lowWheelCanonicalRepeatedFrozenProductOneFace at hqFace
    rcases Finset.mem_insert.mp hqFace with hqp | hqu
    · subst q
      omega
    · rcases Finset.mem_union.mp hqu with hqt | hqc
      · exact hqt
      · have hgt := lowWheelCanonicalRepeatedFrozenCofactor_pivot_lt_primeFactor hy
          (by simpa [squarefreePrimeFace] using hqc)
        omega
  · intro hqt
    apply Finset.mem_filter.mpr
    refine ⟨?_, lowWheelCanonicalRepeatedFrozenCofactor_facePrime_lt_pivot hy hqt⟩
    unfold lowWheelCanonicalRepeatedFrozenProductOneFace
    exact Finset.mem_insert.mpr <| Or.inr <|
      Finset.mem_union.mpr <| Or.inl hqt

/-- Dually, the cofactor prime face is recovered by keeping precisely the
primes above the frozen pivot. -/
theorem lowWheelCanonicalRepeatedFrozenProductOneFace_filter_pivot_lt
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    (lowWheelCanonicalRepeatedFrozenProductOneFace y).filter
        (fun q => lowWheelTaggedDowncrossPivot y < q) =
      squarefreePrimeFace y.2.1 := by
  ext q
  constructor
  · intro hq
    rcases Finset.mem_filter.mp hq with ⟨hqFace, hpq⟩
    unfold lowWheelCanonicalRepeatedFrozenProductOneFace at hqFace
    rcases Finset.mem_insert.mp hqFace with hqp | hqu
    · subst q
      omega
    · rcases Finset.mem_union.mp hqu with hqt | hqc
      · have hlt := lowWheelCanonicalRepeatedFrozenCofactor_facePrime_lt_pivot hy hqt
        omega
      · exact hqc
  · intro hqc
    apply Finset.mem_filter.mpr
    refine ⟨?_, ?_⟩
    · unfold lowWheelCanonicalRepeatedFrozenProductOneFace
      exact Finset.mem_insert.mpr <| Or.inr <|
        Finset.mem_union.mpr <| Or.inr hqc
    · exact lowWheelCanonicalRepeatedFrozenCofactor_pivot_lt_primeFactor hy
        (by simpa [squarefreePrimeFace] using hqc)

private theorem lowWheelCanonicalRepeatedFrozenCofactor_face_mem_powerset
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    y.1 ∈ (primesUpTo R).powerset := by
  have hfrozen := (Finset.mem_filter.mp hy).1
  have hrepeated := (Finset.mem_filter.mp hfrozen).1
  have htagged := (Finset.mem_filter.mp hrepeated).1
  exact (mem_lowWheelCanonicalTaggedDowncrossCarrier.mp htagged).1

/-- **No multiplicity loss.**  The product-one face recovers the complete
frozen source. -/
theorem lowWheelCanonicalRepeatedFrozenProductOneMate_injOn
    (R : ℕ) :
    Set.InjOn lowWheelCanonicalRepeatedFrozenProductOneMate
      (lowWheelCanonicalRepeatedFrozenCofactorPart R) := by
  intro y hy z hz hmate
  have hfaceEq :
      lowWheelCanonicalRepeatedFrozenProductOneFace y =
        lowWheelCanonicalRepeatedFrozenProductOneFace z :=
    congrArg Prod.fst hmate
  have hpEq :
      lowWheelTaggedDowncrossPivot y = lowWheelTaggedDowncrossPivot z := by
    rcases lt_trichotomy (lowWheelTaggedDowncrossPivot y)
        (lowWheelTaggedDowncrossPivot z) with hpz | hpz | hzp
    · exfalso
      have hsub : insert (lowWheelTaggedDowncrossPivot y) y.1 ⊆ z.1 := by
        intro r hr
        have hrLtY : r ≤ lowWheelTaggedDowncrossPivot y := by
          rcases Finset.mem_insert.mp hr with hrp | hry
          · subst r
            exact le_rfl
          · exact (lowWheelCanonicalRepeatedFrozenCofactor_facePrime_lt_pivot hy hry).le
        have hrFinalY :
            r ∈ lowWheelCanonicalRepeatedFrozenProductOneFace y := by
          unfold lowWheelCanonicalRepeatedFrozenProductOneFace
          rcases Finset.mem_insert.mp hr with hrp | hry
          · exact Finset.mem_insert.mpr (Or.inl hrp)
          · exact Finset.mem_insert.mpr <| Or.inr <|
              Finset.mem_union.mpr <| Or.inl hry
        have hrFinalZ :
            r ∈ lowWheelCanonicalRepeatedFrozenProductOneFace z := by
          rw [← hfaceEq]
          exact hrFinalY
        have hrLtZ : r < lowWheelTaggedDowncrossPivot z :=
          lt_of_le_of_lt hrLtY hpz
        have hrFilter :
            r ∈ (lowWheelCanonicalRepeatedFrozenProductOneFace z).filter
              (fun q => q < lowWheelTaggedDowncrossPivot z) :=
          Finset.mem_filter.mpr ⟨hrFinalZ, hrLtZ⟩
        rw [lowWheelCanonicalRepeatedFrozenProductOneFace_filter_lt_pivot hz]
          at hrFilter
        exact hrFilter
      have hpNotY : lowWheelTaggedDowncrossPivot y ∉ y.1 := by
        intro hpMem
        have hlt := lowWheelCanonicalRepeatedFrozenCofactor_facePrime_lt_pivot hy hpMem
        omega
      have hprodInsert :
          primeFaceProduct (insert (lowWheelTaggedDowncrossPivot y) y.1) =
            lowWheelTaggedDowncrossPivot y * primeFaceProduct y.1 := by
        simp [primeFaceProduct, hpNotY]
      have hdiv :
          primeFaceProduct (insert (lowWheelTaggedDowncrossPivot y) y.1) ∣
            primeFaceProduct z.1 := by
        unfold primeFaceProduct
        exact Finset.prod_dvd_prod_of_subset _ _ id hsub
      have hzPos : 0 < primeFaceProduct z.1 :=
        primeFaceProduct_pos_of_mem_powerset
          (lowWheelCanonicalRepeatedFrozenCofactor_face_mem_powerset hz)
      have hle := Nat.le_of_dvd hzPos hdiv
      have hcross := lowWheelCanonicalRepeatedFrozenCofactor_facePivot_crosses_root hy
      have hzLow := lowWheelCanonicalRepeatedFrozenCofactor_faceProduct_le_root hz
      rw [hprodInsert] at hle
      omega
    · exact hpz
    · exfalso
      have hsub : insert (lowWheelTaggedDowncrossPivot z) z.1 ⊆ y.1 := by
        intro r hr
        have hrLtZ : r ≤ lowWheelTaggedDowncrossPivot z := by
          rcases Finset.mem_insert.mp hr with hrp | hrz
          · subst r
            exact le_rfl
          · exact (lowWheelCanonicalRepeatedFrozenCofactor_facePrime_lt_pivot hz hrz).le
        have hrFinalZ :
            r ∈ lowWheelCanonicalRepeatedFrozenProductOneFace z := by
          unfold lowWheelCanonicalRepeatedFrozenProductOneFace
          rcases Finset.mem_insert.mp hr with hrp | hrz
          · exact Finset.mem_insert.mpr (Or.inl hrp)
          · exact Finset.mem_insert.mpr <| Or.inr <|
              Finset.mem_union.mpr <| Or.inl hrz
        have hrFinalY :
            r ∈ lowWheelCanonicalRepeatedFrozenProductOneFace y := by
          rw [hfaceEq]
          exact hrFinalZ
        have hrLtY : r < lowWheelTaggedDowncrossPivot y :=
          lt_of_le_of_lt hrLtZ hzp
        have hrFilter :
            r ∈ (lowWheelCanonicalRepeatedFrozenProductOneFace y).filter
              (fun q => q < lowWheelTaggedDowncrossPivot y) :=
          Finset.mem_filter.mpr ⟨hrFinalY, hrLtY⟩
        rw [lowWheelCanonicalRepeatedFrozenProductOneFace_filter_lt_pivot hy]
          at hrFilter
        exact hrFilter
      have hpNotZ : lowWheelTaggedDowncrossPivot z ∉ z.1 := by
        intro hpMem
        have hlt := lowWheelCanonicalRepeatedFrozenCofactor_facePrime_lt_pivot hz hpMem
        omega
      have hprodInsert :
          primeFaceProduct (insert (lowWheelTaggedDowncrossPivot z) z.1) =
            lowWheelTaggedDowncrossPivot z * primeFaceProduct z.1 := by
        simp [primeFaceProduct, hpNotZ]
      have hdiv :
          primeFaceProduct (insert (lowWheelTaggedDowncrossPivot z) z.1) ∣
            primeFaceProduct y.1 := by
        unfold primeFaceProduct
        exact Finset.prod_dvd_prod_of_subset _ _ id hsub
      have hyPos : 0 < primeFaceProduct y.1 :=
        primeFaceProduct_pos_of_mem_powerset
          (lowWheelCanonicalRepeatedFrozenCofactor_face_mem_powerset hy)
      have hle := Nat.le_of_dvd hyPos hdiv
      have hcross := lowWheelCanonicalRepeatedFrozenCofactor_facePivot_crosses_root hz
      have hyLow := lowWheelCanonicalRepeatedFrozenCofactor_faceProduct_le_root hy
      rw [hprodInsert] at hle
      omega
  have hface : y.1 = z.1 := by
    calc
      y.1 = (lowWheelCanonicalRepeatedFrozenProductOneFace y).filter
          (fun q => q < lowWheelTaggedDowncrossPivot y) :=
        (lowWheelCanonicalRepeatedFrozenProductOneFace_filter_lt_pivot hy).symm
      _ = (lowWheelCanonicalRepeatedFrozenProductOneFace z).filter
          (fun q => q < lowWheelTaggedDowncrossPivot z) := by
        rw [hfaceEq, hpEq]
      _ = z.1 := lowWheelCanonicalRepeatedFrozenProductOneFace_filter_lt_pivot hz
  have hcofactorFace :
      squarefreePrimeFace y.2.1 = squarefreePrimeFace z.2.1 := by
    calc
      squarefreePrimeFace y.2.1 =
          (lowWheelCanonicalRepeatedFrozenProductOneFace y).filter
            (fun q => lowWheelTaggedDowncrossPivot y < q) :=
        (lowWheelCanonicalRepeatedFrozenProductOneFace_filter_pivot_lt hy).symm
      _ = (lowWheelCanonicalRepeatedFrozenProductOneFace z).filter
          (fun q => lowWheelTaggedDowncrossPivot z < q) := by
        rw [hfaceEq, hpEq]
      _ = squarefreePrimeFace z.2.1 :=
        lowWheelCanonicalRepeatedFrozenProductOneFace_filter_pivot_lt hz
  have hyData := lowWheelCanonicalRepeatedFrozenCofactor_source_data hy
  have hzData := lowWheelCanonicalRepeatedFrozenCofactor_source_data hz
  have hc : y.2.1 = z.2.1 := by
    calc
      y.2.1 = primeFaceProduct (squarefreePrimeFace y.2.1) :=
        (primeFaceProduct_squarefreePrimeFace hyData.2.2.2.1).symm
      _ = primeFaceProduct (squarefreePrimeFace z.2.1) := by rw [hcofactorFace]
      _ = z.2.1 := primeFaceProduct_squarefreePrimeFace hzData.2.2.2.1
  have hk : y.2.2 = z.2.2 := by
    calc
      y.2.2 = lowWheelTaggedDowncrossPivot y := hyData.1
      _ = lowWheelTaggedDowncrossPivot z := hpEq
      _ = z.2.2 := hzData.1.symm
  exact Prod.ext hface (Prod.ext hc hk)

/-- Literal image of the frozen product-one mates. -/
def lowWheelCanonicalRepeatedFrozenProductOneMateImage (R : ℕ) :
    Finset LowWheelTaggedCofactorQuotientState :=
  (lowWheelCanonicalRepeatedFrozenCofactorPart R).image
    lowWheelCanonicalRepeatedFrozenProductOneMate

/-- Every mate image occurrence is already in the global tagged physical
transport carrier. -/
theorem lowWheelCanonicalRepeatedFrozenProductOneMateImage_subset_transport
    (R : ℕ) :
    lowWheelCanonicalRepeatedFrozenProductOneMateImage R ⊆
      lowWheelCanonicalTaggedPhysicalCarrier R := by
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
  apply mem_lowWheelCanonicalTaggedPhysicalCarrier.mpr
  exact ⟨lowWheelCanonicalRepeatedFrozenProductOneFace_mem_powerset hy,
    lowWheelCanonicalRepeatedFrozenProductOneMate_mem_physical hy⟩

/-- Signed product-one mate ledger. -/
def lowWheelCanonicalRepeatedFrozenProductOneMateLedger (R : ℕ) : ℂ :=
  ∑ y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R,
    lowWheelTaggedCanonicalWeight
      (lowWheelCanonicalRepeatedFrozenProductOneMate y)

/-- Source and one-shot product-one mate have opposite tagged weights. -/
theorem lowWheelCanonicalRepeatedFrozenProductOneMate_taggedWeight_neg
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    lowWheelTaggedCanonicalWeight
        (lowWheelCanonicalRepeatedFrozenProductOneMate y) =
      -lowWheelTaggedDowncrossWeight y := by
  simpa [lowWheelTaggedCanonicalWeight,
    lowWheelTaggedDowncrossWeight,
    lowWheelCanonicalRepeatedFrozenProductOneMate] using
      lowWheelCanonicalRepeatedFrozenProductOneMate_weight_neg hy

/-- Injectivity turns the source-indexed mate ledger into the literal image
subledger. -/
theorem lowWheelCanonicalRepeatedFrozenProductOneMateLedger_eq_imageSum
    (R : ℕ) :
    lowWheelCanonicalRepeatedFrozenProductOneMateLedger R =
      ∑ z ∈ lowWheelCanonicalRepeatedFrozenProductOneMateImage R,
        lowWheelTaggedCanonicalWeight z := by
  unfold lowWheelCanonicalRepeatedFrozenProductOneMateLedger
    lowWheelCanonicalRepeatedFrozenProductOneMateImage
  rw [Finset.sum_image]
  intro a ha b hb hab
  exact lowWheelCanonicalRepeatedFrozenProductOneMate_injOn R ha hb hab

/-- **Exact global whole-cofactor cancellation.**  The complete frozen `c>1`
source ledger cancels against its already-physical product-one mate image before
any norm is taken. -/
theorem sum_lowWheelCanonicalRepeatedFrozenCofactor_add_productOneMate_eq_zero
    (R : ℕ) :
    (∑ y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R,
        lowWheelTaggedDowncrossWeight y) +
      lowWheelCanonicalRepeatedFrozenProductOneMateLedger R = 0 := by
  unfold lowWheelCanonicalRepeatedFrozenProductOneMateLedger
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro y hy
  rw [lowWheelCanonicalRepeatedFrozenProductOneMate_taggedWeight_neg hy]
  ring

end RHLean.Proof
