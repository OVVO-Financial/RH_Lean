import Mathlib
import RHLean.Proof.SquareRootLowPrimeGoFullFaceResidualAbsorption

/-!
# Ledger-level absorption of the full-face Go defect

The previous module places every far full-face mate of an unfinished Go
second-boundary defect inside the old hard physical residual.  Here the same
geometry is upgraded to an exact signed ledger statement.

The incidence high product is collision-free: from `q*(r*d)` one recovers `q`
as the canonical largest prime, then `r` as the canonical largest prime of the
child, and finally `d`.  Since every defect source is physical, its high product
is strictly larger than `R`.  Therefore the near defect incidences inject into
the seven integers `R+1,...,R+7`.

Consequently the full defect mass is not a new quadratic error.  Its far part
cancels a literal subledger of the existing physical residual before any norm is
taken, and only a signed near remainder of absolute mass at most seven remains.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open CanonicalGapAncestryBridge

attribute [local instance] Classical.propDecidable

/-- Recover the canonical largest-prime/cofactor coordinates represented by
arbitrary source data, without assuming the integer core is smaller than the
prime. -/
theorem canonicalCoordinates_mul_of_sourceData_public
    {q c : ℕ} (hdata : CanonicalSourceData q c) :
    canonicalLargestPrimeFactor (c * q) = q ∧
      canonicalCofactor (c * q) = c := by
  have hqpos : 0 < q := hdata.1.pos
  have hqle : q ≤ c * q := by
    calc
      q = 1 * q := by simp
      _ ≤ c * q := Nat.mul_le_mul_right q hdata.2.1
  have hcle : c ≤ c * q := by
    calc
      c = c * 1 := by simp
      _ ≤ c * q := Nat.mul_le_mul_left c hqpos
  let s : SourceIndex (c * q) :=
    (⟨q, by omega⟩, ⟨c, by omega⟩)
  have hs : SourceAdmissible s := by
    change CanonicalSourceData q c
    exact hdata
  have hp := sourcePrime_eq_canonicalLargestPrimeFactor s hs
  have hc := sourceCore_eq_canonicalCofactor s hs
  have hp' : q = canonicalLargestPrimeFactor (q * c) := by
    simpa [s, sourcePrime, sourceProduct, sourceCore] using hp
  have hc' : c = canonicalCofactor (q * c) := by
    simpa [s, sourcePrime, sourceProduct, sourceCore] using hc
  constructor
  · simpa [Nat.mul_comm] using hp'.symm
  · simpa [Nat.mul_comm] using hc'.symm

/-- The physical high product of a defect source is its literal arithmetic
product `(r*d)*q`. -/
theorem squareRootLowPrimeGoFullFaceDefectSourceTag_highProduct
    {R r q d : ℕ}
    (hz : ((r, q), d) ∈ squareRootLowPrimeGoFullFaceDefectCarrier R) :
    lowWheelTaggedHighProduct
        (squareRootLowPrimeGoFullFaceDefectSourceTag ((r, q), d)) =
      (r * d) * q := by
  rcases mem_squareRootLowPrimeGoFullFaceDefectCarrier.mp hz with
    ⟨_hrR, _hqR, _hdR, hr, hq, hrq, _hcube, hd⟩
  have hfull :=
    (mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp hd).1
  have hsq : Squarefree (r * d) :=
    (squareRootLowPrimeGoFullBirthBoundary_child_canonicalSmooth
      hq hr hrq hfull).1.2.2
  unfold lowWheelTaggedHighProduct
    squareRootLowPrimeGoFullFaceDefectSourceTag
    squareRootLowPrimeGoSecondBoundaryFullFaceSource
  dsimp only
  rw [primeFaceProduct_squarefreePrimeFace hsq]

/-- Distinct live defect incidences have distinct physical high products. -/
theorem squareRootLowPrimeGoFullFaceDefect_highProduct_injOn
    (R : ℕ) :
    Set.InjOn
      (fun z : SquareRootLowPrimeGoFullFaceDefectIncidence =>
        lowWheelTaggedHighProduct
          (squareRootLowPrimeGoFullFaceDefectSourceTag z))
      (squareRootLowPrimeGoFullFaceDefectCarrier R) := by
  intro a ha b hb hab
  rcases a with ⟨⟨r, q⟩, d⟩
  rcases b with ⟨⟨s, t⟩, e⟩
  rcases mem_squareRootLowPrimeGoFullFaceDefectCarrier.mp ha with
    ⟨_hrR, _hqR, _hdR, hr, hq, hrq, _hcube, hd⟩
  rcases mem_squareRootLowPrimeGoFullFaceDefectCarrier.mp hb with
    ⟨_hsR, _htR, _heR, hs, ht, hst, _hcube', he⟩
  have hfullD :=
    (mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp hd).1
  have hfullE :=
    (mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp he).1
  have hdataD :=
    (squareRootLowPrimeGoFullBirthBoundary_child_canonicalSmooth
      hq hr hrq hfullD).1
  have hdataE :=
    (squareRootLowPrimeGoFullBirthBoundary_child_canonicalSmooth
      ht hs hst hfullE).1
  have hprod : (r * d) * q = (s * e) * t := by
    rw [← squareRootLowPrimeGoFullFaceDefectSourceTag_highProduct ha,
      ← squareRootLowPrimeGoFullFaceDefectSourceTag_highProduct hb]
    exact hab
  have hcoordD := canonicalCoordinates_mul_of_sourceData_public hdataD
  have hcoordE := canonicalCoordinates_mul_of_sourceData_public hdataE
  have hqt : q = t := by
    calc
      q = canonicalLargestPrimeFactor ((r * d) * q) := hcoordD.1.symm
      _ = canonicalLargestPrimeFactor ((s * e) * t) := congrArg _ hprod
      _ = t := hcoordE.1
  subst t
  have hchild : r * d = s * e :=
    Nat.eq_of_mul_eq_mul_right hq.pos hprod
  have htopD : canonicalLargestPrimeFactor (r * d) = r := by
    have hd1 := (mem_squareRootLowPrimeGoFullBirthBoundaryParents.mp hfullD).1
    have hrough :=
      (mem_squareRootLowPrimeGoFullBirthBoundaryParents.mp hfullD).2.2.2.1
    have h := canonicalLargestPrimeFactor_mul_prime_eq_of_rough
      (by omega : 0 < d) hr hrough
    simpa [Nat.mul_comm] using h
  have htopE : canonicalLargestPrimeFactor (s * e) = s := by
    have he1 := (mem_squareRootLowPrimeGoFullBirthBoundaryParents.mp hfullE).1
    have hrough :=
      (mem_squareRootLowPrimeGoFullBirthBoundaryParents.mp hfullE).2.2.2.1
    have h := canonicalLargestPrimeFactor_mul_prime_eq_of_rough
      (by omega : 0 < e) hs hrough
    simpa [Nat.mul_comm] using h
  have hrs : r = s := by
    calc
      r = canonicalLargestPrimeFactor (r * d) := htopD.symm
      _ = canonicalLargestPrimeFactor (s * e) := congrArg _ hchild
      _ = s := htopE
  subst s
  have hde : d = e := Nat.eq_of_mul_eq_mul_left hr.pos hchild
  subst e
  rfl

/-- Near live defect incidences, before the `R+8` far cutoff. -/
def squareRootLowPrimeGoFullFaceDefectNearCarrier
    (R : ℕ) : Finset SquareRootLowPrimeGoFullFaceDefectIncidence :=
  (squareRootLowPrimeGoFullFaceDefectCarrier R).filter fun z =>
    lowWheelTaggedHighProduct
      (squareRootLowPrimeGoFullFaceDefectSourceTag z) < R + 8

/-- Complementary far live defect incidences. -/
def squareRootLowPrimeGoFullFaceDefectFarCarrier
    (R : ℕ) : Finset SquareRootLowPrimeGoFullFaceDefectIncidence :=
  (squareRootLowPrimeGoFullFaceDefectCarrier R).filter fun z =>
    R + 8 ≤ lowWheelTaggedHighProduct
      (squareRootLowPrimeGoFullFaceDefectSourceTag z)

/-- Every live defect source high product lies strictly beyond the physical root. -/
theorem squareRootLowPrimeGoFullFaceDefectSource_highProduct_gt_root
    {R : ℕ} (hR : 2 ≤ R)
    {z : SquareRootLowPrimeGoFullFaceDefectIncidence}
    (hz : z ∈ squareRootLowPrimeGoFullFaceDefectCarrier R) :
    R < lowWheelTaggedHighProduct
      (squareRootLowPrimeGoFullFaceDefectSourceTag z) := by
  have hs := squareRootLowPrimeGoFullFaceDefectSourceTag_mem_transport hR hz
  have hphys := (mem_lowWheelFullTaggedPhysicalCarrier.mp hs).2
  have hpair := (mem_lowWheelCanonicalPhysicalStateSet.mp hphys).2.2.2
  exact hpair.2.2.1

/-- The near defect high products lie in the seven-site interval
`R+1,...,R+7`. -/
theorem squareRootLowPrimeGoFullFaceDefectNear_highProduct_mem_seven
    {R : ℕ} (hR : 2 ≤ R)
    {z : SquareRootLowPrimeGoFullFaceDefectIncidence}
    (hz : z ∈ squareRootLowPrimeGoFullFaceDefectNearCarrier R) :
    lowWheelTaggedHighProduct
        (squareRootLowPrimeGoFullFaceDefectSourceTag z) ∈
      Finset.Icc (R + 1) (R + 7) := by
  rcases Finset.mem_filter.mp hz with ⟨hzLive, hnear⟩
  have hroot := squareRootLowPrimeGoFullFaceDefectSource_highProduct_gt_root
    hR hzLive
  exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩

/-- **Seven-site near bound.**  The live defect incidence map is collision-free,
so at most seven incidences can remain below the far cutoff. -/
theorem squareRootLowPrimeGoFullFaceDefectNearCarrier_card_le_seven
    {R : ℕ} (hR : 2 ≤ R) :
    (squareRootLowPrimeGoFullFaceDefectNearCarrier R).card ≤ 7 := by
  let f : SquareRootLowPrimeGoFullFaceDefectIncidence → ℕ := fun z =>
    lowWheelTaggedHighProduct (squareRootLowPrimeGoFullFaceDefectSourceTag z)
  have hmaps : ∀ z ∈ squareRootLowPrimeGoFullFaceDefectNearCarrier R,
      f z ∈ Finset.Icc (R + 1) (R + 7) := by
    intro z hz
    exact squareRootLowPrimeGoFullFaceDefectNear_highProduct_mem_seven hR hz
  have hinj : Set.InjOn f
      (squareRootLowPrimeGoFullFaceDefectNearCarrier R) := by
    intro a ha b hb hab
    apply squareRootLowPrimeGoFullFaceDefect_highProduct_injOn R
      (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1
    exact hab
  have hcard := Finset.card_le_card_of_injOn f hmaps hinj
  have hseven : (Finset.Icc (R + 1) (R + 7)).card = 7 := by
    rw [Nat.card_Icc]
    omega
  rw [hseven] at hcard
  exact hcard

/-- Signed near defect source mass. -/
def squareRootLowPrimeGoFullFaceDefectNearSourceMass (R : ℕ) : ℤ :=
  ∑ z ∈ squareRootLowPrimeGoFullFaceDefectNearCarrier R,
    μ (z.1.2 * z.2)

/-- The complete near defect mass is uniformly bounded by seven. -/
theorem abs_squareRootLowPrimeGoFullFaceDefectNearSourceMass_le_seven
    {R : ℕ} (hR : 2 ≤ R) :
    |squareRootLowPrimeGoFullFaceDefectNearSourceMass R| ≤ 7 := by
  unfold squareRootLowPrimeGoFullFaceDefectNearSourceMass
  calc
    |∑ z ∈ squareRootLowPrimeGoFullFaceDefectNearCarrier R,
        μ (z.1.2 * z.2)| ≤
      ∑ z ∈ squareRootLowPrimeGoFullFaceDefectNearCarrier R,
        |μ (z.1.2 * z.2)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _z ∈ squareRootLowPrimeGoFullFaceDefectNearCarrier R, (1 : ℤ) := by
      apply Finset.sum_le_sum
      intro z _hz
      rcases ArithmeticFunction.moebius_eq_or (z.1.2 * z.2) with h | h | h <;>
        simp [h]
    _ = ((squareRootLowPrimeGoFullFaceDefectNearCarrier R).card : ℤ) := by simp
    _ ≤ 7 := by
      exact_mod_cast squareRootLowPrimeGoFullFaceDefectNearCarrier_card_le_seven hR

/-- Signed far defect source mass. -/
def squareRootLowPrimeGoFullFaceDefectFarSourceMass (R : ℕ) : ℤ :=
  ∑ z ∈ squareRootLowPrimeGoFullFaceDefectFarCarrier R,
    μ (z.1.2 * z.2)

/-- Exact near/far partition of the complete defect source mass. -/
theorem squareRootLowPrimeGoFullFaceDefectSourceMass_eq_near_add_far
    (R : ℕ) :
    squareRootLowPrimeGoFullFaceDefectSourceMass R =
      squareRootLowPrimeGoFullFaceDefectNearSourceMass R +
        squareRootLowPrimeGoFullFaceDefectFarSourceMass R := by
  unfold squareRootLowPrimeGoFullFaceDefectSourceMass
    squareRootLowPrimeGoFullFaceDefectNearSourceMass
    squareRootLowPrimeGoFullFaceDefectFarSourceMass
  rw [← Finset.sum_union]
  · apply Finset.sum_congr
    · ext z
      simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hz
        by_cases hfar : R + 8 ≤ lowWheelTaggedHighProduct
            (squareRootLowPrimeGoFullFaceDefectSourceTag z)
        · exact Or.inr ⟨hz, hfar⟩
        · exact Or.inl ⟨hz, by omega⟩
      · rintro (⟨hz, _⟩ | ⟨hz, _⟩) <;> exact hz
    · intro _z _hz
      rfl
  · rw [Finset.disjoint_left]
    intro z hzNear hzFar
    have hn := (Finset.mem_filter.mp hzNear).2
    have hf := (Finset.mem_filter.mp hzFar).2
    omega

/-- The far incidence mate image is exactly the previously defined far filter
of the global mate image. -/
theorem squareRootLowPrimeGoFullFaceDefectFarCarrier_mateImage_eq
    (R : ℕ) :
    (squareRootLowPrimeGoFullFaceDefectFarCarrier R).image
        (squareRootLowPrimeGoFullFaceDefectMateTag R) =
      squareRootLowPrimeGoFullFaceDefectMateFarImage R := by
  ext y
  constructor
  · intro hy
    rcases Finset.mem_image.mp hy with ⟨z, hz, rfl⟩
    rcases Finset.mem_filter.mp hz with ⟨hzLive, hfar⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨z, hzLive, rfl⟩, ?_⟩
    rw [lowWheelFullFaceQuotientMate_highProduct]
    exact hfar
  · intro hy
    rcases Finset.mem_filter.mp hy with ⟨hyImage, hfar⟩
    rcases Finset.mem_image.mp hyImage with ⟨z, hzLive, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨z, Finset.mem_filter.mpr ⟨hzLive, ?_⟩, rfl⟩
    rw [lowWheelFullFaceQuotientMate_highProduct] at hfar
    exact hfar

/-- Literal signed ledger of the far defect mate image. -/
def squareRootLowPrimeGoFullFaceDefectMateFarLedger (R : ℕ) : ℂ :=
  ∑ y ∈ squareRootLowPrimeGoFullFaceDefectMateFarImage R,
    lowWheelFullTaggedPhysicalWeight y

/-- The far source mass cancels its literal far mate image pointwise. -/
theorem squareRootLowPrimeGoFullFaceDefectFarSourceMass_add_mateFarLedger_eq_zero
    {R : ℕ} (hR : 2 ≤ R) :
    ((squareRootLowPrimeGoFullFaceDefectFarSourceMass R : ℤ) : ℂ) +
      squareRootLowPrimeGoFullFaceDefectMateFarLedger R = 0 := by
  unfold squareRootLowPrimeGoFullFaceDefectFarSourceMass
    squareRootLowPrimeGoFullFaceDefectMateFarLedger
  rw [← squareRootLowPrimeGoFullFaceDefectFarCarrier_mateImage_eq R]
  rw [Finset.sum_image]
  · push_cast
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro z hz
    rcases z with ⟨⟨r, q⟩, d⟩
    rcases Finset.mem_filter.mp hz with ⟨hzLive, _hfar⟩
    rcases mem_squareRootLowPrimeGoFullFaceDefectCarrier.mp hzLive with
      ⟨_hrR, _hqR, _hdR, hr, hq, hrq, hcube, hd⟩
    have hfull :=
      (mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp hd).1
    have hsource :=
      squareRootLowPrimeGoSecondBoundaryFullFaceSource_weight_eq
        hq hr hrq hfull
    have hcancel :=
      squareRootLowPrimeGoSecondBoundaryFullFaceSource_mate_cancel
        hR hq hr hrq hcube hd
    simpa [squareRootLowPrimeGoFullFaceDefectSourceTag,
      squareRootLowPrimeGoFullFaceDefectMateTag,
      canonicalMoebiusWeight] using hcancel
  · intro a ha b hb hab
    exact squareRootLowPrimeGoFullFaceDefectMateTag_injOn hR
      (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 hab

/-- Remove the already-cancelled far defect mates from the hard physical residual. -/
def lowWheelFrozenTopFarPhysicalResidualAfterGoDefects (R : ℕ) :
    Finset LowWheelFullTaggedPhysicalState :=
  lowWheelFrozenTopFarPhysicalResidualCarrier R \
    squareRootLowPrimeGoFullFaceDefectMateFarImage R

/-- Signed ledger after removing the far defect mate subcarrier. -/
def lowWheelFrozenTopFarPhysicalResidualAfterGoDefectsLedger (R : ℕ) : ℂ :=
  ∑ y ∈ lowWheelFrozenTopFarPhysicalResidualAfterGoDefects R,
    lowWheelFullTaggedPhysicalWeight y

/-- The old physical residual splits exactly into the far defect mate subledger
and the residual after deleting it. -/
theorem lowWheelFrozenTopFarPhysicalResidualLedger_eq_goMate_add_after
    {R : ℕ} (hR : 6 ≤ R) :
    lowWheelFrozenTopFarPhysicalResidualLedger R =
      squareRootLowPrimeGoFullFaceDefectMateFarLedger R +
        lowWheelFrozenTopFarPhysicalResidualAfterGoDefectsLedger R := by
  unfold lowWheelFrozenTopFarPhysicalResidualLedger
    squareRootLowPrimeGoFullFaceDefectMateFarLedger
    lowWheelFrozenTopFarPhysicalResidualAfterGoDefectsLedger
    lowWheelFrozenTopFarPhysicalResidualAfterGoDefects
  exact (Finset.sum_sdiff
    (squareRootLowPrimeGoFullFaceDefectMateFarImage_subset_physicalResidual hR)).symm

/-- **Ledger absorption theorem.**  Adding the complete unfinished Go defect
mass to the old hard physical residual removes its entire far population before
any norm and leaves only the seven-site near signed defect plus the residual
with those far mate states deleted. -/
theorem fullFaceDefectMass_add_physicalResidual_eq_near_add_after
    {R : ℕ} (hR : 6 ≤ R) :
    ((squareRootLowPrimeGoFullFaceDefectSourceMass R : ℤ) : ℂ) +
        lowWheelFrozenTopFarPhysicalResidualLedger R =
      ((squareRootLowPrimeGoFullFaceDefectNearSourceMass R : ℤ) : ℂ) +
        lowWheelFrozenTopFarPhysicalResidualAfterGoDefectsLedger R := by
  rw [squareRootLowPrimeGoFullFaceDefectSourceMass_eq_near_add_far,
    lowWheelFrozenTopFarPhysicalResidualLedger_eq_goMate_add_after hR]
  push_cast
  have hcancel :=
    squareRootLowPrimeGoFullFaceDefectFarSourceMass_add_mateFarLedger_eq_zero
      (R := R) (by omega)
  linear_combination hcancel

end RHLean.Proof
