import Mathlib
import RHLean.Proof.SquareRootLowPrimeGoFullFacePartner
import RHLean.Proof.LowWheelFrozenFirstFailureBridge

/-!
# Absorb the full-face Go defect mate into the existing physical residual

PR #641 embeds every unfinished two-boundary Go defect into the literal full
physical carrier and pairs it with the existing full-face/quotient Othello
mate.  The remaining bookkeeping question is where those mate occurrences sit
inside the earlier frozen/top/far normal form.

This file proves that the far part of the complete Go-defect mate image is
already a subcarrier of the literal hard physical residual.  The key geometric
fact is that a defect mate has a face prime strictly *above* its canonical
pivot.  A frozen top image has every face prime strictly below its unchanged
pivot, so the populations are disjoint.  The defect mate quotient is also at
least two, making it disjoint from the internal-terminal mate image, whose
cofactor/quotient state is exactly `(1,1)`.

Thus the far Go-defect correction is not an additional scalar error term.  It is
already present, with opposite sign, inside the old physical residual and can be
cancelled there before any norm is taken.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open FrozenCofactorTopBottom
open CanonicalGapAncestryBridge

attribute [local instance] Classical.propDecidable

/-- Every face prime of a frozen-top image lies strictly below its unchanged
canonical pivot. -/
theorem lowWheelFrozenCofactorTopImage_facePrime_lt_pivot
    {R : ℕ} {z : LowWheelTaggedDowncrossState}
    (hz : z ∈ lowWheelFrozenCofactorTopImage R)
    {a : ℕ} (ha : a ∈ z.1) :
    a < lowWheelCanonicalCofactorQuotientPivot z.2 := by
  rcases mem_lowWheelFrozenCofactorTopImage.mp hz with ⟨y, hy, rfl⟩
  change a ∈ y.1 at ha
  rw [lowWheelFrozenCofactorTopToggle_pivot]
  exact lowWheelCanonicalRepeatedFrozenCofactor_facePrime_lt_pivot hy ha

/-- On a live Go defect source, the least active full-face prime is strictly
below the interior owner `r` and lies on the Boolean face rather than in the
outer quotient. -/
theorem squareRootLowPrimeGoFullFaceDefect_oppositePrime_lt_interior
    {R r q d : ℕ} (hR : 2 ≤ R)
    (hz : ((r, q), d) ∈ squareRootLowPrimeGoFullFaceDefectCarrier R) :
    let s := squareRootLowPrimeGoFullFaceDefectSourceTag ((r, q), d)
    let p := lowWheelFullOppositePrime R s
    (lowWheelFullActivePrimeSet R s).Nonempty ∧
      p.Prime ∧ p < r ∧ p ∈ s.1 := by
  rcases mem_squareRootLowPrimeGoFullFaceDefectCarrier.mp hz with
    ⟨_hrR, hqR, _hdR, hr, hq, hrq, hcube, hd⟩
  let s := squareRootLowPrimeGoFullFaceDefectSourceTag ((r, q), d)
  let p := lowWheelFullOppositePrime R s
  have hfull :=
    (mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp hd).1
  have hdgt : 1 < d :=
    squareRootLowPrimeGoFullBirthBoundary_parent_one_lt hr hrq hfull
  obtain ⟨a, haPrime, haDvd⟩ := Nat.exists_prime_and_dvd (by omega : d ≠ 1)
  have hrough :=
    (mem_squareRootLowPrimeGoFullBirthBoundaryParents.mp hfull).2.2.2.1
  have haLe : a ≤ canonicalLargestPrimeFactor d :=
    prime_dvd_le_canonicalLargestPrimeFactor hdgt haPrime haDvd
  have har : a < r := haLe.trans_lt hrough
  have hdPos : 0 < d := by omega
  have hrdNe : r * d ≠ 0 :=
    Nat.mul_ne_zero hr.ne_zero (Nat.ne_of_gt hdPos)
  have haFace : a ∈ s.1 := by
    have haProd : a ∣ r * d := dvd_mul_of_dvd_right haDvd r
    have haFactors : a ∈ (r * d).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨haPrime, haProd, hrdNe⟩
    simpa [s, squareRootLowPrimeGoFullFaceDefectSourceTag,
      squareRootLowPrimeGoSecondBoundaryFullFaceSource,
      squarefreePrimeFace] using haFactors
  have haGlobal : a ∈ primesUpTo R :=
    mem_primesUpTo.mpr ⟨haPrime, by omega⟩
  have haActive : a ∈ lowWheelFullActivePrimeSet R s :=
    mem_lowWheelFullActivePrimeSet.mpr ⟨haGlobal, Or.inl haFace⟩
  have hnonempty : (lowWheelFullActivePrimeSet R s).Nonempty := ⟨a, haActive⟩
  have hpLeA : p ≤ a := by
    dsimp only [p]
    unfold lowWheelFullOppositePrime
    rw [dif_pos hnonempty]
    exact Finset.min'_le _ _ haActive
  have hpr : p < r := hpLeA.trans_lt har
  have hpData := lowWheelFullOppositePrime_data hnonempty
  have hpPrime : p.Prime := prime_of_mem_primesUpTo hpData.1
  have hpNotDvdQ : ¬ p ∣ q := by
    intro hpq
    have hpEqQ := (Nat.prime_dvd_prime_iff_eq hpPrime hq).mp hpq
    omega
  have hpFace : p ∈ s.1 := by
    have hactive : p ∈ s.1 ∨ p ∣ s.2.2 := hpData.2
    have hsQuot : s.2.2 = q := by
      rfl
    rw [hsQuot] at hactive
    exact hactive.resolve_right hpNotDvdQ
  exact ⟨hnonempty, hpPrime, hpr, hpFace⟩

/-- A complete Go-defect mate retains the interior owner `r` on its face while
its canonical pivot is strictly smaller.  This is the orientation opposite to
a frozen-top image. -/
theorem squareRootLowPrimeGoFullFaceDefectMateTag_exists_facePrime_gt_pivot
    {R r q d : ℕ} (hR : 2 ≤ R)
    (hz : ((r, q), d) ∈ squareRootLowPrimeGoFullFaceDefectCarrier R) :
    ∃ a ∈ (squareRootLowPrimeGoFullFaceDefectMateTag R ((r, q), d)).1,
      lowWheelCanonicalCofactorQuotientPivot
          (squareRootLowPrimeGoFullFaceDefectMateTag R ((r, q), d)).2 < a := by
  rcases mem_squareRootLowPrimeGoFullFaceDefectCarrier.mp hz with
    ⟨_hrR, _hqR, _hdR, hr, hq, hrq, _hcube, hd⟩
  let s := squareRootLowPrimeGoFullFaceDefectSourceTag ((r, q), d)
  let p := lowWheelFullOppositePrime R s
  have hpData :=
    squareRootLowPrimeGoFullFaceDefect_oppositePrime_lt_interior hR hz
  dsimp only at hpData
  rcases hpData with ⟨hnonempty, hpPrime, hpr, hpFace⟩
  have hfull :=
    (mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp hd).1
  have hd1 := (mem_squareRootLowPrimeGoFullBirthBoundaryParents.mp hfull).1
  have hdPos : 0 < d := by omega
  have hrDvd : r ∣ r * d := dvd_mul_right r d
  have hrdNe : r * d ≠ 0 :=
    Nat.mul_ne_zero hr.ne_zero (Nat.ne_of_gt hdPos)
  have hrFace : r ∈ s.1 := by
    have hrFactors : r ∈ (r * d).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hr, hrDvd, hrdNe⟩
    simpa [s, squareRootLowPrimeGoFullFaceDefectSourceTag,
      squareRootLowPrimeGoSecondBoundaryFullFaceSource,
      squarefreePrimeFace] using hrFactors
  have hprNe : p ≠ r := ne_of_lt hpr
  have hrMate :
      r ∈ (squareRootLowPrimeGoFullFaceDefectMateTag R ((r, q), d)).1 := by
    change r ∈ (lowWheelFullFaceQuotientMate R s).1
    unfold lowWheelFullFaceQuotientMate
    rw [dif_pos hnonempty]
    unfold lowWheelFullFaceQuotientToggleAt
    dsimp only
    simp [lowWheelFaceTailToggleAt, hpFace, hrFace, hprNe]
  have hpDvdMate :
      p ∣ (squareRootLowPrimeGoFullFaceDefectMateTag R ((r, q), d)).2.1 *
        (squareRootLowPrimeGoFullFaceDefectMateTag R ((r, q), d)).2.2 := by
    change p ∣ (lowWheelFullFaceQuotientMate R s).2.1 *
      (lowWheelFullFaceQuotientMate R s).2.2
    unfold lowWheelFullFaceQuotientMate
    rw [dif_pos hnonempty]
    unfold lowWheelFullFaceQuotientToggleAt
    dsimp only
    simp [lowWheelFaceTailToggleAt, hpFace]
  have hpivotLe :
      lowWheelCanonicalCofactorQuotientPivot
          (squareRootLowPrimeGoFullFaceDefectMateTag R ((r, q), d)).2 ≤ p := by
    unfold lowWheelCanonicalCofactorQuotientPivot
    exact Nat.minFac_le_of_dvd hpPrime.two_le hpDvdMate
  exact ⟨r, hrMate, hpivotLe.trans_lt hpr⟩

/-- A Go-defect mate has nontrivial quotient.  Hence it cannot coincide with an
internal-terminal mate image, whose complete state is `(1,1)`. -/
theorem squareRootLowPrimeGoFullFaceDefectMateTag_quotient_two_le
    {R r q d : ℕ} (hR : 2 ≤ R)
    (hz : ((r, q), d) ∈ squareRootLowPrimeGoFullFaceDefectCarrier R) :
    2 ≤ (squareRootLowPrimeGoFullFaceDefectMateTag R ((r, q), d)).2.2 := by
  rcases mem_squareRootLowPrimeGoFullFaceDefectCarrier.mp hz with
    ⟨_hrR, _hqR, _hdR, _hr, hq, _hrq, _hcube, _hd⟩
  let s := squareRootLowPrimeGoFullFaceDefectSourceTag ((r, q), d)
  let p := lowWheelFullOppositePrime R s
  have hpData :=
    squareRootLowPrimeGoFullFaceDefect_oppositePrime_lt_interior hR hz
  dsimp only at hpData
  rcases hpData with ⟨hnonempty, hpPrime, _hpr, hpFace⟩
  have hquot :
      (squareRootLowPrimeGoFullFaceDefectMateTag R ((r, q), d)).2.2 = p * q := by
    change (lowWheelFullFaceQuotientMate R s).2.2 = p * q
    unfold lowWheelFullFaceQuotientMate
    rw [dif_pos hnonempty]
    unfold lowWheelFullFaceQuotientToggleAt
    dsimp only
    simp [lowWheelFaceTailToggleAt, hpFace, s,
      squareRootLowPrimeGoFullFaceDefectSourceTag,
      squareRootLowPrimeGoSecondBoundaryFullFaceSource]
  rw [hquot]
  exact hpPrime.two_le.trans (Nat.le_mul_of_pos_right p hq.pos)

/-- The complete Go-defect mate image is disjoint from the old frozen-top image.
The former has a face prime above its pivot; the latter has all face primes
below its pivot. -/
theorem squareRootLowPrimeGoFullFaceDefectMateImage_disjoint_topImage
    {R : ℕ} (hR : 2 ≤ R) :
    Disjoint (squareRootLowPrimeGoFullFaceDefectMateImage R)
      (lowWheelFrozenCofactorTopImage R) := by
  rw [Finset.disjoint_left]
  intro z hzMate hzTop
  rcases Finset.mem_image.mp hzMate with ⟨i, hi, rfl⟩
  rcases i with ⟨⟨r, q⟩, d⟩
  obtain ⟨a, haFace, hpivotLt⟩ :=
    squareRootLowPrimeGoFullFaceDefectMateTag_exists_facePrime_gt_pivot hR hi
  have haTop := lowWheelFrozenCofactorTopImage_facePrime_lt_pivot hzTop haFace
  omega

/-- The complete Go-defect mate image is also disjoint from the internal-terminal
mate image. -/
theorem squareRootLowPrimeGoFullFaceDefectMateImage_disjoint_internalMate
    {R : ℕ} (hR : 2 ≤ R) :
    Disjoint (squareRootLowPrimeGoFullFaceDefectMateImage R)
      (lowWheelCanonicalRepeatedTerminalInternalMateImage R) := by
  rw [Finset.disjoint_left]
  intro z hzMate hzInternal
  rcases Finset.mem_image.mp hzMate with ⟨i, hi, rfl⟩
  rcases i with ⟨⟨r, q⟩, d⟩
  have htwo := squareRootLowPrimeGoFullFaceDefectMateTag_quotient_two_le hR hi
  have hone := lowWheelCanonicalRepeatedTerminalInternalMateImage_state_eq_one hzInternal
  have hquot :
      (squareRootLowPrimeGoFullFaceDefectMateTag R ((r, q), d)).2.2 = 1 :=
    congrArg Prod.snd hone
  omega

/-- Far part of the Go-defect mate image. -/
def squareRootLowPrimeGoFullFaceDefectMateFarImage (R : ℕ) :
    Finset LowWheelFullTaggedPhysicalState :=
  (squareRootLowPrimeGoFullFaceDefectMateImage R).filter fun z =>
    R + 8 ≤ lowWheelTaggedHighProduct z

/-- Every far Go-defect mate is a literal far physical occurrence. -/
theorem squareRootLowPrimeGoFullFaceDefectMateFarImage_subset_farPhysical
    {R : ℕ} (hR : 2 ≤ R) :
    squareRootLowPrimeGoFullFaceDefectMateFarImage R ⊆
      lowWheelFarTaggedPhysicalCarrier R := by
  intro z hz
  rcases Finset.mem_filter.mp hz with ⟨hzImage, hfar⟩
  exact mem_lowWheelFarTaggedPhysicalCarrier.mpr
    ⟨squareRootLowPrimeGoFullFaceDefectMateImage_subset_transport hR hzImage,
      hfar⟩

/-- The far defect-mate image is disjoint from both image populations that were
already removed when the old hard physical residual was formed. -/
theorem squareRootLowPrimeGoFullFaceDefectMateFarImage_disjoint_owned
    {R : ℕ} (hR : 2 ≤ R) :
    Disjoint (squareRootLowPrimeGoFullFaceDefectMateFarImage R)
      (lowWheelFrozenTopFarOwnedImage R) := by
  rw [Finset.disjoint_left]
  intro z hzFar hzOwned
  have hzImage := (Finset.mem_filter.mp hzFar).1
  rcases Finset.mem_union.mp hzOwned with hzInternal | hzTop
  · have hdisj :=
      Finset.disjoint_left.mp
        (squareRootLowPrimeGoFullFaceDefectMateImage_disjoint_internalMate hR)
    exact hdisj hzImage (Finset.mem_filter.mp hzInternal).1
  · have hdisj :=
      Finset.disjoint_left.mp
        (squareRootLowPrimeGoFullFaceDefectMateImage_disjoint_topImage hR)
    exact hdisj hzImage hzTop

/-- **Residual absorption.**  Every far unfinished Go second-boundary defect mate
already lies in the literal hard physical residual carrier.  Hence its signed
cancellation partner must be removed there before any norm/frame estimate is
applied. -/
theorem squareRootLowPrimeGoFullFaceDefectMateFarImage_subset_physicalResidual
    {R : ℕ} (hR : 6 ≤ R) :
    squareRootLowPrimeGoFullFaceDefectMateFarImage R ⊆
      lowWheelFrozenTopFarPhysicalResidualCarrier R := by
  intro z hz
  apply Finset.mem_sdiff.mpr
  refine ⟨squareRootLowPrimeGoFullFaceDefectMateFarImage_subset_farPhysical
      (by omega) hz, ?_⟩
  intro hzOwned
  exact (Finset.disjoint_left.mp
    (squareRootLowPrimeGoFullFaceDefectMateFarImage_disjoint_owned
      (R := R) (by omega))) hz hzOwned

/-! ## Ledger-level absorption and seven-site near remainder -/

/-- Recover native canonical coordinates from arbitrary source data without any
integer orientation assumption on the cofactor. -/
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

/-- The high product of a defect source is its literal arithmetic product. -/
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

/-- Distinct live defect incidences have distinct high products. -/
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

/-- Every live defect source high product lies strictly beyond the root. -/
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

/-- Near high products lie in the seven integers `R+1,...,R+7`. -/
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

/-- At most seven unfinished incidences survive below the far cutoff. -/
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

/-- The near defect mass is uniformly bounded by seven. -/
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

/-- The far incidence mate image is exactly the earlier far mate filter. -/
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

/-- The far source mass cancels the literal far mate image pointwise. -/
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
    simpa [squareRootLowPrimeGoFullFaceDefectSourceTag,
      squareRootLowPrimeGoFullFaceDefectMateTag,
      canonicalMoebiusWeight] using
      squareRootLowPrimeGoSecondBoundaryFullFaceSource_mate_cancel
        hR hq hr hrq hcube hd
  · intro a ha b hb hab
    exact squareRootLowPrimeGoFullFaceDefectMateTag_injOn hR
      (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 hab

/-- Remove the already-cancelled far defect mates from the hard residual. -/
def lowWheelFrozenTopFarPhysicalResidualAfterGoDefects (R : ℕ) :
    Finset LowWheelFullTaggedPhysicalState :=
  lowWheelFrozenTopFarPhysicalResidualCarrier R \
    squareRootLowPrimeGoFullFaceDefectMateFarImage R

/-- Signed ledger after removing those far defect mate occurrences. -/
def lowWheelFrozenTopFarPhysicalResidualAfterGoDefectsLedger (R : ℕ) : ℂ :=
  ∑ y ∈ lowWheelFrozenTopFarPhysicalResidualAfterGoDefects R,
    lowWheelFullTaggedPhysicalWeight y

/-- The old residual splits into the far defect mate subledger and its complement. -/
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

/-- **Ledger absorption theorem.**  The complete unfinished Go defect is
absorbed into the existing physical residual before any norm; only a uniformly
seven-site signed remainder survives. -/
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
