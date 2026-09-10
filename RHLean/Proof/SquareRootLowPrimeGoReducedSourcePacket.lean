import Mathlib
import RHLean.Proof.SquareRootLowPrimeGoFullFaceResidualAbsorption

/-!
# The live Go source packet that survives full-face mate deletion

PR #643 removes the already-physical Othello mate of every unfinished Go
second-boundary defect before any residual norm is taken.  This file records the
complementary carrier fact: the corresponding full-face source occurrence is
itself a far physical state, but it is neither one of the old owned images nor a
defect mate.  Hence exactly one source copy survives on the reduced carrier.

This distinction matters for the quantitative frame problem.  The source packet
may not be silently discarded with its mate, and it may not be charged as a
second independent daughter packet.  The final identities below split the
#643 reduced ledger exactly into this one surviving source packet plus its
literal set-theoretic complement.  No norm or estimate is taken.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open FrozenCofactorTopBottom
open CanonicalGapAncestryBridge

attribute [local instance] Classical.propDecidable

/-- Literal image of the full-face Go defect sources. -/
def squareRootLowPrimeGoFullFaceDefectSourceImage (R : ℕ) :
    Finset LowWheelFullTaggedPhysicalState :=
  (squareRootLowPrimeGoFullFaceDefectCarrier R).image
    squareRootLowPrimeGoFullFaceDefectSourceTag

/-- The source image is injective, so its indexed ledger is literally the sum
on this physical subcarrier. -/
theorem squareRootLowPrimeGoFullFaceDefectSourceLedger_eq_imageSum
    (R : ℕ) :
    squareRootLowPrimeGoFullFaceDefectSourceLedger R =
      ∑ z ∈ squareRootLowPrimeGoFullFaceDefectSourceImage R,
        lowWheelFullTaggedPhysicalWeight z := by
  unfold squareRootLowPrimeGoFullFaceDefectSourceLedger
    squareRootLowPrimeGoFullFaceDefectSourceImage
  rw [Finset.sum_image]
  intro a ha b hb hab
  exact squareRootLowPrimeGoFullFaceDefectSourceTag_injOn R ha hb hab

/-- The source and its full-face mate have the same represented high product,
so the already-proved far estimate for the mate is also a far estimate for the
source. -/
theorem squareRootLowPrimeGoFullFaceDefectSourceTag_far
    {R r q d : ℕ} (hR : 6 ≤ R)
    (hz : ((r, q), d) ∈ squareRootLowPrimeGoFullFaceDefectCarrier R) :
    R + 8 ≤ lowWheelTaggedHighProduct
      (squareRootLowPrimeGoFullFaceDefectSourceTag ((r, q), d)) := by
  have h := squareRootLowPrimeGoFullFaceDefectMateTag_far hR hz
  unfold squareRootLowPrimeGoFullFaceDefectMateTag at h
  rw [lowWheelFullFaceQuotientMate_highProduct] at h
  exact h

/-- Every source occurrence is therefore a literal far physical occurrence. -/
theorem squareRootLowPrimeGoFullFaceDefectSourceImage_subset_farPhysical
    {R : ℕ} (hR : 6 ≤ R) :
    squareRootLowPrimeGoFullFaceDefectSourceImage R ⊆
      lowWheelFarTaggedPhysicalCarrier R := by
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨⟨⟨r, q⟩, d⟩, hd, rfl⟩
  apply mem_lowWheelFarTaggedPhysicalCarrier.mpr
  exact ⟨squareRootLowPrimeGoFullFaceDefectSourceTag_mem_transport
      (by omega : 2 ≤ R) hd,
    squareRootLowPrimeGoFullFaceDefectSourceTag_far hR hd⟩

/-- A full-face Go source cannot be an internal-terminal mate: its quotient is
the live prime owner `q ≥ 2`, whereas every internal-terminal mate has state
`(1,1)`. -/
theorem squareRootLowPrimeGoFullFaceDefectSourceImage_disjoint_internalMate
    {R : ℕ} :
    Disjoint (squareRootLowPrimeGoFullFaceDefectSourceImage R)
      (lowWheelCanonicalRepeatedTerminalInternalMateImage R) := by
  rw [Finset.disjoint_left]
  intro z hzSource hzInternal
  rcases Finset.mem_image.mp hzSource with ⟨⟨⟨r, q⟩, d⟩, hd, rfl⟩
  have hq :=
    (mem_squareRootLowPrimeGoFullFaceDefectCarrier.mp hd).2.2.2.2.1
  have hone :=
    lowWheelCanonicalRepeatedTerminalInternalMateImage_state_eq_one hzInternal
  have hquot := congrArg Prod.snd hone
  change q = 1 at hquot
  have hqTwo : 2 ≤ q := hq.two_le
  omega

/-- A full-face Go source cannot be a frozen-top owned image.  The source
quotient is prime.  A frozen-top image has quotient `q_top * p`, where `q_top`
and the frozen pivot `p` are both nonunit primes. -/
theorem squareRootLowPrimeGoFullFaceDefectSourceImage_disjoint_topImage
    {R : ℕ} :
    Disjoint (squareRootLowPrimeGoFullFaceDefectSourceImage R)
      (lowWheelFrozenCofactorTopImage R) := by
  rw [Finset.disjoint_left]
  intro z hzSource hzTop
  rcases Finset.mem_image.mp hzSource with ⟨⟨⟨r, q⟩, d⟩, hd, rfl⟩
  rcases mem_lowWheelFrozenCofactorTopImage.mp hzTop with ⟨y, hy, htop⟩
  have hqPrime :=
    (mem_squareRootLowPrimeGoFullFaceDefectCarrier.mp hd).2.2.2.2.1
  have htopPrime := (lowWheelFrozenCofactorTopPrime_data hy).1
  have hquot := congrArg
    (fun w : LowWheelFullTaggedPhysicalState => w.2.2) htop
  have hquotEq :
      lowWheelFrozenCofactorTopPrime y * y.2.2 = q := by
    rw [lowWheelFrozenCofactorTopToggle_eq hy] at hquot
    simpa [squareRootLowPrimeGoFullFaceDefectSourceTag,
      squareRootLowPrimeGoSecondBoundaryFullFaceSource] using hquot
  have hdiv : lowWheelFrozenCofactorTopPrime y ∣ q :=
    ⟨y.2.2, hquotEq.symm⟩
  have htopEq : lowWheelFrozenCofactorTopPrime y = q :=
    (Nat.prime_dvd_prime_iff_eq htopPrime hqPrime).mp hdiv
  have hpPrime := lowWheelFrozenCofactor_pivot_prime hy
  have hshape := lowWheelFrozenCofactor_quotient_eq_pivot hy
  have htwo : 2 ≤ y.2.2 := by
    rw [hshape]
    exact hpPrime.two_le
  rw [htopEq] at hquotEq
  nlinarith [hqPrime.pos, htwo]

/-- Exact quotient shape of a defect mate.  Its quotient acquires the least
active face prime as a second nonunit prime factor beside the outer owner. -/
theorem squareRootLowPrimeGoFullFaceDefectMateTag_quotient_eq
    {R r q d : ℕ} (hR : 2 ≤ R)
    (hz : ((r, q), d) ∈ squareRootLowPrimeGoFullFaceDefectCarrier R) :
    (squareRootLowPrimeGoFullFaceDefectMateTag R ((r, q), d)).2.2 =
      lowWheelFullOppositePrime R
          (squareRootLowPrimeGoFullFaceDefectSourceTag ((r, q), d)) * q := by
  let s := squareRootLowPrimeGoFullFaceDefectSourceTag ((r, q), d)
  let p := lowWheelFullOppositePrime R s
  have hpData :=
    squareRootLowPrimeGoFullFaceDefect_oppositePrime_lt_interior hR hz
  dsimp only at hpData
  rcases hpData with ⟨hnonempty, _hpPrime, _hpr, hpFace⟩
  change (lowWheelFullFaceQuotientMate R s).2.2 = p * q
  unfold lowWheelFullFaceQuotientMate
  rw [dif_pos hnonempty]
  change (lowWheelFullFaceQuotientToggleAt p s).2.2 = p * q
  unfold lowWheelFullFaceQuotientToggleAt
  dsimp only
  unfold lowWheelFaceTailToggleAt
  rw [if_pos hpFace]
  rfl

/-- Source and mate images are disjoint.  A source quotient is prime, while a
mate quotient is the product of the prime opposite direction and the prime
outer owner. -/
theorem squareRootLowPrimeGoFullFaceDefectSourceImage_disjoint_mateImage
    {R : ℕ} (hR : 2 ≤ R) :
    Disjoint (squareRootLowPrimeGoFullFaceDefectSourceImage R)
      (squareRootLowPrimeGoFullFaceDefectMateImage R) := by
  rw [Finset.disjoint_left]
  intro z hzSource hzMate
  rcases Finset.mem_image.mp hzSource with ⟨⟨⟨r, q⟩, d⟩, hd, rfl⟩
  rcases Finset.mem_image.mp hzMate with ⟨⟨⟨s, t⟩, e⟩, he, hmate⟩
  have hqPrime :=
    (mem_squareRootLowPrimeGoFullFaceDefectCarrier.mp hd).2.2.2.2.1
  have htPrime :=
    (mem_squareRootLowPrimeGoFullFaceDefectCarrier.mp he).2.2.2.2.1
  have hpData :=
    squareRootLowPrimeGoFullFaceDefect_oppositePrime_lt_interior hR he
  dsimp only at hpData
  rcases hpData with ⟨_hnonempty, hpPrime, _hps, _hpFace⟩
  let p := lowWheelFullOppositePrime R
    (squareRootLowPrimeGoFullFaceDefectSourceTag ((s, t), e))
  have hmateQuot :=
    squareRootLowPrimeGoFullFaceDefectMateTag_quotient_eq hR he
  have hquot := congrArg
    (fun w : LowWheelFullTaggedPhysicalState => w.2.2) hmate
  have hprod : p * t = q := by
    rw [hmateQuot] at hquot
    simpa [squareRootLowPrimeGoFullFaceDefectSourceTag,
      squareRootLowPrimeGoSecondBoundaryFullFaceSource] using hquot
  have hpDvd : p ∣ q := ⟨t, hprod.symm⟩
  have hpEq : p = q :=
    (Nat.prime_dvd_prime_iff_eq hpPrime hqPrime).mp hpDvd
  rw [hpEq] at hprod
  nlinarith [hqPrime.pos, htPrime.two_le]

/-- The source image avoids the entire old owned-image union. -/
theorem squareRootLowPrimeGoFullFaceDefectSourceImage_disjoint_owned
    {R : ℕ} :
    Disjoint (squareRootLowPrimeGoFullFaceDefectSourceImage R)
      (lowWheelFrozenTopFarOwnedImage R) := by
  rw [Finset.disjoint_left]
  intro z hzSource hzOwned
  rcases Finset.mem_union.mp hzOwned with hzInternal | hzTop
  · exact (Finset.disjoint_left.mp
      squareRootLowPrimeGoFullFaceDefectSourceImage_disjoint_internalMate)
      hzSource (Finset.mem_filter.mp hzInternal).1
  · exact (Finset.disjoint_left.mp
      squareRootLowPrimeGoFullFaceDefectSourceImage_disjoint_topImage)
      hzSource hzTop

/-- Hence every source occurrence belongs to the old hard physical residual. -/
theorem squareRootLowPrimeGoFullFaceDefectSourceImage_subset_physicalResidual
    {R : ℕ} (hR : 6 ≤ R) :
    squareRootLowPrimeGoFullFaceDefectSourceImage R ⊆
      lowWheelFrozenTopFarPhysicalResidualCarrier R := by
  intro z hzSource
  apply Finset.mem_sdiff.mpr
  refine ⟨squareRootLowPrimeGoFullFaceDefectSourceImage_subset_farPhysical hR
      hzSource, ?_⟩
  intro hzOwned
  exact (Finset.disjoint_left.mp
    squareRootLowPrimeGoFullFaceDefectSourceImage_disjoint_owned)
    hzSource hzOwned

/-- **One-copy theorem after #643.**  The live full-face Go source image remains
inside the mate-deleted reduced physical carrier.  The mate image has been
removed; the source image has not. -/
theorem squareRootLowPrimeGoFullFaceDefectSourceImage_subset_reducedPhysical
    {R : ℕ} (hR : 6 ≤ R) :
    squareRootLowPrimeGoFullFaceDefectSourceImage R ⊆
      squareRootLowPrimeGoReducedPhysicalResidualCarrier R := by
  intro z hzSource
  apply Finset.mem_sdiff.mpr
  refine ⟨squareRootLowPrimeGoFullFaceDefectSourceImage_subset_physicalResidual
      hR hzSource, ?_⟩
  intro hzMateFar
  have hzMate := (Finset.mem_filter.mp hzMateFar).1
  exact (Finset.disjoint_left.mp
    (squareRootLowPrimeGoFullFaceDefectSourceImage_disjoint_mateImage
      (by omega : 2 ≤ R))) hzSource hzMate

/-- Literal complement of the one surviving defect-source packet inside the
#643 reduced carrier. -/
def squareRootLowPrimeGoReducedPhysicalResidualRemainderCarrier (R : ℕ) :
    Finset LowWheelFullTaggedPhysicalState :=
  squareRootLowPrimeGoReducedPhysicalResidualCarrier R \
    squareRootLowPrimeGoFullFaceDefectSourceImage R

/-- Signed mass of the literal complementary reduced packet. -/
def squareRootLowPrimeGoReducedPhysicalResidualRemainderLedger (R : ℕ) : ℂ :=
  ∑ z ∈ squareRootLowPrimeGoReducedPhysicalResidualRemainderCarrier R,
    lowWheelFullTaggedPhysicalWeight z

/-- **Exact one-packet decomposition.**  After mate deletion the reduced
physical ledger is one surviving defect-source packet plus the literal
complement.  This is a set decomposition before any norm, not a frame bound. -/
theorem squareRootLowPrimeGoReducedPhysicalResidualLedger_eq_source_add_remainder
    {R : ℕ} (hR : 6 ≤ R) :
    squareRootLowPrimeGoReducedPhysicalResidualLedger R =
      squareRootLowPrimeGoFullFaceDefectSourceLedger R +
        squareRootLowPrimeGoReducedPhysicalResidualRemainderLedger R := by
  have hsub :=
    squareRootLowPrimeGoFullFaceDefectSourceImage_subset_reducedPhysical hR
  have hs := Finset.sum_sdiff hsub (f := lowWheelFullTaggedPhysicalWeight)
  rw [squareRootLowPrimeGoFullFaceDefectSourceLedger_eq_imageSum]
  simpa [squareRootLowPrimeGoReducedPhysicalResidualLedger,
    squareRootLowPrimeGoReducedPhysicalResidualRemainderLedger,
    squareRootLowPrimeGoReducedPhysicalResidualRemainderCarrier,
    add_comm] using hs.symm

/-- Same decomposition with the source packet returned to its arithmetic Go
mass. -/
theorem squareRootLowPrimeGoReducedPhysicalResidualLedger_eq_defectMass_add_remainder
    {R : ℕ} (hR : 6 ≤ R) :
    squareRootLowPrimeGoReducedPhysicalResidualLedger R =
      ((squareRootLowPrimeGoFullFaceDefectSourceMass R : ℤ) : ℂ) +
        squareRootLowPrimeGoReducedPhysicalResidualRemainderLedger R := by
  rw [squareRootLowPrimeGoReducedPhysicalResidualLedger_eq_source_add_remainder hR,
    squareRootLowPrimeGoFullFaceDefectSourceLedger_eq_mass]

end RHLean.Proof