import Mathlib
import RHLean.Proof.SquareRootLowPrimeGoReducedSourcePacket
import RHLean.Proof.LowWheelFrozenSecondContactRoughPrefix
import RHLean.Proof.LowWheelFrozenSecondContactWindowReassembly

/-!
# Combined residual / saturated second-contact pushforward

This module is deliberately structural.  It takes no norm and proves no energy
estimate.  The first job is to place the full-face Go source from #645 on the
*existing saturated* second-contact arithmetic carrier, not on the superseded
loose `X/q^2` window and not on a fictitious square-divisible deletion cell.

For an incidence `((r,q),d)`, write

`n = q * (r*d)`.

#645 proves that the physical full-face source is pre-contact for `q`: `q`
appears once and one further `q` crosses the square endpoint.  The independent
arithmetic description of the saturated #629 carrier says that `n` is a genuine
second-contact child exactly when the additional root-floor wall

`R*q < n`

holds.  Here that wall is simply `R < r*d`.  Thus the full-face defect splits
canonically into a saturated child population and the explicit root-floor
failure `r*d <= R`.

The saturated child has the correct signed orientation: the full-face source
weight is `mu(q*d)`, while the arithmetic child has weight `mu(q*r*d) =
-mu(q*d)`.  This is exactly the minus sign in
`lowWheelFrozenSecondContactSource_sum_eq_neg_crossColumnChildMass`.

No statement below treats the root-floor complement as generic leakage; it is
kept as its literal incidence carrier.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open CanonicalGapAncestryBridge

attribute [local instance] Classical.propDecidable

/-- Full-face defect incidences whose represented pre-contact integer is above
the saturated `R*q` root floor. -/
def squareRootLowPrimeGoFullFaceDefectSaturatedIncidences (R : ℕ) :
    Finset SquareRootLowPrimeGoFullFaceDefectIncidence :=
  (squareRootLowPrimeGoFullFaceDefectCarrier R).filter fun z =>
    R < z.1.1 * z.2

/-- The exact complementary root-floor failures. -/
def squareRootLowPrimeGoFullFaceDefectRootFloorIncidences (R : ℕ) :
    Finset SquareRootLowPrimeGoFullFaceDefectIncidence :=
  (squareRootLowPrimeGoFullFaceDefectCarrier R).filter fun z =>
    z.1.1 * z.2 <= R

/-- Arithmetic pre-contact child represented by one full-face source. -/
def squareRootLowPrimeGoFullFaceDefectArithmeticChild
    (z : SquareRootLowPrimeGoFullFaceDefectIncidence) : ℕ :=
  z.1.2 * (z.1.1 * z.2)

@[simp] theorem mem_squareRootLowPrimeGoFullFaceDefectSaturatedIncidences
    {R r q d : ℕ} :
    ((r, q), d) ∈ squareRootLowPrimeGoFullFaceDefectSaturatedIncidences R ↔
      ((r, q), d) ∈ squareRootLowPrimeGoFullFaceDefectCarrier R ∧
        R < r * d := by
  simp [squareRootLowPrimeGoFullFaceDefectSaturatedIncidences]

@[simp] theorem mem_squareRootLowPrimeGoFullFaceDefectRootFloorIncidences
    {R r q d : ℕ} :
    ((r, q), d) ∈ squareRootLowPrimeGoFullFaceDefectRootFloorIncidences R ↔
      ((r, q), d) ∈ squareRootLowPrimeGoFullFaceDefectCarrier R ∧
        r * d <= R := by
  simp [squareRootLowPrimeGoFullFaceDefectRootFloorIncidences]

/-- The two incidence populations are an exact partition of the #645 defect. -/
theorem squareRootLowPrimeGoFullFaceDefectCarrier_eq_saturated_union_rootFloor
    (R : ℕ) :
    squareRootLowPrimeGoFullFaceDefectCarrier R =
      squareRootLowPrimeGoFullFaceDefectSaturatedIncidences R ∪
        squareRootLowPrimeGoFullFaceDefectRootFloorIncidences R := by
  ext z
  rcases z with ⟨⟨r, q⟩, d⟩
  by_cases h : R < r * d
  · simp [h]
  · have hle : r * d <= R := Nat.le_of_not_gt h
    simp [h, hle]

/-- The saturated and root-floor pieces are disjoint. -/
theorem squareRootLowPrimeGoFullFaceDefectSaturated_disjoint_rootFloor
    (R : ℕ) :
    Disjoint (squareRootLowPrimeGoFullFaceDefectSaturatedIncidences R)
      (squareRootLowPrimeGoFullFaceDefectRootFloorIncidences R) := by
  rw [Finset.disjoint_left]
  intro z hsat hroot
  rcases z with ⟨⟨r, q⟩, d⟩
  have hlt :=
    (mem_squareRootLowPrimeGoFullFaceDefectSaturatedIncidences.mp hsat).2
  have hle :=
    (mem_squareRootLowPrimeGoFullFaceDefectRootFloorIncidences.mp hroot).2
  omega

/-- The source high product is exactly the independent arithmetic child. -/
theorem squareRootLowPrimeGoFullFaceDefectSource_highProduct_eq_child
    {r q d : ℕ} :
    lowWheelTaggedHighProduct
        (squareRootLowPrimeGoFullFaceDefectSourceTag ((r, q), d)) =
      squareRootLowPrimeGoFullFaceDefectArithmeticChild ((r, q), d) := by
  rfl

/-- The distinguished outer owner is the canonical largest prime of the
arithmetic child. -/
theorem squareRootLowPrimeGoFullFaceDefectArithmeticChild_largestPrime
    {R r q d : ℕ}
    (hz : ((r, q), d) ∈ squareRootLowPrimeGoFullFaceDefectCarrier R) :
    canonicalLargestPrimeFactor
        (squareRootLowPrimeGoFullFaceDefectArithmeticChild ((r, q), d)) = q := by
  rcases mem_squareRootLowPrimeGoFullFaceDefectCarrier.mp hz with
    ⟨_hrR, _hqR, _hdR, hr, hq, hrq, _hcube, hd⟩
  have hfull :=
    (mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp hd).1
  have hchild :=
    squareRootLowPrimeGoFullBirthBoundary_child_canonicalSmooth hq hr hrq hfull
  rcases hchild.1 with ⟨_hq, hrd1, _hsq, _hcop, hdom⟩
  have hrdgt : 1 < r * d := lt_trans hq.one_lt hchild.2
  have hrough : canonicalLargestPrimeFactor (r * d) < q :=
    hdom _ (canonicalLargestPrimeFactor_prime hrdgt)
      (canonicalLargestPrimeFactor_dvd hrdgt)
  have htop := canonicalLargestPrimeFactor_mul_prime_eq_of_rough
    (by omega : 0 < r * d) hq hrough
  simpa [squareRootLowPrimeGoFullFaceDefectArithmeticChild, Nat.mul_comm] using htop

/-- **Positive splice.**  Above the root floor, the represented full-face Go
source integer is literally a member of the independent saturated second-contact
arithmetic child carrier.  The state itself is pre-contact; the carrier records
that one further copy of its canonical largest prime crosses the endpoint. -/
theorem squareRootLowPrimeGoFullFaceDefectArithmeticChild_mem_saturatedCarrier
    {R r q d : ℕ}
    (hz : ((r, q), d) ∈ squareRootLowPrimeGoFullFaceDefectSaturatedIncidences R) :
    squareRootLowPrimeGoFullFaceDefectArithmeticChild ((r, q), d) ∈
      lowWheelFrozenSecondContactArithmeticChildCarrier R := by
  rcases mem_squareRootLowPrimeGoFullFaceDefectSaturatedIncidences.mp hz with
    ⟨hzFull, hroot⟩
  rcases mem_squareRootLowPrimeGoFullFaceDefectCarrier.mp hzFull with
    ⟨_hrR, hqR, _hdR, hr, hq, hrq, hcube, hd⟩
  have hfull :=
    (mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp hd).1
  have hchild :=
    squareRootLowPrimeGoFullBirthBoundary_child_canonicalSmooth hq hr hrq hfull
  rcases hchild.1 with ⟨_hq, hrd1, hsqRD, hcop, _hdom⟩
  have hsq : Squarefree (q * (r * d)) :=
    (Nat.squarefree_mul hcop).2 ⟨hq.squarefree, hsqRD⟩
  have hfirst :=
    squareRootLowPrimeGoFullBirthBoundary_firstContact_le
      hq hrq hcube hfull
  have hsecond :=
    squareRootLowPrimeGoSecondBoundaryDefect_secondContact_gt hq hr hd
  have hlpf :=
    squareRootLowPrimeGoFullFaceDefectArithmeticChild_largestPrime hzFull
  unfold lowWheelFrozenSecondContactArithmeticChildCarrier
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, hsq, ?_, ?_, ?_⟩
  · have htwo := hq.two_le
    have hone : 1 <= r * d := hrd1
    nlinarith
  · simpa [squareRootLowPrimeGoFullFaceDefectArithmeticChild] using hfirst
  · simpa [hlpf] using hqR
  · rw [hlpf]
    simpa [squareRootLowPrimeGoFullFaceDefectArithmeticChild,
      Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hsecond
  · rw [hlpf]
    have hmul := Nat.mul_lt_mul_of_pos_right hroot hq.pos
    simpa [squareRootLowPrimeGoFullFaceDefectArithmeticChild,
      Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul

/-- Below the root floor the same arithmetic integer is *not* in the saturated
carrier: the failed condition is exactly `R*q < n`. -/
theorem squareRootLowPrimeGoFullFaceDefectArithmeticChild_not_mem_saturatedCarrier
    {R r q d : ℕ}
    (hz : ((r, q), d) ∈ squareRootLowPrimeGoFullFaceDefectRootFloorIncidences R) :
    squareRootLowPrimeGoFullFaceDefectArithmeticChild ((r, q), d) ∉
      lowWheelFrozenSecondContactArithmeticChildCarrier R := by
  rcases mem_squareRootLowPrimeGoFullFaceDefectRootFloorIncidences.mp hz with
    ⟨hzFull, hroot⟩
  have hlpf :=
    squareRootLowPrimeGoFullFaceDefectArithmeticChild_largestPrime hzFull
  intro hmem
  have hwall := (Finset.mem_filter.mp hmem).2.2.2.2
  rw [hlpf] at hwall
  have hq :=
    (mem_squareRootLowPrimeGoFullFaceDefectCarrier.mp hzFull).2.2.2.2.1
  have hmul :
      squareRootLowPrimeGoFullFaceDefectArithmeticChild ((r, q), d) <= R * q := by
    have := Nat.mul_le_mul_right q hroot
    simpa [squareRootLowPrimeGoFullFaceDefectArithmeticChild,
      Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using this
  omega

/-- The source sign is exactly the saturated-source orientation: it is the
negative ordinary Mobius weight of the arithmetic child. -/
theorem squareRootLowPrimeGoFullFaceDefectSource_weight_eq_neg_child
    {R r q d : ℕ}
    (hz : ((r, q), d) ∈ squareRootLowPrimeGoFullFaceDefectCarrier R) :
    lowWheelFullTaggedPhysicalWeight
        (squareRootLowPrimeGoFullFaceDefectSourceTag ((r, q), d)) =
      -canonicalMoebiusWeight
        (squareRootLowPrimeGoFullFaceDefectArithmeticChild ((r, q), d)) := by
  rcases mem_squareRootLowPrimeGoFullFaceDefectCarrier.mp hz with
    ⟨_hrR, _hqR, _hdR, hr, hq, hrq, _hcube, hd⟩
  have hfull :=
    (mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp hd).1
  have hdgt := squareRootLowPrimeGoFullBirthBoundary_parent_one_lt hr hrq hfull
  have hrough :=
    (mem_squareRootLowPrimeGoFullBirthBoundaryParents.mp hfull).2.2.2.1
  have hrNotDvdD : ¬ r ∣ d := by
    intro hrd
    have hle :=
      CanonicalGapAncestryBridge.prime_dvd_le_canonicalLargestPrimeFactor
        hdgt hr hrd
    omega
  have hrNotDvdQ : ¬ r ∣ q := by
    intro hrqDvd
    have heq := (Nat.prime_dvd_prime_iff_eq hr hq).mp hrqDvd
    omega
  have hrNotDvdQD : ¬ r ∣ q * d := by
    intro hdiv
    rcases hr.dvd_mul.mp hdiv with hqdiv | hddiv
    · exact hrNotDvdQ hqdiv
    · exact hrNotDvdD hddiv
  have hmu :
      μ (squareRootLowPrimeGoFullFaceDefectArithmeticChild ((r, q), d)) =
        -μ (q * d) := by
    change μ (q * (r * d)) = -μ (q * d)
    rw [show q * (r * d) = r * (q * d) by ring]
    exact moebius_prime_mul hr hrNotDvdQD
  rw [squareRootLowPrimeGoFullFaceDefectSourceLedger_eq_mass] at *
  have hsource :=
    squareRootLowPrimeGoSecondBoundaryFullFaceSource_weight_eq
      hq hr hrq hfull
  simpa [squareRootLowPrimeGoFullFaceDefectSourceTag,
    canonicalMoebiusWeight, hmu] using hsource

/-- The full-face source is not literally one of the frozen nontrivial-cofactor
second-contact source states: its low cofactor is `1`.  This records the
coordinate change that the arithmetic-child map above performs. -/
theorem squareRootLowPrimeGoFullFaceDefectSource_not_literal_frozenSource
    {R r q d : ℕ}
    (hz : ((r, q), d) ∈ squareRootLowPrimeGoFullFaceDefectCarrier R) :
    squareRootLowPrimeGoFullFaceDefectSourceTag ((r, q), d) ∉
      lowWheelCanonicalRepeatedFrozenSecondContactPart R := by
  intro hmem
  have hfrozen := (Finset.mem_filter.mp hmem).1
  have hdata := lowWheelCanonicalRepeatedFrozenCofactor_source_data hfrozen
  have hcgt := hdata.2.2.2.2.1
  simpa [squareRootLowPrimeGoFullFaceDefectSourceTag,
    squareRootLowPrimeGoSecondBoundaryFullFaceSource] using hcgt

/-- Nor is the full-face source literally a RoughPrefix historical fixed
transport mate: every such mate has cofactor/quotient state `(1,1)`, while the
Go pre-contact source retains the prime quotient `q`. -/
theorem squareRootLowPrimeGoFullFaceDefectSource_not_literal_matchingFixedTransport
    {R r q d A : ℕ}
    (hz : ((r, q), d) ∈ squareRootLowPrimeGoFullFaceDefectCarrier R) :
    squareRootLowPrimeGoFullFaceDefectSourceTag ((r, q), d) ∉
      lowWheelFrozenSourceScaleTransportCarrier R A := by
  intro hmem
  rcases Finset.mem_image.mp hmem with ⟨y, _hy, heq⟩
  have hstate := congrArg (fun z : LowWheelTaggedCofactorQuotientState => z.2) heq
  have hqPrime :=
    (mem_squareRootLowPrimeGoFullFaceDefectCarrier.mp hz).2.2.2.2.1
  have hqTwo := hqPrime.two_le
  simp [squareRootLowPrimeGoFullFaceDefectSourceTag,
    squareRootLowPrimeGoSecondBoundaryFullFaceSource,
    lowWheelCanonicalRepeatedFrozenProductOneMate] at hstate
  omega

end RHLean.Proof
