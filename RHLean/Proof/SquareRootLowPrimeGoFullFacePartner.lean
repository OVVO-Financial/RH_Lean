import Mathlib
import RHLean.Proof.LowWheelFullFaceQuotientOthello
import RHLean.Proof.SquareRootLowPrimeGoGlobalPartner

/-!
# Full-face transport partner for every Go second-boundary defect

The singleton Go crossing map only uses the face `{r}` and therefore requires
`R < r*q`.  That is unnecessarily restrictive.  A second-boundary defect
already carries the complete squarefree child `r*d`.  Put *all* prime factors
of that child on the Boolean face, keep cofactor `1`, and retain the outer owner
`q` as the high quotient.

The physical first contact gives the top-product ceiling.  The second contact
forces the full face strictly across the root: otherwise

`q * (r*d) <= R`

would imply `q^2 * (r*d) < R^2`, contradicting
`R^2 - 1 < q^2 * (r*d)`.

Thus every two-boundary defect is a literal occurrence of the complete tagged
low-wheel transport carrier.  Its signed face weight is exactly the defect
source weight `mu(q*d)`.  The already-compiled full face/quotient Othello mate
then gives an opposite-sign physical occurrence, with no extra singleton
crossing hypothesis and no root-equality exception.

No norm, density estimate, PNT input, Mertens estimate, or asymptotic claim is
used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Full tagged transport occurrence attached to one Go defect incidence. -/
def squareRootLowPrimeGoSecondBoundaryFullFaceSource
    (r q d : ℕ) : LowWheelFullTaggedPhysicalState :=
  (squarefreePrimeFace (r * d), (1, q))

/-- A genuinely unfinished Go owner lies strictly below the physical root. -/
theorem squareRootLowPrimeGoFullFace_liveOwner_lt_root
    {R q : ℕ} (hR : 2 ≤ R) (_hq : q.Prime)
    (hcube : q ^ 3 ≤ squareRootEndpoint R) :
    q < R := by
  have hXlt : squareRootEndpoint R < R ^ 2 := by
    unfold squareRootEndpoint
    have hpos : 0 < R ^ 2 := by positivity
    omega
  have hq3lt : q ^ 3 < R ^ 2 := hcube.trans_lt hXlt
  by_contra hnot
  have hRq : R ≤ q := Nat.le_of_not_gt hnot
  have hR2leR3 : R ^ 2 ≤ R ^ 3 := by
    calc
      R ^ 2 = R ^ 2 * 1 := by simp
      _ ≤ R ^ 2 * R := Nat.mul_le_mul_left (R ^ 2) (by omega)
      _ = R ^ 3 := by ring
  have hR3leQ3 : R ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hRq 3
  omega

/-- The full Boolean face recovers exactly the complete Go child product. -/
theorem squareRootLowPrimeGoSecondBoundaryFullFaceSource_faceProduct
    {q r d : ℕ} (hq : q.Prime) (hr : r.Prime) (hrq : r < q)
    (hd : d ∈ squareRootLowPrimeGoFullBirthBoundaryParents q r) :
    primeFaceProduct
        (squareRootLowPrimeGoSecondBoundaryFullFaceSource r q d).1 =
      r * d := by
  have hchild :=
    squareRootLowPrimeGoFullBirthBoundary_child_canonicalSmooth hq hr hrq hd
  exact primeFaceProduct_squarefreePrimeFace hchild.1.2.2.1

/-- **Every Go second-boundary defect is a literal full-face transport state.**
The full face removes the artificial singleton condition `R < r*q`. -/
theorem squareRootLowPrimeGoSecondBoundaryFullFaceSource_mem_transport
    {R q r d : ℕ} (hR : 2 ≤ R)
    (hq : q.Prime) (hr : r.Prime) (hrq : r < q)
    (hcube : q ^ 3 ≤ squareRootEndpoint R)
    (hd : d ∈ squareRootLowPrimeGoSecondBoundaryDefectParents q
      (squareRootEndpoint R) r) :
    squareRootLowPrimeGoSecondBoundaryFullFaceSource r q d ∈
      lowWheelFullTaggedPhysicalCarrier R := by
  let y := squareRootLowPrimeGoSecondBoundaryFullFaceSource r q d
  have hfull :=
    (mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp hd).1
  have hchild :=
    squareRootLowPrimeGoFullBirthBoundary_child_canonicalSmooth hq hr hrq hfull
  have hsqChild : Squarefree (r * d) := hchild.1.2.2.1
  have hdom := hchild.1.2.2.2.2
  have hqR : q < R :=
    squareRootLowPrimeGoFullFace_liveOwner_lt_root hR hq hcube
  have hfaceProd : primeFaceProduct y.1 = r * d := by
    simpa [y, squareRootLowPrimeGoSecondBoundaryFullFaceSource] using
      primeFaceProduct_squarefreePrimeFace hsqChild
  have hface : y.1 ∈ (primesUpTo R).powerset := by
    apply Finset.mem_powerset.mpr
    intro p hp
    have hpFactors : p ∈ (r * d).primeFactors := by
      simpa [y, squareRootLowPrimeGoSecondBoundaryFullFaceSource,
        squarefreePrimeFace] using hp
    have hpData := Nat.mem_primeFactors.mp hpFactors
    have hpLtQ : p < q := hdom p hpData.1 hpData.2.1
    exact mem_primesUpTo.mpr ⟨hpData.1, by omega⟩
  have hfirst :=
    squareRootLowPrimeGoFullBirthBoundary_firstContact_le
      hq hrq hcube hfull
  have hsecond :=
    squareRootLowPrimeGoSecondBoundaryDefect_secondContact_gt hq hr hd
  have hroot : R < (r * d) * q := by
    by_contra hnot
    have hle : (r * d) * q ≤ R := Nat.le_of_not_gt hnot
    have hqRmul : q * R < R * R :=
      Nat.mul_lt_mul_of_pos_right hqR (by omega)
    have hlt : q * q * (r * d) < R ^ 2 := by
      calc
        q * q * (r * d) = q * ((r * d) * q) := by ring
        _ ≤ q * R := Nat.mul_le_mul_left q hle
        _ < R * R := hqRmul
        _ = R ^ 2 := by ring
    have hnotSecond : ¬ squareRootEndpoint R < q * q * (r * d) := by
      unfold squareRootEndpoint
      omega
    exact hnotSecond hsecond
  have hcarrier : LowWheelTransportPairCarrier R y.1 y.2 := by
    change LowWheelTransportPairCarrier R y.1 (1, q)
    refine ⟨by simp, by omega, ?_, ?_⟩
    · rw [hfaceProd]
      exact hroot
    · rw [hfaceProd]
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hfirst
  have hranges := lowWheelTransportPairCarrier_mem_ranges hcarrier
  apply mem_lowWheelFullTaggedPhysicalCarrier.mpr
  refine ⟨hface, mem_lowWheelCanonicalPhysicalStateSet.mpr ?_⟩
  exact ⟨hranges.1, hranges.2, by simp [y], hcarrier⟩

/-- The full-face occurrence has exactly the raw Go defect source sign. -/
theorem squareRootLowPrimeGoSecondBoundaryFullFaceSource_weight_eq
    {q r d : ℕ} (hq : q.Prime) (hr : r.Prime) (hrq : r < q)
    (hd : d ∈ squareRootLowPrimeGoFullBirthBoundaryParents q r) :
    lowWheelFullTaggedPhysicalWeight
        (squareRootLowPrimeGoSecondBoundaryFullFaceSource r q d) =
      canonicalMoebiusWeight (q * d) := by
  have hchild :=
    squareRootLowPrimeGoFullBirthBoundary_child_canonicalSmooth hq hr hrq hd
  have hsqChild : Squarefree (r * d) := hchild.1.2.2.1
  have hfaceProd :
      primeFaceProduct (squarefreePrimeFace (r * d)) = r * d :=
    primeFaceProduct_squarefreePrimeFace hsqChild
  have hfacePrime : ∀ p ∈ squarefreePrimeFace (r * d), p.Prime := by
    intro p hp
    exact (Nat.mem_primeFactors.mp (by
      simpa [squarefreePrimeFace] using hp)).1
  have hfaceMu :=
    moebius_primeFaceProduct_eq_booleanCubeSign
      (squarefreePrimeFace (r * d)) hfacePrime
  have hdgt := squareRootLowPrimeGoFullBirthBoundary_parent_one_lt hr hrq hd
  have hrough :=
    (mem_squareRootLowPrimeGoFullBirthBoundaryParents.mp hd).2.2.2.1
  have hrNotDvd : ¬ r ∣ d := by
    intro hrd
    have hle := prime_dvd_le_canonicalLargestPrimeFactor hdgt hr hrd
    omega
  have hmuR : μ (r * d) = -μ d := by
    exact moebius_prime_mul hr hrNotDvd
  have hmuQ : (μ (q * d) : ℤ) = -(μ d : ℤ) :=
    squareRootLowPrimeGoFullBirthBoundary_parentSourceWeight_eq_neg
      hq hr hrq hd
  have hsign : booleanCubeSign (squarefreePrimeFace (r * d)) = μ (q * d) := by
    calc
      booleanCubeSign (squarefreePrimeFace (r * d)) =
          μ (primeFaceProduct (squarefreePrimeFace (r * d))) := hfaceMu.symm
      _ = μ (r * d) := by rw [hfaceProd]
      _ = -μ d := hmuR
      _ = μ (q * d) := hmuQ.symm
  unfold squareRootLowPrimeGoSecondBoundaryFullFaceSource
    lowWheelFullTaggedPhysicalWeight canonicalMoebiusWeight
  simp only [Prod.fst, Prod.snd]
  norm_num
  exact_mod_cast hsign

/-- The complete full-face Othello mate moves every defect source and reverses
its sign.  Hence the source and its already-physical transport mate cancel
pointwise, with no `r*q = R` exceptional case. -/
theorem squareRootLowPrimeGoSecondBoundaryFullFaceSource_mate_cancel
    {R q r d : ℕ} (hR : 2 ≤ R)
    (hq : q.Prime) (hr : r.Prime) (hrq : r < q)
    (hcube : q ^ 3 ≤ squareRootEndpoint R)
    (hd : d ∈ squareRootLowPrimeGoSecondBoundaryDefectParents q
      (squareRootEndpoint R) r) :
    lowWheelFullTaggedPhysicalWeight
        (squareRootLowPrimeGoSecondBoundaryFullFaceSource r q d) +
      lowWheelFullTaggedPhysicalWeight
        (lowWheelFullFaceQuotientMate R
          (squareRootLowPrimeGoSecondBoundaryFullFaceSource r q d)) = 0 := by
  let y := squareRootLowPrimeGoSecondBoundaryFullFaceSource r q d
  have hy : y ∈ lowWheelFullTaggedPhysicalCarrier R := by
    simpa [y] using
      squareRootLowPrimeGoSecondBoundaryFullFaceSource_mem_transport
        hR hq hr hrq hcube hd
  have hfull :=
    (mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp hd).1
  have hchild :=
    squareRootLowPrimeGoFullBirthBoundary_child_canonicalSmooth hq hr hrq hfull
  have hdPos : 0 < d := by
    have hd1 := (mem_squareRootLowPrimeGoFullBirthBoundaryParents.mp hfull).1
    omega
  have hrFace : r ∈ y.1 := by
    have hrDvd : r ∣ r * d := dvd_mul_right r d
    have hrdNe : r * d ≠ 0 := Nat.mul_ne_zero hr.ne_zero (Nat.ne_of_gt hdPos)
    have hrFactors : r ∈ (r * d).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hr, hrDvd, hrdNe⟩
    simpa [y, squareRootLowPrimeGoSecondBoundaryFullFaceSource,
      squarefreePrimeFace] using hrFactors
  have hne : lowWheelFullFaceQuotientMate R y ≠ y := by
    intro hfix
    have hempty := lowWheelFullStable_face_eq_empty hy hfix
    rw [hempty] at hrFace
    simp at hrFace
  have hneg := lowWheelFullFaceQuotientMate_weight_neg hne
  change lowWheelFullTaggedPhysicalWeight y +
      lowWheelFullTaggedPhysicalWeight (lowWheelFullFaceQuotientMate R y) = 0
  rw [hneg]
  ring

end RHLean.Proof