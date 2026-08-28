import Mathlib
import RHLean.Proof.CanonicalGapAncestryBridge
import RHLean.Proof.LowWheelCanonicalDowncrossOwnership

/-!
# Canonical pairing of the late-parent downcross population

The `late` half of the canonical downcross ledger consists of first-failure
states whose invariant root-side parent

`a = P(t) * (k/p)`

still has a prime divisor at least the canonical pivot `p = minFac(c*k)`.

The canonical allocation coordinate is the largest prime divisor

`q = P⁺(a)`.

Because `a <= R`, this is an already-existing low-wheel coordinate.  The
late-parent condition implies `p <= q`.  If `q` is absent from the Boolean face,
primality forces it to divide `k/p`; if it is present, it can be moved from the
face into that quotient.  Thus `q` is the unique invariant coordinate for the
face/quotient allocation involution constructed below.

No magnitude or analytic estimate appears.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- A tagged occurrence remembers the Boolean face as well as the physical
cofactor/quotient state. -/
abbrev LowWheelCanonicalDowncrossTaggedState :=
  Finset ℕ × LowWheelCofactorQuotientState

/-- Common finite state universe underlying every physical low-wheel face. -/
def lowWheelCanonicalDowncrossStateUniverse
    (R : ℕ) : Finset LowWheelCofactorQuotientState :=
  (Finset.Ico 1 R).product (Finset.Icc 1 (squareRootEndpoint R))

/-- Tagged late-parent carrier, preserving face multiplicity exactly. -/
def lowWheelCanonicalDowncrossLateTaggedCarrier
    (R : ℕ) : Finset LowWheelCanonicalDowncrossTaggedState :=
  ((primesUpTo R).powerset.product
      (lowWheelCanonicalDowncrossStateUniverse R)).filter fun y =>
    y.2 ∈ lowWheelCanonicalDowncrossLateParentPart R y.1

@[simp] theorem mem_lowWheelCanonicalDowncrossLateTaggedCarrier
    {R : ℕ} {y : LowWheelCanonicalDowncrossTaggedState} :
    y ∈ lowWheelCanonicalDowncrossLateTaggedCarrier R ↔
      y.1 ∈ (primesUpTo R).powerset ∧
        y.2 ∈ lowWheelCanonicalDowncrossStateUniverse R ∧
        y.2 ∈ lowWheelCanonicalDowncrossLateParentPart R y.1 := by
  simp [lowWheelCanonicalDowncrossLateTaggedCarrier, and_assoc]

/-- Invariant root-side parent of one tagged occurrence. -/
def lowWheelCanonicalDowncrossTaggedParent
    (y : LowWheelCanonicalDowncrossTaggedState) : ℕ :=
  lowWheelCanonicalDowncrossParent y.1 y.2

/-- Canonical face/quotient allocation coordinate: the largest prime divisor of
the invariant root-side parent. -/
def lowWheelCanonicalDowncrossLatePrime
    (y : LowWheelCanonicalDowncrossTaggedState) : ℕ :=
  canonicalLargestPrimeFactor (lowWheelCanonicalDowncrossTaggedParent y)

/-- Signed weight of one tagged occurrence. -/
def lowWheelCanonicalDowncrossTaggedWeight
    (y : LowWheelCanonicalDowncrossTaggedState) : ℂ :=
  canonicalMoebiusWeight y.2.1 * (booleanCubeSign y.1 : ℂ)

/-- A late parent is nontrivial. -/
theorem lowWheelCanonicalDowncrossLate_parent_one_lt
    {R : ℕ} {y : LowWheelCanonicalDowncrossTaggedState}
    (hy : y ∈ lowWheelCanonicalDowncrossLateTaggedCarrier R) :
    1 < lowWheelCanonicalDowncrossTaggedParent y := by
  have hlate :=
    (mem_lowWheelCanonicalDowncrossLateTaggedCarrier.mp hy).2.2
  have hdown :=
    (mem_lowWheelCanonicalDowncrossLateParentPart.mp hlate).1
  rcases (mem_lowWheelCanonicalDowncrossLateParentPart.mp hlate).2 with
    ⟨q, hq, _hpq⟩
  rcases Nat.mem_primeFactors.mp hq with ⟨hqPrime, hqDvd, _⟩
  have hparentPos := lowWheelCanonicalDowncrossParent_pos hdown
  have hqLe : q ≤ lowWheelCanonicalDowncrossTaggedParent y :=
    Nat.le_of_dvd hparentPos hqDvd
  exact lt_of_lt_of_le hqPrime.one_lt hqLe

/-- The canonical late-parent coordinate is prime. -/
theorem lowWheelCanonicalDowncrossLatePrime_prime
    {R : ℕ} {y : LowWheelCanonicalDowncrossTaggedState}
    (hy : y ∈ lowWheelCanonicalDowncrossLateTaggedCarrier R) :
    (lowWheelCanonicalDowncrossLatePrime y).Prime := by
  exact canonicalLargestPrimeFactor_prime
    (lowWheelCanonicalDowncrossLate_parent_one_lt hy)

/-- The canonical late-parent coordinate divides the invariant parent. -/
theorem lowWheelCanonicalDowncrossLatePrime_dvd_parent
    {R : ℕ} {y : LowWheelCanonicalDowncrossTaggedState}
    (hy : y ∈ lowWheelCanonicalDowncrossLateTaggedCarrier R) :
    lowWheelCanonicalDowncrossLatePrime y ∣
      lowWheelCanonicalDowncrossTaggedParent y := by
  exact canonicalLargestPrimeFactor_dvd
    (lowWheelCanonicalDowncrossLate_parent_one_lt hy)

/-- Late means that the canonical parent prime lies at or above the pivot. -/
theorem lowWheelCanonicalDowncrossLate_pivot_le_prime
    {R : ℕ} {y : LowWheelCanonicalDowncrossTaggedState}
    (hy : y ∈ lowWheelCanonicalDowncrossLateTaggedCarrier R) :
    lowWheelCanonicalDowncrossPivot y.2 ≤
      lowWheelCanonicalDowncrossLatePrime y := by
  have hlate :=
    (mem_lowWheelCanonicalDowncrossLateTaggedCarrier.mp hy).2.2
  rcases (mem_lowWheelCanonicalDowncrossLateParentPart.mp hlate).2 with
    ⟨q, hq, hpq⟩
  rcases Nat.mem_primeFactors.mp hq with ⟨hqPrime, hqDvd, _⟩
  have hqLe : q ≤ lowWheelCanonicalDowncrossLatePrime y :=
    CanonicalGapAncestryBridge.prime_dvd_le_canonicalLargestPrimeFactor
      (lowWheelCanonicalDowncrossLate_parent_one_lt hy) hqPrime hqDvd
  exact hpq.trans hqLe

/-- The canonical late-parent prime is itself in the already-existing low wheel. -/
theorem lowWheelCanonicalDowncrossLatePrime_mem_primesUpTo
    {R : ℕ} {y : LowWheelCanonicalDowncrossTaggedState}
    (hy : y ∈ lowWheelCanonicalDowncrossLateTaggedCarrier R) :
    lowWheelCanonicalDowncrossLatePrime y ∈ primesUpTo R := by
  have hlate :=
    (mem_lowWheelCanonicalDowncrossLateTaggedCarrier.mp hy).2.2
  have hdown :=
    (mem_lowWheelCanonicalDowncrossLateParentPart.mp hlate).1
  have hgeom := lowWheelCanonicalDowncross_firstFailure_geometry hdown
  dsimp only at hgeom
  have hparentLe : lowWheelCanonicalDowncrossTaggedParent y ≤ R := hgeom.2.2.2.1
  have hparentPos := lowWheelCanonicalDowncrossParent_pos hdown
  have hprimeLeParent :
      lowWheelCanonicalDowncrossLatePrime y ≤
        lowWheelCanonicalDowncrossTaggedParent y :=
    Nat.le_of_dvd hparentPos
      (lowWheelCanonicalDowncrossLatePrime_dvd_parent hy)
  exact mem_primesUpTo.mpr
    ⟨lowWheelCanonicalDowncrossLatePrime_prime hy,
      hprimeLeParent.trans hparentLe⟩

/-- If the canonical allocation prime is not already stored in the Boolean
face, then it is stored in the quotient part `k/p` of the same parent. -/
theorem lowWheelCanonicalDowncrossLatePrime_dvd_quotient_of_not_mem_face
    {R : ℕ} {t : Finset ℕ} {c k : ℕ}
    (hy : (t, (c, k)) ∈ lowWheelCanonicalDowncrossLateTaggedCarrier R)
    (hqt : lowWheelCanonicalDowncrossLatePrime (t, (c, k)) ∉ t) :
    lowWheelCanonicalDowncrossLatePrime (t, (c, k)) ∣
      k / lowWheelCanonicalDowncrossPivot (c, k) := by
  have ht :=
    (mem_lowWheelCanonicalDowncrossLateTaggedCarrier.mp hy).1
  have hqPrime := lowWheelCanonicalDowncrossLatePrime_prime hy
  have hqDvdParent := lowWheelCanonicalDowncrossLatePrime_dvd_parent hy
  unfold lowWheelCanonicalDowncrossTaggedParent at hqDvdParent
  unfold lowWheelCanonicalDowncrossParent at hqDvdParent
  rcases hqPrime.dvd_mul.mp hqDvdParent with hqFace | hqQuot
  · exfalso
    have hqProd : lowWheelCanonicalDowncrossLatePrime (t, (c, k)) ∣
        t.prod id := by
      simpa [primeFaceProduct] using hqFace
    rcases (Prime.dvd_finset_prod_iff hqPrime.prime id).mp hqProd with
      ⟨r, hrt, hqr⟩
    have hrPrime : r.Prime :=
      prime_of_mem_primesUpTo ((Finset.mem_powerset.mp ht) hrt)
    have hqrEq : lowWheelCanonicalDowncrossLatePrime (t, (c, k)) = r :=
      (Nat.prime_dvd_prime_iff_eq hqPrime hrPrime).mp hqr
    exact hqt (hqrEq ▸ hrt)
  · exact hqQuot

end RHLean.Proof
