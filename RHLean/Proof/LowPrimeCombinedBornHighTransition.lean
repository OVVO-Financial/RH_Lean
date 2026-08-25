import Mathlib
import RHLean.Proof.LowPrimeCompletedPartnerWindowFold

/-!
# Combined born/high finite differences at one fresh low prime

The high parent/child response from `LowPrimeParentChildWindowDifference` has
three exact cases.  The important empirical correction is that the middle case
`a <= K < p*a` carries substantial mass, so the born and high channels must be
kept together before any estimate.

This module makes that combination literal.

First, for every cofactor `c < R`, all auxiliary cutoffs in the born partner
set are automatic: a prime partner lies exactly in

`P+(c) < q <= c`.

Consequently, on every old parent whose fresh child remains below `R`, the born
parent/child finite difference is an explicit difference of two prime
intervals.  We then add this signed born difference to the high response and
retain the complete three-way geometry:

* `p*a <= K`: only the born interval difference remains;
* `a <= K < p*a`: the born interval difference stays attached to the explicit
  high transition difference;
* `K < a`: the born interval difference stays attached to the completed
  `window - p*window` partner fold proved in
  `LowPrimeCompletedPartnerWindowFold`.

The theorem is pointwise on the chronological old Boolean face, so it can be
summed without changing signs.  It is an exact representation theorem only:
no norm, absolute value, PNT estimate, Mertens bound, RH input, or dissipation
claim appears.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Prime sites in a finite open/closed interval `(L,U]`. -/
def squareRootPrimeIntervalSet (L U : ℕ) : Finset ℕ :=
  (Finset.Ioc L U).filter Nat.Prime

/-- Cardinality of the prime interval `(L,U]`. -/
def squareRootPrimeIntervalCount (L U : ℕ) : ℕ :=
  (squareRootPrimeIntervalSet L U).card

/-- Below the root, the born partner set is exactly the prime interval
`(P+(c),c]`.  Both the displayed root cutoff and the product cutoff are
automatic consequences of `q <= c < R`. -/
theorem squareRootBornPartnerSet_eq_primeInterval_of_lt_root
    {R c : ℕ} (hcR : c < R) :
    squareRootBornPartnerSet R c =
      squareRootPrimeIntervalSet (canonicalLargestPrimeFactor c) c := by
  classical
  ext q
  constructor
  · intro hq
    rcases Finset.mem_filter.mp hq with
      ⟨hqRange, hqPrime, hrough, hqc, _hproduct⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr ⟨hrough, hqc⟩, hqPrime⟩
  · intro hq
    rcases Finset.mem_filter.mp hq with ⟨hqIoc, hqPrime⟩
    rcases Finset.mem_Ioc.mp hqIoc with ⟨hrough, hqc⟩
    have hqR : q ≤ R := hqc.trans (Nat.le_of_lt hcR)
    have hcq : c * q ≤ c * c := Nat.mul_le_mul_left c hqc
    have hcc : c * c < R * R := by nlinarith
    have hproductLt : c * q < R ^ 2 := by
      calc
        c * q ≤ c * c := hcq
        _ < R * R := hcc
        _ = R ^ 2 := by ring
    have hproduct : c * q ≤ squareRootEndpoint R := by
      unfold squareRootEndpoint
      omega
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hqPrime.two_le, hqR⟩,
        hqPrime, hrough, hqc, hproduct⟩

/-- Cardinality form of the exact born-prime interval identification. -/
theorem squareRootBornPartnerCount_eq_primeIntervalCount_of_lt_root
    {R c : ℕ} (hcR : c < R) :
    squareRootBornPartnerCount R c =
      squareRootPrimeIntervalCount (canonicalLargestPrimeFactor c) c := by
  unfold squareRootBornPartnerCount squareRootPrimeIntervalCount
  rw [squareRootBornPartnerSet_eq_primeInterval_of_lt_root hcR]

/-- Explicit born parent/child interval difference when the fresh child remains
below `R`.  Roughness identifies the child's largest prime factor with `p`. -/
theorem squareRootBornPartnerCount_sub_child_eq_primeIntervalDifference
    {R p a : ℕ} (hp : p.Prime) (ha : 0 < a)
    (hrough : canonicalLargestPrimeFactor a < p)
    (hchildR : p * a < R) :
    ((squareRootBornPartnerCount R a : ℕ) : ℂ) -
        ((squareRootBornPartnerCount R (p * a) : ℕ) : ℂ) =
      ((squareRootPrimeIntervalCount
          (canonicalLargestPrimeFactor a) a : ℕ) : ℂ) -
        ((squareRootPrimeIntervalCount p (p * a) : ℕ) : ℂ) := by
  have haLe : a ≤ p * a := Nat.le_mul_of_pos_left a hp.pos
  have haR : a < R := lt_of_le_of_lt haLe hchildR
  have hlpfChild : canonicalLargestPrimeFactor (p * a) = p := by
    have h := canonicalLargestPrimeFactor_mul_prime_eq_of_rough ha hp hrough
    simpa [Nat.mul_comm] using h
  rw [squareRootBornPartnerCount_eq_primeIntervalCount_of_lt_root haR,
    squareRootBornPartnerCount_eq_primeIntervalCount_of_lt_root hchildR,
    hlpfChild]

/-- The born interval finite difference attached to one old parent. -/
def squareRootBornPrimeIntervalDifference (p a : ℕ) : ℂ :=
  ((squareRootPrimeIntervalCount
      (canonicalLargestPrimeFactor a) a : ℕ) : ℂ) -
    ((squareRootPrimeIntervalCount p (p * a) : ℕ) : ℂ)

/-- The two response channels are deliberately combined before any case split
or estimate. -/
def squareRootBornPostTailCombinedParentChildDifference
    (R K j p a : ℕ) : ℂ :=
  (((squareRootBornPartnerCount R a : ℕ) : ℂ) -
      ((squareRootBornPartnerCount R (p * a) : ℕ) : ℂ)) +
    (((squareRootBornPostTailHighResponse R K j a : ℕ) : ℂ) -
      ((squareRootBornPostTailHighResponse R K j (p * a) : ℕ) : ℂ))

/-- **Combined born/high trichotomy on one common parent face.**

The middle transition is not discarded or estimated: it remains attached to
the born interval difference.  Beyond `K`, the high term is already the
completed partner mixed fold from #468. -/
theorem squareRootBornPostTailCombinedParentChildDifference_trichotomy
    {R K j p a : ℕ} (hp : p.Prime) (hpR : p ≤ R)
    (hR : 2 ≤ R) (ha : 0 < a)
    (hrough : canonicalLargestPrimeFactor a < p)
    (hchildR : p * a < R) :
    squareRootBornPostTailCombinedParentChildDifference R K j p a =
      if p * a ≤ K then
        squareRootBornPrimeIntervalDifference p a
      else if a ≤ K then
        squareRootBornPrimeIntervalDifference p a +
          squareRootBornPostTailHighTransitionDifference R K j p a
      else
        squareRootBornPrimeIntervalDifference p a +
          (lowPrimeCompletedPartnerMixedFold
            p R (squareRootEndpoint R) a : ℂ) := by
  have hborn :=
    squareRootBornPartnerCount_sub_child_eq_primeIntervalDifference
      hp ha hrough hchildR
  unfold squareRootBornPostTailCombinedParentChildDifference
    squareRootBornPrimeIntervalDifference
  rw [hborn]
  by_cases hchildK : p * a ≤ K
  · rw [if_pos hchildK]
    rw [squareRootBornPostTailHighResponse_sub_child_eq_zero_of_child_le_K
      hp hchildK]
    ring
  · rw [if_neg hchildK]
    by_cases haK : a ≤ K
    · rw [if_pos haK]
      rfl
    · rw [if_neg haK]
      rw [squareRootBornPostTailHighResponse_sub_child_eq_completedPartnerMixedFold
        hp hpR hR ha (by omega)]

/-- Face-specialized form on the actual chronological old cube.  Membership in
`lowPrimeFreshParentFaces (R-1) p` supplies positivity, roughness, and the fact
that the fresh child is still below the root. -/
theorem squareRootBornPostTailCombinedParentChildDifference_face_trichotomy
    {R K j p : ℕ} (hp : p.Prime) (hpR : p ≤ R) (hR : 2 ≤ R)
    {u : Finset ℕ} (hu : u ∈ lowPrimeFreshParentFaces (R - 1) p) :
    squareRootBornPostTailCombinedParentChildDifference
        R K j p (primeFaceProduct u) =
      if p * primeFaceProduct u ≤ K then
        squareRootBornPrimeIntervalDifference p (primeFaceProduct u)
      else if primeFaceProduct u ≤ K then
        squareRootBornPrimeIntervalDifference p (primeFaceProduct u) +
          squareRootBornPostTailHighTransitionDifference
            R K j p (primeFaceProduct u)
      else
        squareRootBornPrimeIntervalDifference p (primeFaceProduct u) +
          (lowPrimeCompletedPartnerMixedFold
            p R (squareRootEndpoint R) (primeFaceProduct u) : ℂ) := by
  rcases mem_lowPrimeFreshParentFaces.mp hu with ⟨huOld, hchild⟩
  have ha : 0 < primeFaceProduct u :=
    primeFaceProduct_pos_of_mem_powerset huOld
  have hrough : canonicalLargestPrimeFactor (primeFaceProduct u) < p :=
    canonicalLargestPrimeFactor_primeFaceProduct_lt_freshPrime hp huOld
  have hchildR : p * primeFaceProduct u < R := by omega
  exact squareRootBornPostTailCombinedParentChildDifference_trichotomy
    hp hpR hR ha hrough hchildR

end RHLean.Proof
