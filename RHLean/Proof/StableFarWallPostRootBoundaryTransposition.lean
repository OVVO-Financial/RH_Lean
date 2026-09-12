import Mathlib
import RHLean.Proof.StableFarWallAdaptiveFourCornerBridge
import RHLean.Proof.CanonicalRoughCriticalDefectWindows

/-!
# Post-root far-prime boundary transposition

PR #682 proves that a stable-far state contributes no new correction when its
lower owner is processed: the larger far-prime four-corner has already zeroed
both lower-owner coefficients.  The amplitude therefore lives on an earlier
post-root fresh-prime step.

That step is *not* itself a complete sub-root Euler-wheel step.  A fresh prime
`p > R` has zero child response, so its loss boundary is the entire parent
rough-prime partner set and its birth boundary is empty.  Thus the exact bridge
out of the post-root chronology is a transposition from the far fresh-prime
coordinate to the intact parent-partner coordinate.

This file records that transposition before any norm.  In particular, for every
actual stable-far triple `(q,(d,p))`, the physical boundary at the far prime `p`
on the original low cofactor `q*d` is exactly the signed sum over *all* canonical
rough partners of `q*d`; the far prime `p` itself is one literal member of that
partner set.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis
open CanonicalRoughPrimeAdditionDescent

attribute [local instance] Classical.propDecidable

/-- **Post-root loss exhausts the parent partner set.**  Once the fresh prime is
strictly above the root, the fresh child has no rough-prime response at all, so
there is no surviving child partner to remove from the parent set. -/
theorem squareRootCanonicalRoughFreshLossBoundary_eq_partnerSet_of_rootPrime
    {R c p : ℕ} (hR : 2 ≤ R) (hc : 0 < c) (hp : p.Prime)
    (hfresh : canonicalLargestPrimeFactor c < p) (hRp : R < p) :
    squareRootCanonicalRoughFreshLossBoundary R c p =
      squareRootCanonicalRoughPrimePartnerSet R c := by
  unfold squareRootCanonicalRoughFreshLossBoundary
  rw [Nat.mul_comm p c,
    squareRootCanonicalRoughPrimePartnerSet_mul_freshPrime_eq_empty_of_rootPrime
      hR hc hp hfresh hRp]
  simp

/-- **Post-root birth is empty.**  This is the set-level companion of the
post-root zero-child-response theorem. -/
theorem squareRootCanonicalRoughFreshBirthBoundary_eq_empty_of_rootPrime
    {R c p : ℕ} (hR : 2 ≤ R) (hc : 0 < c) (hp : p.Prime)
    (hfresh : canonicalLargestPrimeFactor c < p) (hRp : R < p) :
    squareRootCanonicalRoughFreshBirthBoundary R c p = ∅ := by
  unfold squareRootCanonicalRoughFreshBirthBoundary
  rw [Nat.mul_comm p c,
    squareRootCanonicalRoughPrimePartnerSet_mul_freshPrime_eq_empty_of_rootPrime
      hR hc hp hfresh hRp]
  simp

/-- The unweighted raw child atom itself vanishes at a post-root fresh prime. -/
theorem squareRootCanonicalRoughRawCorrelationSummand_mul_freshPrime_eq_zero_of_rootPrime
    {R c p : ℕ} (hR : 2 ≤ R) (hc : 0 < c) (hp : p.Prime)
    (hfresh : canonicalLargestPrimeFactor c < p) (hRp : R < p) :
    squareRootCanonicalRoughRawCorrelationSummand R (c * p) = 0 := by
  unfold squareRootCanonicalRoughRawCorrelationSummand
  rw [squareRootCanonicalRoughCofactorResponse_eq_primePartnerCount R (c * p) hR,
    squareRootCanonicalRoughPrimePartnerCount_mul_freshPrime_eq_zero_of_rootPrime
      hR hc hp hfresh hRp]
  simp

/-- **Post-root raw boundary = parent raw correlation.**  No magnitude estimate
is involved: loss is the complete parent partner set and birth is empty. -/
theorem squareRootCanonicalRoughFreshPrimeRawBoundary_eq_parentRaw_of_rootPrime
    {R c p : ℕ} (hR : 2 ≤ R) (hc : 0 < c) (hp : p.Prime)
    (hfresh : canonicalLargestPrimeFactor c < p) (hRp : R < p) :
    canonicalMoebiusWeight c *
        (((squareRootCanonicalRoughFreshLossBoundary R c p).card : ℂ) -
          ((squareRootCanonicalRoughFreshBirthBoundary R c p).card : ℂ)) =
      squareRootCanonicalRoughRawCorrelationSummand R c := by
  rw [squareRootCanonicalRoughFreshLossBoundary_eq_partnerSet_of_rootPrime
      hR hc hp hfresh hRp,
    squareRootCanonicalRoughFreshBirthBoundary_eq_empty_of_rootPrime
      hR hc hp hfresh hRp]
  simp only [Finset.card_empty, Nat.cast_zero, sub_zero]
  unfold squareRootCanonicalRoughRawCorrelationSummand
  rw [squareRootCanonicalRoughCofactorResponse_eq_primePartnerCount R c hR,
    squareRootCanonicalRoughPrimePartnerCount_eq_partnerSet_card R c]

/-- The parent raw correlation is literally a signed incidence column over its
canonical rough-prime partners.  This is the finite-Fubini coordinate needed to
transpose a far fresh-prime boundary into a partner-prime column. -/
theorem squareRootCanonicalRoughRawCorrelationSummand_eq_partnerIncidenceSum
    (R c : ℕ) (hR : 2 ≤ R) :
    squareRootCanonicalRoughRawCorrelationSummand R c =
      ∑ _q ∈ squareRootCanonicalRoughPrimePartnerSet R c,
        canonicalMoebiusWeight c := by
  unfold squareRootCanonicalRoughRawCorrelationSummand
  rw [squareRootCanonicalRoughCofactorResponse_eq_primePartnerCount R c hR,
    squareRootCanonicalRoughPrimePartnerCount_eq_partnerSet_card R c]
  simp [mul_comm]

/-- Every actual stable-far triple's far prime is itself a literal partner of
its original low cofactor `q*d`. -/
theorem lowWheelFarPrimeLowCofactorTriple_farPrime_mem_partnerSet
    {R : ℕ} {t : ℕ × (ℕ × ℕ)} (hR : 2 ≤ R)
    (ht : t ∈ lowWheelFarPrimeLowCofactorTriples R) :
    t.2.2 ∈ squareRootCanonicalRoughPrimePartnerSet R (t.1 * t.2.1) := by
  rcases lowWheelFarPrimeLowCofactorTriple_data ht with
    ⟨hqPrime, hqR, hd1, hpPrime, hpR, _hdsq, hdq, hcut⟩
  have hcpos : 0 < t.1 * t.2.1 := Nat.mul_pos hqPrime.pos (by omega)
  have hlpf : canonicalLargestPrimeFactor (t.1 * t.2.1) = t.1 := by
    simpa [Nat.mul_comm] using
      canonicalLargestPrimeFactor_mul_prime_eq_of_rough hd1 hqPrime hdq
  apply (mem_squareRootCanonicalRoughPrimePartnerSet_iff hR hcpos).2
  refine ⟨hpPrime, ?_, ?_, ?_⟩
  · rw [hlpf]
    omega
  · have hpR' : R ≤ t.2.2 := by omega
    have hc1 : 1 ≤ t.1 * t.2.1 := Nat.succ_le_iff.mpr hcpos
    calc
      R ≤ t.2.2 := hpR'
      _ = 1 * t.2.2 := by simp
      _ ≤ (t.1 * t.2.1) * t.2.2 := Nat.mul_le_mul_right t.2.2 hc1
  · simpa [Nat.mul_assoc] using hcut

/-- **Stable-far post-root boundary transposition.**  On every actual stripped
stable-far triple, the complete physical raw boundary generated at its far prime
is exactly the intact signed partner column of the original low cofactor.

This is the exact coordinate change that must precede the canonical Abel-wheel
comparison: the far prime is a post-root *fresh* coordinate, whereas the Abel
shell machinery runs after Fubini in the *partner* coordinate. -/
theorem lowWheelFarPrimeLowCofactorTriple_farPrimeRawBoundary_eq_partnerIncidenceSum
    {R : ℕ} {t : ℕ × (ℕ × ℕ)} (hR : 2 ≤ R)
    (ht : t ∈ lowWheelFarPrimeLowCofactorTriples R) :
    canonicalMoebiusWeight (t.1 * t.2.1) *
        (((squareRootCanonicalRoughFreshLossBoundary
            R (t.1 * t.2.1) t.2.2).card : ℂ) -
          ((squareRootCanonicalRoughFreshBirthBoundary
            R (t.1 * t.2.1) t.2.2).card : ℂ)) =
      ∑ r ∈ squareRootCanonicalRoughPrimePartnerSet R (t.1 * t.2.1),
        canonicalMoebiusWeight (t.1 * t.2.1) := by
  rcases lowWheelFarPrimeLowCofactorTriple_data ht with
    ⟨hqPrime, hqR, hd1, hpPrime, hpR, _hdsq, hdq, _hcut⟩
  have hcpos : 0 < t.1 * t.2.1 := Nat.mul_pos hqPrime.pos (by omega)
  have hlpf : canonicalLargestPrimeFactor (t.1 * t.2.1) = t.1 := by
    simpa [Nat.mul_comm] using
      canonicalLargestPrimeFactor_mul_prime_eq_of_rough hd1 hqPrime hdq
  have hfresh : canonicalLargestPrimeFactor (t.1 * t.2.1) < t.2.2 := by
    rw [hlpf]
    omega
  have hRp : R < t.2.2 := by omega
  calc
    canonicalMoebiusWeight (t.1 * t.2.1) *
        (((squareRootCanonicalRoughFreshLossBoundary
            R (t.1 * t.2.1) t.2.2).card : ℂ) -
          ((squareRootCanonicalRoughFreshBirthBoundary
            R (t.1 * t.2.1) t.2.2).card : ℂ)) =
      squareRootCanonicalRoughRawCorrelationSummand R (t.1 * t.2.1) :=
        squareRootCanonicalRoughFreshPrimeRawBoundary_eq_parentRaw_of_rootPrime
          hR hcpos hpPrime hfresh hRp
    _ = ∑ r ∈ squareRootCanonicalRoughPrimePartnerSet R (t.1 * t.2.1),
          canonicalMoebiusWeight (t.1 * t.2.1) :=
        squareRootCanonicalRoughRawCorrelationSummand_eq_partnerIncidenceSum
          R (t.1 * t.2.1) hR

end RHLean.Proof
