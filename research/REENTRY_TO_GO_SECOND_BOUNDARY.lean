import Mathlib
import RHLean.Proof.SquareRootLowPrimeResponseReentryBirthWitness
import RHLean.Proof.SquareRootLowPrimeGoTwoBoundaryShell
import RHLean.Proof.SquareRootLowPrimeGoFullFacePartner

/-!
# Response re-entry routes canonically into the Go two-boundary shell

This file formalizes the arithmetic bridge exposed by the finite X=210 model.

A non-born processed seat can survive a first-owner fallout only through the
inherited response tail. If it later re-enters at a larger scheduled owner,
SquareRootLowPrimeResponseReentryBirthWitness produces a strictly larger newly
born prime. Read that newborn prime as the Go outer owner, the later scheduled
prime as the Go smaller owner, and retain the original cofactor as the Go
parent.

The birth witness is then exactly a member of the full Go birth boundary.
The existing two-boundary theorem splits that parent into:

* a physically completed second-contact terminal parent; or
* a genuine SecondBoundaryDefectParents occurrence.

The latter is already consumed by the full-face transport mate theorem, so this
bridge introduces no new estimate and never sends a completed second contact
(such as the X=210 example) into the hard carrier.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- A born re-entry witness is literally a full Go birth-boundary parent. -/
theorem squareRootLowPrimeReentryBirthBoundary_mem_goFullBirthBoundary
    {R p q c t : ℕ}
    (hc : 0 < c)
    (_hp : p.Prime) (hq : q.Prime)
    (hrough : canonicalLargestPrimeFactor c < p)
    (hpq : p < q)
    (hsq : Squarefree c)
    (htBirth : t ∈ squareRootBornPartnerBirthBoundary R c (q * c)) :
    c ∈ squareRootLowPrimeGoFullBirthBoundaryParents t q := by
  rcases mem_squareRootBornPartnerBirthBoundary.mp htBirth with
    ⟨htBorn, hct⟩
  rcases Finset.mem_filter.mp htBorn with
    ⟨_htRange, _htPrime, _hroughChild, htqc, _hprod⟩
  apply mem_squareRootLowPrimeGoFullBirthBoundaryParents.mpr
  refine ⟨by omega, ?_, hsq, hrough.trans hpq, ?_⟩
  · omega
  · apply (Nat.div_lt_iff_lt_mul hq.pos).2
    have htqc' : t ≤ c * q := by
      simpa [Nat.mul_comm] using htqc
    omega

/-- Every re-entry birth witness has exactly the two physical Go outcomes:
second contact already completed, or a genuine second-boundary defect. -/
theorem squareRootLowPrimeReentryBirthBoundary_goTerminal_or_secondBoundary
    {R X p q c t : ℕ}
    (hc : 0 < c)
    (hp : p.Prime) (hq : q.Prime)
    (hrough : canonicalLargestPrimeFactor c < p)
    (hpq : p < q)
    (hsq : Squarefree c)
    (htBirth : t ∈ squareRootBornPartnerBirthBoundary R c (q * c)) :
    c ∈ squareRootLowPrimeGoSmallerOwnerBirthBoundaryParents
          t (X / (t * t)) q ∨
      c ∈ squareRootLowPrimeGoSecondBoundaryDefectParents t X q := by
  have hfull :
      c ∈ squareRootLowPrimeGoFullBirthBoundaryParents t q :=
    squareRootLowPrimeReentryBirthBoundary_mem_goFullBirthBoundary
      hc hp hq hrough hpq hsq htBirth
  have hsplit :=
    squareRootLowPrimeGoFullBirthBoundaryParents_eq_terminal_union_defect
      t X q
  rw [hsplit] at hfull
  exact Finset.mem_union.mp hfull

/-- Dynamic processed-seat to Go-shell bridge. -/
theorem squareRootLowPrimeNonBornFalloutReentry_goTerminal_or_secondBoundary
    {R K j U p q c s : ℕ}
    (hR : 1 ≤ R) (hc : 0 < c)
    (hsq : Squarefree c)
    (hp : p.Prime) (hq : q.Prime)
    (hrough : canonicalLargestPrimeFactor c < p) (hpq : p < q)
    (hpU : p ≤ U) (hUR : U ≤ squareRootBornPostTailLowPrimeCutoff R)
    (hs : s < squareRootLowPrimeCombinedFreshResponse R K j c)
    (hnb : ¬ s < squareRootBornPartnerCount R c)
    (hfall : some (c, s) ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff
      (squareRootLowPrimeProcessedSeatCarrier R K j U) p)
    (hqAlive : s < squareRootLowPrimeCombinedFreshResponse R K j (q * c)) :
    ∃ t,
      t.Prime ∧ q < t ∧ p * c < t ∧
        (c ∈ squareRootLowPrimeGoSmallerOwnerBirthBoundaryParents
              t (squareRootEndpoint R / (t * t)) q ∨
          c ∈ squareRootLowPrimeGoSecondBoundaryDefectParents
              t (squareRootEndpoint R) q) := by
  obtain ⟨t, htBirth, hqt, hpct⟩ :=
    squareRootLowPrimeNonBornFalloutReentry_birthWitness
      hR hc hp hq hrough hpq hpU hUR hs hnb hfall hqAlive
  have htBorn := (mem_squareRootBornPartnerBirthBoundary.mp htBirth).1
  have htPrime : t.Prime := (Finset.mem_filter.mp htBorn).2.1
  have hsplit :=
    squareRootLowPrimeReentryBirthBoundary_goTerminal_or_secondBoundary
      (X := squareRootEndpoint R)
      hc hp hq hrough hpq hsq htBirth
  exact ⟨t, htPrime, hqt, hpct, hsplit⟩

/-- The hard branch is already consumed pointwise by the full-face Go mate. -/
theorem squareRootLowPrimeSecondBoundaryDefect_fullFace_cancel
    {R t q c : ℕ}
    (hR : 2 ≤ R)
    (ht : t.Prime) (hq : q.Prime) (hqt : q < t)
    (hcube : t ^ 3 ≤ squareRootEndpoint R)
    (hcDefect : c ∈ squareRootLowPrimeGoSecondBoundaryDefectParents
      t (squareRootEndpoint R) q) :
    lowWheelFullTaggedPhysicalWeight
        (squareRootLowPrimeGoSecondBoundaryFullFaceSource q t c) +
      lowWheelFullTaggedPhysicalWeight
        (lowWheelFullFaceQuotientMate R
          (squareRootLowPrimeGoSecondBoundaryFullFaceSource q t c)) = 0 := by
  exact squareRootLowPrimeGoSecondBoundaryFullFaceSource_mate_cancel
    hR ht hq hqt hcube hcDefect

end RHLean.Proof
