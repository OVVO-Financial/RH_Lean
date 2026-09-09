import Mathlib
import RHLean.Proof.LowWheelLeastLargestStableTransfer

/-!
# Geometry of the largest-prime stable defect

The least/largest Othello transfer identifies the canonical downcross ledger
with the largest-prime stable defect ledger.  This module does not estimate that
ledger: by `LowWheelLargestDefectSeamEquivalence` such an estimate is the
terminal RH-strength seam itself.

Instead we classify its pointwise carrier exactly.  A largest-prime defect can
only occur in the insertion direction.  If `q = P⁺(c*k)` is the largest prime
factor of the invariant cofactor/quotient product, then `q` is prime, `q ∤ c`,
`q ∣ k`, and the failed insertion is precisely the quotient root-downcross

`P(t) * (k / q) ≤ R`.

No norm, cardinality bound, density input, or asymptotic estimate is used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- If an active fixed-prime cofactor/quotient toggle still satisfies the
physical carrier inequalities, then it belongs to the actual finite physical
state set.  This is the fixed-prime analogue of the canonical-mate closure
lemma, and is used below in both removal and insertion directions. -/
private theorem lowWheelCofactorQuotientToggleAt_mem_physical_of_carrier
    {R p : ℕ} {t : Finset ℕ} {x : LowWheelCofactorQuotientState}
    (hp : p.Prime)
    (hx : x ∈ lowWheelCanonicalPhysicalStateSet R t)
    (hactive : p ∣ x.1 ∨ p ∣ x.2)
    (hmate : LowWheelTransportPairCarrier R t
      (lowWheelCofactorQuotientToggleAt p x)) :
    lowWheelCofactorQuotientToggleAt p x ∈
      lowWheelCanonicalPhysicalStateSet R t := by
  rcases x with ⟨c, k⟩
  have hsq : Squarefree c :=
    lowWheelCanonicalPhysicalStateSet_squarefree (c, k) hx
  have hsquare :
      Squarefree (lowWheelCofactorQuotientToggleAt p (c, k)).1 := by
    by_cases hpc : p ∣ c
    · have hd : c / p ∣ c :=
        ⟨p, (Nat.div_mul_cancel hpc).symm⟩
      have hsqd : Squarefree (c / p) := hsq.squarefree_of_dvd hd
      unfold lowWheelCofactorQuotientToggleAt
      rw [if_pos hpc]
      exact hsqd
    · have hpk : p ∣ k := hactive.resolve_left hpc
      have hmuC : μ c ≠ 0 :=
        ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hsq
      have hmu := moebius_prime_mul hp hpc
      have hmuNe : μ (p * c) ≠ 0 := by
        rw [hmu]
        exact neg_ne_zero.mpr hmuC
      have hsqp : Squarefree (p * c) :=
        ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmuNe
      unfold lowWheelCofactorQuotientToggleAt
      rw [if_neg hpc, if_pos hpk]
      simpa [Nat.mul_comm] using hsqp
  have hrange := lowWheelTransportPairCarrier_mem_ranges hmate
  apply mem_lowWheelCanonicalPhysicalStateSet.mpr
  exact ⟨hrange.1, hrange.2, hsquare, hmate⟩

/-- **Exact largest-prime defect geometry.**

A state stable only because its largest-prime raw mate leaves the physical
carrier must be an insertion state.  Writing `q = P⁺(c*k)`, removal from the
cofactor would always preserve the carrier, so `q ∤ c`; activity then forces
`q ∣ k`.  The square-endpoint one-sided insertion theorem leaves only the
quotient root-downcross `P(t) * (k/q) ≤ R`. -/
theorem lowWheelLargestDefect_geometry
    {R : ℕ} {t : Finset ℕ} {x : LowWheelCofactorQuotientState}
    (ht : t ∈ (primesUpTo R).powerset)
    (hx : x ∈ lowWheelLargestDefectPart R t) :
    let q := lowWheelLargestCofactorQuotientPivot x
    q.Prime ∧
      ¬ q ∣ x.1 ∧
      q ∣ x.2 ∧
      primeFaceProduct t * (x.2 / q) ≤ R := by
  rcases x with ⟨c, k⟩
  dsimp
  have hdata := Finset.mem_filter.mp hx
  have hxF : (c, k) ∈ lowWheelCanonicalPhysicalStateSet R t := hdata.1
  have hprod : c * k ≠ 1 := hdata.2.1
  have hnotMate :
      lowWheelLargestCofactorQuotientToggle (c, k) ∉
        lowWheelCanonicalPhysicalStateSet R t := hdata.2.2
  have hqPrime :
      (lowWheelLargestCofactorQuotientPivot (c, k)).Prime :=
    lowWheelLargestCofactorQuotientPivot_prime ht hxF hprod
  have hactive :
      lowWheelLargestCofactorQuotientPivot (c, k) ∣ c ∨
        lowWheelLargestCofactorQuotientPivot (c, k) ∣ k :=
    lowWheelLargestCofactorQuotientPivot_active ht hxF hprod
  have hcarrier : LowWheelTransportPairCarrier R t (c, k) :=
    (mem_lowWheelCanonicalPhysicalStateSet.mp hxF).2.2.2
  have hnotC : ¬ lowWheelLargestCofactorQuotientPivot (c, k) ∣ c := by
    intro hqc
    apply hnotMate
    unfold lowWheelLargestCofactorQuotientToggle
    exact lowWheelCofactorQuotientToggleAt_mem_physical_of_carrier
      hqPrime hxF hactive
      (lowWheelCofactorQuotientToggleAt_preserves_of_dvd_cofactor
        hqPrime hcarrier hqc)
  have hqK : lowWheelLargestCofactorQuotientPivot (c, k) ∣ k :=
    hactive.resolve_left hnotC
  refine ⟨hqPrime, hnotC, hqK, ?_⟩
  rcases lowWheelCofactorQuotientToggleAt_preserves_or_downcross_of_dvd_quotient
      hqPrime hcarrier hnotC hqK with hmate | hdown
  · exfalso
    apply hnotMate
    unfold lowWheelLargestCofactorQuotientToggle
    exact lowWheelCofactorQuotientToggleAt_mem_physical_of_carrier
      hqPrime hxF hactive hmate
  · exact hdown

end RHLean.Proof
