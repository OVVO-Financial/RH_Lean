import Mathlib
import «research.DIRECT_SUM_COUPLED_FRESH_PRIME_RANGE_EXIT»

/-!
# Coupled direct-sum packet: chronological range-exit collapse

A larger prime partner has already acted on the literal descending raw
chronology.  This first layer isolates that coefficient-kill statement before
reassembling the range-exit step.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic
open CanonicalRoughPrimeAdditionDescent

attribute [local instance] Classical.propDecidable

/-- A current cofactor whose response has any larger prime partner has already
had its raw coefficient killed when that larger prime was processed. -/
theorem evolvedRawCoefficient_eq_zero_of_larger_partner_of_completeDescendingPrefix
    {R c p q : ℕ} (qs : List ℕ)
    (hc : 0 < c) (hp : p.Prime) (hq : q.Prime)
    (hrough : canonicalLargestPrimeFactor c < p)
    (hpq : p < q)
    (hcqUpper : c * q ≤ squareRootEndpoint R)
    (hcomplete : SquareRootCanonicalRoughCompleteDescendingPrefix R p qs) :
    squareRootCanonicalRoughAdaptiveRawCoefficient qs
        (Finset.Icc 1 (squareRootEndpoint R))
        (fun _ => (1 : ℂ)) c = 0 := by
  have hqUpper : q ≤ squareRootEndpoint R := by
    have hq_le_cq : q ≤ c * q := by
      simpa [Nat.mul_comm] using Nat.le_mul_of_pos_right q hc
    exact hq_le_cq.trans hcqUpper
  rcases hcomplete.2 q hq hpq hqUpper with
    ⟨pre, post, hsplit, hprePrime, hpreLarger⟩
  let U0 : Finset ℕ := Finset.Icc 1 (squareRootEndpoint R)
  let V : Finset ℕ := squareRootCanonicalRoughAdaptiveCarrier pre U0
  have hroughQ : canonicalLargestPrimeFactor c < q := hrough.trans hpq
  have hc_le_cq : c ≤ c * q := by
    simpa [Nat.mul_comm] using Nat.le_mul_of_pos_right c hq.pos
  have hcU0 : c ∈ U0 := by
    apply Finset.mem_Icc.mpr
    exact ⟨by omega, hc_le_cq.trans hcqUpper⟩
  have hcqPos : 0 < c * q := Nat.mul_pos hc hq.pos
  have hcqU0 : c * q ∈ U0 := by
    apply Finset.mem_Icc.mpr
    exact ⟨Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hcqPos), hcqUpper⟩
  have hlpfCQ : canonicalLargestPrimeFactor (c * q) = q :=
    canonicalLargestPrimeFactor_mul_prime_eq_of_rough hc hq hroughQ
  have hcV : c ∈ V := by
    dsimp [V]
    apply mem_adaptiveCarrier_of_all_larger_primes pre hcU0 hprePrime
    intro r hr
    exact hroughQ.trans (hpreLarger r hr)
  have hcqV : c * q ∈ V := by
    dsimp [V]
    apply mem_adaptiveCarrier_of_all_larger_primes pre hcqU0 hprePrime
    intro r hr
    rw [hlpfCQ]
    exact hpreLarger r hr
  have hcParent :
      c ∈ squareRootCanonicalRoughFreshPrimeParentsOn q V := by
    apply mem_squareRootCanonicalRoughFreshPrimeParentsOn.mpr
    exact ⟨hcV, hc, hroughQ, hcqV⟩
  rw [hsplit]
  exact squareRootCanonicalRoughAdaptiveRawCoefficient_eq_zero_of_parent_at_split
    pre post U0 (fun _ => (1 : ℂ)) hcParent

end RHLean.Proof
