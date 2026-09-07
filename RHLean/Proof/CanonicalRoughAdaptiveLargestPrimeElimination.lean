import Mathlib
import RHLean.Proof.CanonicalRoughAdaptiveCriticalCompression
import RHLean.Proof.ReplacementFibreCofactorWindows

/-!
# Largest-prime elimination in the adaptive critical descent

The adaptive carrier removes only paired child copies.  This file proves the
arithmetic reason a descending prime schedule has no nontrivial squarefree
survivor: a squarefree integer `n > 1` is a legal child exactly when the
coordinate `p = P+(n)` is processed, while no strictly larger prime can remove
`n` or its canonical parent beforehand.

Consequently any schedule whose prefix before `P+(n)` consists only of larger
primes deletes `n` at that coordinate, and later carrier updates cannot bring it
back.  This is an exact carrier statement; no norm or asymptotic estimate is
used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis
open CanonicalRoughPrimeAdditionDescent

attribute [local instance] Classical.propDecidable

/-- A squarefree nontrivial integer is a legal child at its canonical largest
prime whenever both it and its canonical parent are active. -/
theorem squarefree_mem_freshPrimeChildrenOn_canonicalLargestPrimeFactor
    {n : ℕ} {U : Finset ℕ}
    (hsq : Squarefree n) (hn : 1 < n)
    (hnU : n ∈ U) (hcU : canonicalCofactor n ∈ U) :
    n ∈ squareRootCanonicalRoughFreshPrimeChildrenOn
      (canonicalLargestPrimeFactor n) U := by
  let c := canonicalCofactor n
  let p := canonicalLargestPrimeFactor n
  have hp : p.Prime := by
    simpa [p] using canonicalLargestPrimeFactor_prime hn
  have hcpos : 0 < c := by
    have hc1 : 1 ≤ canonicalCofactor n :=
      CanonicalGapAncestryBridge.canonicalCofactor_pos hn
    simpa [c] using hc1
  have hrough : canonicalLargestPrimeFactor c < p := by
    simpa [c, p] using
      canonicalLargestPrimeFactor_canonicalCofactor_lt_of_squarefree hn hsq
  have hprod : c * p = n := by
    simpa [c, p] using canonicalCofactor_mul_largestPrimeFactor hn
  have hparent : c ∈ squareRootCanonicalRoughFreshPrimeParentsOn p U := by
    apply mem_squareRootCanonicalRoughFreshPrimeParentsOn.mpr
    refine ⟨?_, hcpos, hrough, ?_⟩
    · simpa [c] using hcU
    · rw [hprod]
      exact hnU
  unfold squareRootCanonicalRoughFreshPrimeChildrenOn
  exact Finset.mem_image.mpr ⟨c, hparent, hprod⟩

/-- A prime strictly above the canonical largest prime of `n` cannot remove
`n` as one of its child copies. -/
theorem not_mem_freshPrimeChildrenOn_of_largestPrime_lt
    {n p : ℕ} {U : Finset ℕ}
    (hp : p.Prime) (hlt : canonicalLargestPrimeFactor n < p) :
    n ∉ squareRootCanonicalRoughFreshPrimeChildrenOn p U := by
  intro hnChild
  rcases Finset.mem_image.mp hnChild with ⟨c, hcParent, hcn⟩
  rcases mem_squareRootCanonicalRoughFreshPrimeParentsOn.mp hcParent with
    ⟨_hcU, hcpos, hcrough, _hchildU⟩
  have hlpf : canonicalLargestPrimeFactor (c * p) = p :=
    canonicalLargestPrimeFactor_mul_prime_eq_of_rough hcpos hp hcrough
  have heq : canonicalLargestPrimeFactor n = p := by
    rw [← hcn]
    exact hlpf
  rw [heq] at hlt
  exact (lt_irrefl p hlt)

/-- Therefore a state survives one adaptive step at every prime strictly above
its largest prime factor. -/
theorem mem_adaptiveNextCarrier_of_largestPrime_lt
    {n p : ℕ} {U : Finset ℕ}
    (hnU : n ∈ U) (hp : p.Prime)
    (hlt : canonicalLargestPrimeFactor n < p) :
    n ∈ squareRootCanonicalRoughAdaptiveNextCarrier p U := by
  apply Finset.mem_sdiff.mpr
  exact ⟨hnU, not_mem_freshPrimeChildrenOn_of_largestPrime_lt hp hlt⟩

/-- Adaptive updates only remove states; they never create a new carrier
coordinate. -/
theorem squareRootCanonicalRoughAdaptiveNextCarrier_subset
    (p : ℕ) (U : Finset ℕ) :
    squareRootCanonicalRoughAdaptiveNextCarrier p U ⊆ U := by
  intro n hn
  exact (Finset.mem_sdiff.mp hn).1

/-- The whole adaptive run is a subcarrier of its initial carrier. -/
theorem squareRootCanonicalRoughAdaptiveCarrier_subset
    (ps : List ℕ) (U : Finset ℕ) :
    squareRootCanonicalRoughAdaptiveCarrier ps U ⊆ U := by
  induction ps generalizing U with
  | nil => simp [squareRootCanonicalRoughAdaptiveCarrier]
  | cons p ps ih =>
      intro n hn
      have hnNext :
          n ∈ squareRootCanonicalRoughAdaptiveNextCarrier p U :=
        ih (U := squareRootCanonicalRoughAdaptiveNextCarrier p U) hn
      exact squareRootCanonicalRoughAdaptiveNextCarrier_subset p U hnNext

/-- A state absent from the current carrier stays absent under every later
adaptive prime step. -/
theorem not_mem_adaptiveCarrier_of_not_mem
    {n : ℕ} (ps : List ℕ) {U : Finset ℕ}
    (hn : n ∉ U) :
    n ∉ squareRootCanonicalRoughAdaptiveCarrier ps U := by
  intro hfinal
  exact hn (squareRootCanonicalRoughAdaptiveCarrier_subset ps U hfinal)

/-- Membership persists through any prime list all of whose coordinates are
strictly above the state's largest prime factor. -/
theorem mem_adaptiveCarrier_of_all_larger_primes
    {n : ℕ} (ps : List ℕ) {U : Finset ℕ}
    (hnU : n ∈ U)
    (hprime : ∀ p ∈ ps, p.Prime)
    (hlarger : ∀ p ∈ ps, canonicalLargestPrimeFactor n < p) :
    n ∈ squareRootCanonicalRoughAdaptiveCarrier ps U := by
  induction ps generalizing U with
  | nil => simpa [squareRootCanonicalRoughAdaptiveCarrier] using hnU
  | cons p ps ih =>
      have hp : p.Prime := hprime p (by simp)
      have hnp : canonicalLargestPrimeFactor n < p := hlarger p (by simp)
      have hnNext := mem_adaptiveNextCarrier_of_largestPrime_lt hnU hp hnp
      have hprimeTail : ∀ q ∈ ps, q.Prime := by
        intro q hq
        exact hprime q (by simp [hq])
      have hlargerTail : ∀ q ∈ ps, canonicalLargestPrimeFactor n < q := by
        intro q hq
        exact hlarger q (by simp [hq])
      exact ih hnNext hprimeTail hlargerTail

/-- Adaptive carriers compose along list append. -/
theorem squareRootCanonicalRoughAdaptiveCarrier_append
    (ps qs : List ℕ) (U : Finset ℕ) :
    squareRootCanonicalRoughAdaptiveCarrier (ps ++ qs) U =
      squareRootCanonicalRoughAdaptiveCarrier qs
        (squareRootCanonicalRoughAdaptiveCarrier ps U) := by
  induction ps generalizing U with
  | nil => simp [squareRootCanonicalRoughAdaptiveCarrier]
  | cons p ps ih =>
      simp only [List.cons_append, squareRootCanonicalRoughAdaptiveCarrier]
      exact ih (U := squareRootCanonicalRoughAdaptiveNextCarrier p U)

/-- **Largest-prime deletion after any larger-prime prefix.**  A squarefree
state and its canonical parent both survive all strictly larger coordinates;
at `P+(n)` they form a legal parent/child pair and the child `n` is deleted. -/
theorem squarefree_not_mem_adaptiveNext_after_largerPrimePrefix
    {n : ℕ} {U : Finset ℕ} (qs : List ℕ)
    (hsq : Squarefree n) (hn : 1 < n)
    (hnU : n ∈ U) (hcU : canonicalCofactor n ∈ U)
    (hprime : ∀ q ∈ qs, q.Prime)
    (hlarger : ∀ q ∈ qs, canonicalLargestPrimeFactor n < q) :
    n ∉ squareRootCanonicalRoughAdaptiveNextCarrier
      (canonicalLargestPrimeFactor n)
      (squareRootCanonicalRoughAdaptiveCarrier qs U) := by
  let V := squareRootCanonicalRoughAdaptiveCarrier qs U
  have hnV : n ∈ V := by
    dsimp [V]
    exact mem_adaptiveCarrier_of_all_larger_primes qs hnU hprime hlarger
  have hparentRough :
      canonicalLargestPrimeFactor (canonicalCofactor n) <
        canonicalLargestPrimeFactor n :=
    canonicalLargestPrimeFactor_canonicalCofactor_lt_of_squarefree hn hsq
  have hcV : canonicalCofactor n ∈ V := by
    dsimp [V]
    apply mem_adaptiveCarrier_of_all_larger_primes qs hcU hprime
    intro q hq
    exact hparentRough.trans (hlarger q hq)
  have hchild :=
    squarefree_mem_freshPrimeChildrenOn_canonicalLargestPrimeFactor
      hsq hn hnV hcV
  intro hnNext
  exact (Finset.mem_sdiff.mp hnNext).2 hchild

/-- **Permanent elimination in a descending schedule.**  Once a squarefree
state reaches its own largest-prime coordinate after only larger primes, it is
deleted there and no arbitrary tail of later/smaller coordinates can restore
it. -/
theorem squarefree_not_mem_adaptiveCarrier_of_schedule_split
    {n : ℕ} {U : Finset ℕ} (qs rs : List ℕ)
    (hsq : Squarefree n) (hn : 1 < n)
    (hnU : n ∈ U) (hcU : canonicalCofactor n ∈ U)
    (hprime : ∀ q ∈ qs, q.Prime)
    (hlarger : ∀ q ∈ qs, canonicalLargestPrimeFactor n < q) :
    n ∉ squareRootCanonicalRoughAdaptiveCarrier
      (qs ++ canonicalLargestPrimeFactor n :: rs) U := by
  rw [squareRootCanonicalRoughAdaptiveCarrier_append]
  simp only [squareRootCanonicalRoughAdaptiveCarrier]
  apply not_mem_adaptiveCarrier_of_not_mem rs
  exact squarefree_not_mem_adaptiveNext_after_largerPrimePrefix
    qs hsq hn hnU hcU hprime hlarger

end RHLean.Proof
