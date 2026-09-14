import Mathlib
import «research.DIRECT_SUM_FRESH_PRIME_STOKES_PRE_SQUARE»

/-!
# Canonical complete descending prime chronology

The adaptive/fresh-prime normal forms are stated for any complete descending
prime schedule.  This file constructs the canonical one: all primes up to the
square endpoint, sorted in descending order.  Thus the chronological identities
require no external schedule witness.

This is finite list bookkeeping only.  No norm or analytic estimate is used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- All primes that can act below the square endpoint, in descending order. -/
def squareRootCanonicalRoughDescendingPrimeSchedule (R : ℕ) : List ℕ :=
  (primesUpTo (squareRootEndpoint R)).sort (fun a b : ℕ => a ≥ b)

private theorem exists_split_of_mem {a : ℕ} {l : List ℕ} (ha : a ∈ l) :
    ∃ pre post : List ℕ, l = pre ++ a :: post := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact ⟨[], l, rfl⟩
      · rcases ih ha with ⟨pre, post, hsplit⟩
        refine ⟨b :: pre, post, ?_⟩
        simp [hsplit]

/-- In a duplicate-free list sorted by `≥`, every element before the marked
current coordinate is strictly larger than it. -/
private theorem sorted_ge_nodup_prefix_before_current
    {pre post : List ℕ} {q : ℕ}
    (hsorted : List.Sorted (fun a b : ℕ => a ≥ b) (pre ++ q :: post))
    (hnodup : (pre ++ q :: post).Nodup) :
    ∀ r ∈ pre, q < r := by
  have hge := (List.pairwise_append.mp hsorted).2.2
  have hne := (List.pairwise_append.mp hnodup).2.2
  intro r hr
  have hqr : q ≤ r := hge r hr q (by simp)
  have hrq : r ≠ q := hne r hr q (by simp)
  omega

/-- The sorted prime list satisfies the repository's exact complete-descending
schedule predicate. -/
theorem squareRootCanonicalRoughDescendingPrimeSchedule_complete
    (R : ℕ) :
    SquareRootCanonicalRoughCompleteDescendingSchedule R
      (squareRootCanonicalRoughDescendingPrimeSchedule R) := by
  let S := primesUpTo (squareRootEndpoint R)
  let ps := S.sort (fun a b : ℕ => a ≥ b)
  change SquareRootCanonicalRoughCompleteDescendingSchedule R ps
  have hsorted : List.Sorted (fun a b : ℕ => a ≥ b) ps := by
    dsimp [ps]
    exact Finset.sort_sorted (· ≥ ·) _
  have hnodup : ps.Nodup := by
    dsimp [ps]
    exact Finset.sort_nodup _ _
  constructor
  · intro p hp
    have hpS : p ∈ S := by
      dsimp [ps] at hp
      exact (Finset.mem_sort (fun a b : ℕ => a ≥ b)).mp hp
    dsimp [S] at hpS
    exact prime_of_mem_primesUpTo hpS
  · intro q hq hqUpper
    have hqS : q ∈ S := by
      dsimp [S]
      exact mem_primesUpTo_of_prime_le hq hqUpper
    have hqps : q ∈ ps := by
      dsimp [ps]
      exact (Finset.mem_sort (fun a b : ℕ => a ≥ b)).2 hqS
    rcases exists_split_of_mem hqps with ⟨pre, post, hsplit⟩
    refine ⟨pre, post, hsplit, ?_, ?_⟩
    · intro r hr
      apply prime_of_mem_primesUpTo
      have hrps : r ∈ ps := by
        rw [hsplit]
        simp [hr]
      have hrS : r ∈ S := by
        dsimp [ps] at hrps
        exact (Finset.mem_sort (fun a b : ℕ => a ≥ b)).mp hrps
      simpa [S] using hrS
    · intro r hr
      rw [hsplit] at hsorted hnodup
      exact sorted_ge_nodup_prefix_before_current hsorted hnodup r hr

/-- The fresh-prime packet normal form is unconditional when evaluated on the
canonical descending schedule. -/
theorem canonicalFreshPrimePacket_eq_roughCorrelation
    (R : ℕ) (hR : 56 ≤ R) :
    directSumCoupledFreshPrimePacket R
        (squareRootCanonicalRoughDescendingPrimeSchedule R) =
      squareRootCanonicalRoughCorrelation R := by
  exact directSumCoupledFreshPrimePacket_eq_roughCorrelation_of_completeSchedule
    R hR (squareRootCanonicalRoughDescendingPrimeSchedule R)
    (squareRootCanonicalRoughDescendingPrimeSchedule_complete R)

/-- **Unconditional canonical pre-square Stokes normal form.** -/
theorem canonicalFreshPrimeScaledReciprocalDropLedger_eq_roughCorrelation
    (R : ℕ) (hR : 56 ≤ R) :
    directSumFreshPrimeScaledReciprocalDropLedger R []
        (squareRootCanonicalRoughDescendingPrimeSchedule R) =
      squareRootCanonicalRoughCorrelation R := by
  exact directSumFreshPrimeScaledReciprocalDropLedger_eq_roughCorrelation
    R hR (squareRootCanonicalRoughDescendingPrimeSchedule R)
    (squareRootCanonicalRoughDescendingPrimeSchedule_complete R)

end RHLean.Proof
