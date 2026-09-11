import Mathlib
import RHLean.Analysis.OutsidePrimeLeastSquareBlocker

/-!
# Finite maximal-wheel blocker for generic least-square owners

The least-owner super-orbit for `q` contains the selected prime set, every prime
strictly below `q`, and `q` itself.  This makes the growing wheel useful as a
geometric blocker: once the product of the reserved small squares, the selected
squares and `q^2` exceeds one square block, `q` cannot occur in the complete
least-owner interior.
-/

open scoped BigOperators

noncomputable section

namespace RHLean.Analysis

/-- The small prime-square coordinates reserved outside the generic selected
wheel. -/
def outsidePrimeReservedBlockerPrimes : Finset ℕ := {2, 3, 5, 7}

@[simp] theorem outsidePrimeReservedBlockerPrimes_prod_sq :
    (∏ p ∈ outsidePrimeReservedBlockerPrimes, p ^ 2) = 210 ^ 2 := by
  native_decide

/-- A selected generic wheel contains only primes at least `11`. -/
def IsSelectedGenericBlockerWheel (P : Finset ℕ) : Prop :=
  ∀ p ∈ P, p.Prime ∧ 11 ≤ p

/-- Reserved primes are all decided before any generic owner. -/
theorem outsidePrimeReservedBlockerPrimes_subset_earlier
    {q : ℕ} (hq : 11 ≤ q) :
    outsidePrimeReservedBlockerPrimes ⊆ outsidePrimeEarlierPrimes q := by
  intro p hp
  simp [outsidePrimeReservedBlockerPrimes] at hp
  rcases hp with rfl | rfl | rfl | rfl
  all_goals simp [outsidePrimeEarlierPrimes] <;> omega

/-- A finite seed whose square-product is the reserved `210^2` factor, the
selected generic wheel, and the current outside owner. -/
def outsidePrimeBlockerSeed (P : Finset ℕ) (q : ℕ) : Finset ℕ :=
  insert q (outsidePrimeReservedBlockerPrimes ∪ P)

/-- The blocker seed is contained in the actual least-owner super-prime set. -/
theorem outsidePrimeBlockerSeed_subset_super
    {P : Finset ℕ} {q : ℕ} (hq : 11 ≤ q) :
    outsidePrimeBlockerSeed P q ⊆ outsidePrimeLeastSuperPrimeSet P q := by
  intro p hp
  rw [outsidePrimeBlockerSeed, Finset.mem_insert] at hp
  unfold outsidePrimeLeastSuperPrimeSet outsidePrimeLeastStagePrimes
  rcases hp with rfl | hp
  · exact Finset.mem_insert_self q _
  · rw [Finset.mem_union] at hp
    apply Finset.mem_insert_of_mem
    rcases hp with hpSmall | hpP
    · apply Finset.mem_union_right
      exact outsidePrimeReservedBlockerPrimes_subset_earlier hq hpSmall
    · exact Finset.mem_union_left _ hpP

/-- Every coordinate in a least-owner super-prime set is prime, provided the
selected wheel and the owner are prime. -/
theorem outsidePrimeLeastSuperPrimeSet_prime
    {P : Finset ℕ} {q r : ℕ}
    (hP : IsSelectedGenericBlockerWheel P) (hq : q.Prime)
    (hr : r ∈ outsidePrimeLeastSuperPrimeSet P q) : r.Prime := by
  unfold outsidePrimeLeastSuperPrimeSet outsidePrimeLeastStagePrimes at hr
  rcases Finset.mem_insert.mp hr with hrq | hr
  · simpa [hrq] using hq
  · rcases Finset.mem_union.mp hr with hrP | hrEarlier
    · exact (hP r hrP).1
    · exact (Finset.mem_filter.mp hrEarlier).2

/-- The blocker seed has exactly the expected square product. -/
theorem outsidePrimeBlockerSeed_prod_sq
    {P : Finset ℕ} {q : ℕ}
    (hP : IsSelectedGenericBlockerWheel P)
    (hq11 : 11 ≤ q) (hqP : q ∉ P) :
    (∏ p ∈ outsidePrimeBlockerSeed P q, p ^ 2) =
      210 ^ 2 * (∏ p ∈ P, p ^ 2) * q ^ 2 := by
  have hdis : Disjoint outsidePrimeReservedBlockerPrimes P := by
    apply Finset.disjoint_left.mpr
    intro p hpSmall hpP
    have hp11 := (hP p hpP).2
    simp [outsidePrimeReservedBlockerPrimes] at hpSmall
    omega
  have hqSmall : q ∉ outsidePrimeReservedBlockerPrimes := by
    simp [outsidePrimeReservedBlockerPrimes]
    omega
  have hqUnion : q ∉ outsidePrimeReservedBlockerPrimes ∪ P := by
    simp [hqSmall, hqP]
  unfold outsidePrimeBlockerSeed
  rw [Finset.prod_insert hqUnion, Finset.prod_union hdis]
  rw [outsidePrimeReservedBlockerPrimes_prod_sq]
  ring

/-- **Exact period lower bound.**  The genuine least-owner super-orbit period
contains the reserved small-prime squares, every selected generic square, and
`q^2`. -/
theorem outsidePrimeLeastSuperPeriod_ge_blocker
    {P : Finset ℕ} {q : ℕ}
    (hP : IsSelectedGenericBlockerWheel P)
    (hq : q.Prime) (hq11 : 11 ≤ q) (hqP : q ∉ P) :
    210 ^ 2 * (∏ p ∈ P, p ^ 2) * q ^ 2 ≤
      finitePrimeCRTPeriod (outsidePrimeLeastSuperPrimeSet P q) := by
  have hsub := outsidePrimeBlockerSeed_subset_super (P := P) hq11
  have hprod :
      (∏ p ∈ outsidePrimeBlockerSeed P q, p ^ 2) ≤
        ∏ p ∈ outsidePrimeLeastSuperPrimeSet P q, p ^ 2 := by
    exact Finset.prod_le_prod_of_subset_of_one_le' hsub (by
      intro p hpSuper _hpSeed
      have hpPrime := outsidePrimeLeastSuperPrimeSet_prime hP hq hpSuper
      nlinarith [hpPrime.two_le])
  rw [outsidePrimeBlockerSeed_prod_sq hP hq11 hqP] at hprod
  unfold finitePrimeCRTPeriod
  exact hprod.trans (le_max_right _ _)

/-- **Generic complete-owner blocker.**  Any generic owner outside the selected
wheel whose reserved/selected/owner square product exceeds the square block is
forced out of the complete interior. -/
theorem outsidePrimeLeastComplete_no_generic_owner_of_blocker
    {P : Finset ℕ} {R q k : ℕ}
    (hP : IsSelectedGenericBlockerWheel P)
    (hq : q.Prime) (hq11 : 11 ≤ q) (hqP : q ∉ P)
    (hlarge : 2 * R + 2 <
      210 ^ 2 * (∏ p ∈ P, p ^ 2) * q ^ 2)
    (hk : k ∈ squareBlockOutsidePrimeLeastCompleteCells P R) :
    physicalLeastOddSquarePrime k ≠ some q := by
  apply outsidePrimeLeastComplete_no_owner_of_period_gt
  exact hlarge.trans_le
    (outsidePrimeLeastSuperPeriod_ge_blocker hP hq hq11 hqP)
  exact hk

end RHLean.Analysis
