import Mathlib
import RHLean.Analysis.PNTSpacedPrimeFlipClosure
import RHLean.Analysis.SquareRunTopEscapeClassification

open scoped BigOperators

/-!
# The unique fresh-prime owner cube straddles both square-run boundaries

Global first-separation ownership assigns every nonzero square-run covariance
atom to one unique fresh prime `p`.  On a subdoubling run this cube is never a
complete cube contained in the physical window.  The endpoint carrying `p`
strips below the lower square anchor, while adjoining `p` to the other endpoint
overshoots the upper square cutoff.

This is the exact chronology statement needed to distinguish unique atom
ownership from the stronger, false idea that the run decomposes into disjoint
complete four-corner cubes.  Four-corner cancellation is therefore genuinely
nonlocal in square time.
-/

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Proof

/-- In a subdoubling run, adjoining any prime to any physical site reaches or
passes the upper endpoint. -/
theorem prime_mul_runSite_ge_top_of_subdoubling
    {p a b n : ℕ} (hp : p.Prime)
    (hn : n ∈ Finset.Ico (a ^ 2) ((b + 1) ^ 2))
    (hsub : (b + 1) ^ 2 ≤ 2 * a ^ 2) :
    (b + 1) ^ 2 ≤ p * n := by
  have hnLow : a ^ 2 ≤ n := (Finset.mem_Ico.mp hn).1
  have htwo : 2 * a ^ 2 ≤ p * n := Nat.mul_le_mul hp.two_le hnLow
  exact hsub.trans htwo

/-- **Two-sided owner-cube boundary theorem.**

For every nonzero physical pair in a subdoubling run, let `p` be its unique
first differing prime and strip `p` from both endpoints.  In the orientation
where `p` occurred in the first endpoint, that stripped parent lies below the
run while adjoining `p` to the second parent lies above it; and symmetrically in
the other orientation.

Thus the unique owner cube exists, but its complementary corners lie on opposite
sides of the physical square-time window. -/
theorem squareRunFreshPrimeOwner_cube_straddles
    {a b m n : ℕ} (hab : a ≤ b)
    (hm : m ∈ Finset.Ico (a ^ 2) ((b + 1) ^ 2))
    (hn : n ∈ Finset.Ico (a ^ 2) ((b + 1) ^ 2))
    (hmn : m < n)
    (hm0 : realMoebiusStep m ≠ 0)
    (hn0 : realMoebiusStep n ≠ 0)
    (hsub : (b + 1) ^ 2 ≤ 2 * a ^ 2) :
    let p := squarefreePairFreshPrimeOwner m n
    let um := squarefreePrimeFamilyParent p m
    let un := squarefreePrimeFamilyParent p n
    (um < a ^ 2 ∧ (b + 1) ^ 2 ≤ p * un) ∨
      (un < a ^ 2 ∧ (b + 1) ^ 2 ≤ p * um) := by
  let p := squarefreePairFreshPrimeOwner m n
  let um := squarefreePrimeFamilyParent p m
  let un := squarefreePrimeFamilyParent p n
  have hmsq := squarefree_of_realMoebiusStep_ne_zero hm0
  have hnsq := squarefree_of_realMoebiusStep_ne_zero hn0
  have hmpos : 0 < m := by
    by_contra hz
    have hmz : m = 0 := by omega
    subst m
    simp [realMoebiusStep] at hm0
  have hnpos : 0 < n := lt_trans hmpos hmn
  have hp : p.Prime := squarefreePairFreshPrimeOwner_prime hmsq hnsq (by omega)
  rcases squarefreePairFreshPrimeOwner_dvd_xor
      hmsq hnsq (by omega) hmpos hnpos with h | h
  · left
    have hum : um < a ^ 2 := by
      dsimp [um]
      exact squarefreePrimeFamilyParent_lt_runAnchor_of_dvd hp hm h.1 hsub
    have hun : un = n := by
      dsimp [un]
      exact squarefreePrimeFamilyParent_eq_of_not_dvd h.2
    refine ⟨hum, ?_⟩
    rw [hun]
    exact prime_mul_runSite_ge_top_of_subdoubling hp hn hsub
  · right
    have hun : un < a ^ 2 := by
      dsimp [un]
      exact squarefreePrimeFamilyParent_lt_runAnchor_of_dvd hp hn h.1 hsub
    have hum : um = m := by
      dsimp [um]
      exact squarefreePrimeFamilyParent_eq_of_not_dvd h.2
    refine ⟨hun, ?_⟩
    rw [hum]
    exact prime_mul_runSite_ge_top_of_subdoubling hp hm hsub

/-- No unique owner cube of a contributing pair can have all four of its
fresh-parent/mixed corners strictly inside a subdoubling square run. -/
theorem squareRunFreshPrimeOwner_not_complete_internal_cube
    {a b m n : ℕ} (hab : a ≤ b)
    (hm : m ∈ Finset.Ico (a ^ 2) ((b + 1) ^ 2))
    (hn : n ∈ Finset.Ico (a ^ 2) ((b + 1) ^ 2))
    (hmn : m < n)
    (hm0 : realMoebiusStep m ≠ 0)
    (hn0 : realMoebiusStep n ≠ 0)
    (hsub : (b + 1) ^ 2 ≤ 2 * a ^ 2) :
    let p := squarefreePairFreshPrimeOwner m n
    let um := squarefreePrimeFamilyParent p m
    let un := squarefreePrimeFamilyParent p n
    ¬ (um ∈ Finset.Ico (a ^ 2) ((b + 1) ^ 2) ∧
       un ∈ Finset.Ico (a ^ 2) ((b + 1) ^ 2) ∧
       p * um ∈ Finset.Ico (a ^ 2) ((b + 1) ^ 2) ∧
       p * un ∈ Finset.Ico (a ^ 2) ((b + 1) ^ 2)) := by
  intro hall
  have hstraddle := squareRunFreshPrimeOwner_cube_straddles
    hab hm hn hmn hm0 hn0 hsub
  rcases hstraddle with h | h
  · exact (not_lt_of_ge (Finset.mem_Ico.mp hall.1).1) h.1
  · exact (not_lt_of_ge (Finset.mem_Ico.mp hall.2.1).1) h.1

end RHLean.Analysis
