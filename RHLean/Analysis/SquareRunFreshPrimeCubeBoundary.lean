import Mathlib
import RHLean.Analysis.PrimeSieveCollapseIdentity
import RHLean.Analysis.SquarePrefixMertensBridge
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

/-! ## Conditional PNT-spaced prime-flip closure

The exact prime-sieve collapse shows why a bare PNT or prime-gap estimate is not
by itself a Mertens bound: even after the post-root prime counts are controlled,
the signed smooth remainder remains.  The following hypothesis isolates the
stronger chronology proposed here.  It says that PNT-spaced fresh-prime arrivals,
together with complete Euler-generation cancellation, leave at most one
unit-bounded endpoint residual for each reciprocal coordinate below `sqrt x`.

This is intentionally a conditional statement.  The content still to be derived
from the actual owner chronology is precisely this closure representation; once
it is available, the square-root bound is elementary.
-/

/-- **PNT-spaced prime-flip closure hypothesis.**  After every completed Euler
generation has cancelled, `M(x)` is the sum of one unit-bounded residual for
each of the `sqrt x` lower reciprocal coordinates. -/
def PNTSpacedPrimeFlipClosureStatement : Prop :=
  ∀ x : ℕ,
    ∃ residual : Fin (Nat.sqrt x) → ℂ,
      (∀ z, ‖residual z‖ ≤ 1) ∧
      mertensSummatory x = ∑ z, residual z

/-- Under the explicit prime-flip closure hypothesis, the Mertens function obeys
the strong square-root bound pointwise. -/
theorem norm_mertensSummatory_le_sqrt_of_pntSpacedPrimeFlipClosure
    (h : PNTSpacedPrimeFlipClosureStatement) (x : ℕ) :
    ‖mertensSummatory x‖ ≤ (Nat.sqrt x : ℝ) := by
  classical
  rcases h x with ⟨residual, hresidual, hcollapse⟩
  rw [hcollapse]
  calc
    ‖∑ z, residual z‖ ≤
        ∑ z : Fin (Nat.sqrt x), ‖residual z‖ := by
      exact norm_sum_le Finset.univ residual
    _ ≤ ∑ _z : Fin (Nat.sqrt x), (1 : ℝ) := by
      exact Finset.sum_le_sum (fun z _hz => hresidual z)
    _ = (Nat.sqrt x : ℝ) := by simp

/-- The conditional square-root bound is stronger than the repository's
RH-scale squared-energy criterion; the latter holds with constant `C = 1`. -/
theorem mertensEnergyBounded_of_pntSpacedPrimeFlipClosure
    (h : PNTSpacedPrimeFlipClosureStatement) :
    MertensEnergyBoundedStatement := by
  intro ε hε
  refine ⟨1, by norm_num, ?_⟩
  intro x
  have hnorm :=
    norm_mertensSummatory_le_sqrt_of_pntSpacedPrimeFlipClosure h x
  have hnorm0 : 0 ≤ ‖mertensSummatory x‖ := norm_nonneg _
  have hsqrt0 : 0 ≤ (Nat.sqrt x : ℝ) := by positivity
  have hsq :
      ‖mertensSummatory x‖ ^ 2 ≤ (Nat.sqrt x : ℝ) ^ 2 := by
    nlinarith
  have hsqrtNat : (Nat.sqrt x) ^ 2 ≤ x := Nat.sqrt_le' x
  have hsqrtReal : (Nat.sqrt x : ℝ) ^ 2 ≤ (x : ℝ) := by
    exact_mod_cast hsqrtNat
  have hxsucc : (x : ℝ) ≤ ((x + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_succ x
  have hbase : (1 : ℝ) ≤ ((x + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le x))
  have hexp : (1 : ℝ) ≤ 1 + ε := by linarith
  have hbasePow :
      ((x + 1 : ℕ) : ℝ) ≤
        Real.rpow ((x + 1 : ℕ) : ℝ) (1 + ε) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hbase hexp
  calc
    ‖mertensSummatory x‖ ^ 2 ≤ (Nat.sqrt x : ℝ) ^ 2 := hsq
    _ ≤ (x : ℝ) := hsqrtReal
    _ ≤ ((x + 1 : ℕ) : ℝ) := hxsucc
    _ ≤ 1 * Real.rpow ((x + 1 : ℕ) : ℝ) (1 + ε) := by
      simpa using hbasePow

end RHLean.Analysis
