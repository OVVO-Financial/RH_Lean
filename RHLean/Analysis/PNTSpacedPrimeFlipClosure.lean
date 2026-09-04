import Mathlib
import RHLean.Analysis.PrimeSieveCollapseIdentity
import RHLean.Analysis.SquarePrefixMertensBridge

/-!
# Conditional PNT-spaced prime-flip closure

This file deliberately separates two logically different inputs.

The repository already proves that every fresh post-root prime reverses the
completed lower Mobius family, and that the full post-root contribution is a
reciprocal-quotient sum of lower Mertens values weighted by exact prime counts.
A PNT spacing model controls the chronology of those fresh-prime arrivals, but
spacing alone does not prove a Mertens bound: the exact collapse still contains
the signed smooth remainder.

The hypothesis below therefore records the additional chronological closure that
would be needed for the proposed mechanism to finish: after all completed Euler
generations have cancelled, the endpoint residual consists of at most one
unit-bounded signed state for each lower reciprocal coordinate below `sqrt x`.
We index those possible states by `Fin (sqrt x)`, so the cardinality budget is
literally `sqrt x`.

Under that explicit hypothesis the strong square-root Mertens bound is immediate,
and hence so is `MertensEnergyBoundedStatement`.  Nothing in this file claims
that ordinary PNT, or even a prime-gap upper bound by itself, proves the closure
hypothesis.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

/-- **PNT-spaced prime-flip closure hypothesis.**

At every endpoint `x`, after the prime-by-prime Euler flips have completed all
finished generations, the remaining Mertens mass can be represented by one
unit-bounded complex residual for each of the `sqrt x` lower reciprocal
coordinates.

This is the exact extra statement needed to turn prime-spacing chronology into a
square-root bound.  It is intentionally stronger than ordinary PNT or a bare
prime-gap estimate. -/
def PNTSpacedPrimeFlipClosureStatement : Prop :=
  ∀ x : ℕ,
    ∃ residual : Fin (Nat.sqrt x) → ℂ,
      (∀ z, ‖residual z‖ ≤ 1) ∧
      mertensSummatory x = ∑ z, residual z

/-- One endpoint satisfying the prime-flip closure has the strong square-root
Mertens bound.  The proof is only the triangle inequality plus the exact number
`sqrt x` of possible unfinished reciprocal channels. -/
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

/-- The pointwise square-root closure is stronger than the repository's RH-scale
squared-energy criterion.  In fact the criterion holds with constant `C = 1`
for every positive epsilon. -/
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
