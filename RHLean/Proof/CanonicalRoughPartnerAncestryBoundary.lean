import Mathlib
import RHLean.Proof.TerminalMertensReduction

/-!
# Canonical rough-partner ancestry boundary telescoping

The fresh-prime boundary law is local: one ancestry edge replaces the difference
of two positive rough-partner capacities by a loss boundary minus a birth
boundary.  This file records the first genuinely global consequence along a
single ancestry chain.

For an arbitrary multiplicative chain, the signed loss-minus-birth boundary
mass telescopes exactly to the endpoint partner capacities.  Once every child
in the segment has reached the square-root cutoff, the birth boundary on every
edge is empty, so the *positive* loss-boundary mass itself telescopes exactly.

Thus depth creates no multiplicity in the post-root regime: along one branch,
each unit of loss can be charged to endpoint capacity with constant one.  Any
remaining global multiplicity issue must come from branching/recombination
between ancestry chains, not from repeated loss along a single chain.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis

private theorem complex_sum_range_forwardDifference
    (f : ℕ → ℂ) (n : ℕ) :
    (∑ i in Finset.range n, (f i - f (i + 1))) = f 0 - f n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- Along any multiplicative ancestry chain, the complete signed finite
boundary `Loss - Birth` telescopes to the difference of endpoint rough-partner
capacities.  No root-crossing or primality hypothesis is needed for this purely
set-theoretic aggregation of the exact one-edge law. -/
theorem squareRootCanonicalRoughFreshBoundary_chain_telescope
    {R n : ℕ} (c p : ℕ → ℕ)
    (hstep : ∀ i, i < n → c (i + 1) = p i * c i) :
    (∑ i in Finset.range n,
        (((squareRootCanonicalRoughFreshLossBoundary R (c i) (p i)).card : ℂ) -
          ((squareRootCanonicalRoughFreshBirthBoundary R (c i) (p i)).card : ℂ))) =
      squareRootCanonicalRoughPrimePartnerCount R (c 0) -
        squareRootCanonicalRoughPrimePartnerCount R (c n) := by
  calc
    (∑ i in Finset.range n,
        (((squareRootCanonicalRoughFreshLossBoundary R (c i) (p i)).card : ℂ) -
          ((squareRootCanonicalRoughFreshBirthBoundary R (c i) (p i)).card : ℂ))) =
      ∑ i in Finset.range n,
        (squareRootCanonicalRoughPrimePartnerCount R (c i) -
          squareRootCanonicalRoughPrimePartnerCount R (c (i + 1))) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hin : i < n := Finset.mem_range.mp hi
        have hedge :=
          squareRootCanonicalRoughPrimePartnerCount_sub_freshChild_eq_loss_sub_birth
            (R := R) (c := c i) (p := p i)
        rw [← hstep i hin] at hedge
        exact hedge.symm
    _ = squareRootCanonicalRoughPrimePartnerCount R (c 0) -
        squareRootCanonicalRoughPrimePartnerCount R (c n) := by
      simpa using complex_sum_range_forwardDifference
        (fun i => squareRootCanonicalRoughPrimePartnerCount R (c i)) n

/-- On a chain segment whose fresh-prime children have all reached the root,
every birth boundary is empty. -/
theorem squareRootCanonicalRoughFreshBirthBoundary_chain_sum_eq_zero_of_root_reached
    {R n : ℕ} (c p : ℕ → ℕ)
    (hR : 2 ≤ R)
    (hc : ∀ i, i < n → 0 < c i)
    (hp : ∀ i, i < n → (p i).Prime)
    (hfresh : ∀ i, i < n → canonicalLargestPrimeFactor (c i) < p i)
    (hroot : ∀ i, i < n → R ≤ p i * c i) :
    (∑ i in Finset.range n,
        ((squareRootCanonicalRoughFreshBirthBoundary R (c i) (p i)).card : ℂ)) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  have hin : i < n := Finset.mem_range.mp hi
  rw [squareRootCanonicalRoughFreshBirthBoundary_eq_empty_of_root_reached
    (hR := hR) (hc := hc i hin) (hp := hp i hin)
    (hfresh := hfresh i hin) (hroot := hroot i hin)]
  simp

/-- **Post-root ancestry telescope.**  Along any fresh-prime chain segment for
which every child is at or beyond `R`, the *positive* sum of loss-boundary
cardinalities is exactly the difference of the endpoint rough-partner
capacities.  Hence ancestry depth contributes no extra post-root multiplicity
on a single branch. -/
theorem squareRootCanonicalRoughFreshLossBoundary_chain_telescope_of_root_reached
    {R n : ℕ} (c p : ℕ → ℕ)
    (hR : 2 ≤ R)
    (hc : ∀ i, i < n → 0 < c i)
    (hp : ∀ i, i < n → (p i).Prime)
    (hfresh : ∀ i, i < n → canonicalLargestPrimeFactor (c i) < p i)
    (hstep : ∀ i, i < n → c (i + 1) = p i * c i)
    (hroot : ∀ i, i < n → R ≤ p i * c i) :
    (∑ i in Finset.range n,
        ((squareRootCanonicalRoughFreshLossBoundary R (c i) (p i)).card : ℂ)) =
      squareRootCanonicalRoughPrimePartnerCount R (c 0) -
        squareRootCanonicalRoughPrimePartnerCount R (c n) := by
  calc
    (∑ i in Finset.range n,
        ((squareRootCanonicalRoughFreshLossBoundary R (c i) (p i)).card : ℂ)) =
      ∑ i in Finset.range n,
        (squareRootCanonicalRoughPrimePartnerCount R (c i) -
          squareRootCanonicalRoughPrimePartnerCount R (c (i + 1))) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hin : i < n := Finset.mem_range.mp hi
        have hedge :=
          squareRootCanonicalRoughPrimePartnerCount_sub_freshChild_eq_lossBoundary
            (R := R) (c := c i) (p := p i)
            hR (hc i hin) (hp i hin) (hfresh i hin) (hroot i hin)
        rw [← hstep i hin] at hedge
        exact hedge.symm
    _ = squareRootCanonicalRoughPrimePartnerCount R (c 0) -
        squareRootCanonicalRoughPrimePartnerCount R (c n) := by
      simpa using complex_sum_range_forwardDifference
        (fun i => squareRootCanonicalRoughPrimePartnerCount R (c i)) n

end RHLean.Proof
