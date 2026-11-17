import «research.HISTORICAL_DENSITY_MASK_OBSTRUCTION»

set_option autoImplicit false
open scoped BigOperators
open Finset RHLean.Analysis

example (s : Finset Nat) (c : Nat -> Real) (D : Nat) (beta : Real)
    (hD : 1 <= D) (hs : ∀ d ∈ s, D <= d)
    (hbalance : (∑ d ∈ s, c d / (d : Real)) = -1) :
    (∑ d ∈ s, |c d| / (d : Real) ^ beta) =
      (D : Real) ^ (1 - beta) +
        2 * (D : Real) ^ (1 - beta) *
          (∑ d ∈ s, max (c d) 0 / (d : Real)) +
        ∑ d ∈ s, |c d| / (d : Real) *
          ((d : Real) ^ (1 - beta) - (D : Real) ^ (1 - beta)) :=
  historicalDensityMask_cost_identity s c D beta hD hs hbalance

example (s : Finset Nat) (c : Nat -> Real) (D : Nat) (beta : Real)
    (hD : 1 <= D) (hs : ∀ d ∈ s, D <= d)
    (hbalance : (∑ d ∈ s, c d / (d : Real)) = -1) (hbeta : beta <= 1) :
    (D : Real) ^ (1 - beta) <= ∑ d ∈ s, |c d| / (d : Real) ^ beta :=
  historicalDensityMask_cost_lower s c D beta hD hs hbalance hbeta

example (s : Finset Nat) (c : Nat -> Real) (beta : Real)
    (hs : ∀ d ∈ s, 2 <= d)
    (hbalance : (∑ d ∈ s, c d / (d : Real)) = -1) (hbeta : beta < 1) :
    1 < ∑ d ∈ s, |c d| / (d : Real) ^ beta :=
  historicalDensityMask_cost_gt_one s c beta hs hbalance hbeta

example (s : Finset Nat) (c : Nat -> Real) (beta : Real)
    (hunit : 1 ∈ s) (hs : ∀ d ∈ s, 1 <= d) (hc : c 1 = 1)
    (hcancel : (∑ d ∈ s, c d / (d : Real)) = 0) (hbeta : beta < 1) :
    1 < ∑ d ∈ s.erase 1, |c d| / (d : Real) ^ beta :=
  historicalDensityMask_no_contraction s c beta hunit hs hc hcancel hbeta

example (D : Nat) (beta : Real) (hD : 1 <= D) :
    (∑ d ∈ ({D} : Finset Nat), (-(D : Real)) / (d : Real)) = -1 ∧
      (∑ d ∈ ({D} : Finset Nat), |-(D : Real)| / (d : Real) ^ beta) =
        (D : Real) ^ (1 - beta) :=
  historicalDensityMask_cost_sharp D beta hD

example (s : Finset Nat) (c : Nat -> Real)
    (hs : ∀ d ∈ s, 2 <= d)
    (hbalance : (∑ d ∈ s, c d / (d : Real)) = -1) :
    Real.sqrt 2 <= ∑ d ∈ s, |c d| / Real.sqrt (d : Real) := by
  simpa only [Real.sqrt_eq_rpow, show (1 : Real) - 1 / 2 = 1 / 2 by norm_num] using
    historicalDensityMask_cost_lower s c 2 (1 / 2) (by norm_num) hs hbalance (by norm_num)

#print historicalDensityMask_cost_identity
#print historicalDensityMask_cost_lower
#print historicalDensityMask_cost_gt_one
#print historicalDensityMask_no_contraction
#print historicalDensityMask_cost_sharp
