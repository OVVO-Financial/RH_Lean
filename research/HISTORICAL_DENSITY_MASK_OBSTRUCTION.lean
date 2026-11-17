import Mathlib

/-!
The sharp cost obstruction from 20261117-owner-0809-EST/HF1, independently
accepted at its finite-mask scope by 20261117-referee-1203-EST/IC.

The unit coefficient is one and the reciprocal density moment is zero.
Estimating the historical cofactor errors separately then costs more than
one at every exponent below one. This is a theorem about that absolute
certificate, not a lower bound for the genuine signed prime discrepancy.
The actual first-bad interpolation and its asymptotic cap transfer are not
claimed here. No RH premise, prime distribution or endpoint estimate enters.
-/

set_option autoImplicit false

noncomputable section
open scoped BigOperators
open Finset

namespace RHLean.Analysis

private theorem abs_eq_twice_positive_sub (x : Real) :
    |x| = 2 * max x 0 - x := by
  by_cases hx : 0 <= x
  · rw [abs_of_nonneg hx, max_eq_left hx]
    ring
  · have hx' : x <= 0 := le_of_not_ge hx
    rw [abs_of_nonpos hx', max_eq_right hx']
    ring

/-- Exact positive-mass and large-cofactor costs. The identity itself needs
no upper restriction on beta and no sign assumption on the coefficients. -/
theorem historicalDensityMask_cost_identity
    (s : Finset Nat) (c : Nat -> Real) (D : Nat) (beta : Real)
    (hD : 1 <= D) (hs : ∀ d ∈ s, D <= d)
    (hbalance : (∑ d ∈ s, c d / (d : Real)) = -1) :
    (∑ d ∈ s, |c d| / (d : Real) ^ beta) =
      (D : Real) ^ (1 - beta) +
        2 * (D : Real) ^ (1 - beta) *
          (∑ d ∈ s, max (c d) 0 / (d : Real)) +
        ∑ d ∈ s, |c d| / (d : Real) *
          ((d : Real) ^ (1 - beta) - (D : Real) ^ (1 - beta)) := by
  have hmass : (∑ d ∈ s, |c d| / (d : Real)) =
      1 + 2 * ∑ d ∈ s, max (c d) 0 / (d : Real) := by
    calc
      _ = ∑ d ∈ s, (2 * (max (c d) 0 / (d : Real)) -
          c d / (d : Real)) := by
        apply Finset.sum_congr rfl
        intro d _hd
        rw [abs_eq_twice_positive_sub]
        ring
      _ = 2 * (∑ d ∈ s, max (c d) 0 / (d : Real)) -
          ∑ d ∈ s, c d / (d : Real) := by
        rw [Finset.sum_sub_distrib, Finset.mul_sum]
      _ = _ := by rw [hbalance]; ring
  calc
    _ = ∑ d ∈ s, ((D : Real) ^ (1 - beta) * (|c d| / (d : Real)) +
        |c d| / (d : Real) *
          ((d : Real) ^ (1 - beta) - (D : Real) ^ (1 - beta))) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdpos : (0 : Real) < d := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hD.trans (hs d hd)))
      have hdpow : (d : Real) ^ beta != 0 := ne_of_gt (Real.rpow_pos_of_pos hdpos beta)
      rw [Real.rpow_sub hdpos, Real.rpow_one]
      field_simp [ne_of_gt hdpos, hdpow]
      <;> ring
    _ = (D : Real) ^ (1 - beta) * (∑ d ∈ s, |c d| / (d : Real)) +
        ∑ d ∈ s, |c d| / (d : Real) *
          ((d : Real) ^ (1 - beta) - (D : Real) ^ (1 - beta)) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = _ := by rw [hmass]; ring

/-- A larger minimum cofactor only raises the sharp absolute return cost. -/
theorem historicalDensityMask_cost_lower
    (s : Finset Nat) (c : Nat -> Real) (D : Nat) (beta : Real)
    (hD : 1 <= D) (hs : ∀ d ∈ s, D <= d)
    (hbalance : (∑ d ∈ s, c d / (d : Real)) = -1)
    (hbeta : beta <= 1) :
    (D : Real) ^ (1 - beta) <= ∑ d ∈ s, |c d| / (d : Real) ^ beta := by
  have hpositive : 0 <= ∑ d ∈ s, max (c d) 0 / (d : Real) :=
    Finset.sum_nonneg fun d _hd =>
      div_nonneg (le_max_right _ _) (Nat.cast_nonneg d)
  have hgap : 0 <= ∑ d ∈ s, |c d| / (d : Real) *
      ((d : Real) ^ (1 - beta) - (D : Real) ^ (1 - beta)) := by
    apply Finset.sum_nonneg
    intro d hd
    apply mul_nonneg (div_nonneg (abs_nonneg _) (Nat.cast_nonneg d))
    apply sub_nonneg.mpr
    exact Real.rpow_le_rpow (Nat.cast_nonneg D)
      (by exact_mod_cast hs d hd) (sub_nonneg.mpr hbeta)
  have hpow : 0 <= (D : Real) ^ (1 - beta) := Real.rpow_nonneg (Nat.cast_nonneg D) _
  rw [historicalDensityMask_cost_identity s c D beta hD hs hbalance]
  nlinarith

/-- No nonunit density-cancelling tail has absolute cost at most one below
the linear exponent. This does not constrain the signed return itself. -/
theorem historicalDensityMask_cost_gt_one
    (s : Finset Nat) (c : Nat -> Real) (beta : Real)
    (hs : ∀ d ∈ s, 2 <= d)
    (hbalance : (∑ d ∈ s, c d / (d : Real)) = -1)
    (hbeta : beta < 1) :
    1 < ∑ d ∈ s, |c d| / (d : Real) ^ beta := by
  have hpow : (1 : Real) < (2 : Real) ^ (1 - beta) :=
    Real.one_lt_rpow (by norm_num) (sub_pos.mpr hbeta)
  exact hpow.trans_le
    (historicalDensityMask_cost_lower s c 2 beta (by norm_num) hs hbalance hbeta.le)

/-- Original full-mask formulation: retain the unit and its exact reciprocal
moment before removing it from the historical cost. -/
theorem historicalDensityMask_no_contraction
    (s : Finset Nat) (c : Nat -> Real) (beta : Real)
    (hunit : 1 ∈ s) (hs : ∀ d ∈ s, 1 <= d)
    (hc : c 1 = 1) (hcancel : (∑ d ∈ s, c d / (d : Real)) = 0)
    (hbeta : beta < 1) :
    1 < ∑ d ∈ s.erase 1, |c d| / (d : Real) ^ beta := by
  have htail : ∀ d ∈ s.erase 1, 2 <= d := by
    intro d hd
    have hm := Finset.mem_erase.mp hd
    have hp := hs d hm.2
    omega
  have hsplit : (∑ d ∈ s.erase 1, c d / (d : Real)) + c 1 / (1 : Real) =
      ∑ d ∈ s, c d / (d : Real) := Finset.sum_erase_add _ _ hunit
  have hbalance : (∑ d ∈ s.erase 1, c d / (d : Real)) = -1 := by
    rw [hc, hcancel] at hsplit
    norm_num at hsplit
    linarith
  exact historicalDensityMask_cost_gt_one (s.erase 1) c beta htail hbalance hbeta

/-- The lower bound is attained by the single historical cofactor D with
coefficient -D. In particular D=2 gives the sharp original HF1 constant. -/
theorem historicalDensityMask_cost_sharp (D : Nat) (beta : Real) (hD : 1 <= D) :
    (∑ d ∈ ({D} : Finset Nat), (-(D : Real)) / (d : Real)) = -1 ∧
      (∑ d ∈ ({D} : Finset Nat), |-(D : Real)| / (d : Real) ^ beta) =
        (D : Real) ^ (1 - beta) := by
  have hpos : (0 : Real) < D := by exact_mod_cast (Nat.zero_lt_one.trans_le hD)
  constructor
  · simp [ne_of_gt hpos]
  · simp [abs_of_nonneg (Nat.cast_nonneg D), Real.rpow_sub hpos, Real.rpow_one]

end RHLean.Analysis
