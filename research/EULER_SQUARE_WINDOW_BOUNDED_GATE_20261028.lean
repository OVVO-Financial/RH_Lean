import Mathlib
import «research.EULER_RANK_ONE_FRACTIONAL_ROWS_20261027»
import «research.EULER_SELF_DUAL_ENDPOINT_GATE_20261027»

/-!
# Actual Euler historical square-window sampling, with bounded moving gate

For R>=3 write X=R²-1, Y=(R+1)²-1. The ORIGINAL self-dual
Euler bilinear Q_R uses the genuine Mobius factors a,b<R. Its
fixed-historical window W_R is the same old (a,b) population observed at
the two consecutive physical square endpoints.

The only population addition when passing to Q_(R+1) is a=R or b=R.
Using mu*zeta=1, this whole moving-history gate collapses to THREE local
Mobius coefficients, bounded by five. This removes a feared large
dynamic-cutoff error, without claiming a new analytic signed power saving.

The shared-prime and long-period correlations inside W_R remain open.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof
open RHLean.Analysis

/-- ORIGINAL physical window, keeping a,b<R fixed across the two walls. -/
def eulerHistoricalSquareWindowQ (R : ℕ) : ℚ :=
  ∑ b ∈ Finset.Icc 1 (R - 1), eulerMuQ b *
    ∑ a ∈ Finset.Icc 1 (R - 1), eulerMuQ a *
      (eulerFloorQ (R + 1) a b - eulerFloorQ R a b)

/-- Small local correction from admitting the new history index R. -/
def eulerHistoricalSquareGateQ (R : ℕ) : ℚ :=
  eulerMuQ R ^ 2 +
    2 * eulerMuQ R * (eulerMuQ (R + 1) + eulerMuQ (R + 2))

private theorem euler_sum_Icc_top (R : ℕ) (hR : 1 ≤ R)
    (f : ℕ → ℚ) :
    (∑ a ∈ Finset.Icc 1 R, f a) =
      (∑ a ∈ Finset.Icc 1 (R - 1), f a) + f R := by
  have hp : R - 1 + 1 = R := by omega
  calc
    _ = ∑ a ∈ Finset.Icc 1 (R - 1 + 1), f a := by rw [hp]
    _ = _ := Finset.sum_Icc_succ_top (by omega : 1 ≤ R - 1 + 1)

/-- One symmetric new row, one symmetric new column, and one diagonal.
No positive absolute-value bound is inserted during the row expansion. -/
private theorem euler_historical_double_sum_top
    (R : ℕ) (hR : 1 ≤ R) (F : ℕ → ℕ → ℚ)
    (hsym : ∀ a b, F a b = F b a) :
    (∑ b ∈ Finset.Icc 1 R, eulerMuQ b *
      ∑ a ∈ Finset.Icc 1 R, eulerMuQ a * F a b) =
    (∑ b ∈ Finset.Icc 1 (R - 1), eulerMuQ b *
      ∑ a ∈ Finset.Icc 1 (R - 1), eulerMuQ a * F a b) +
    2 * eulerMuQ R *
      (∑ a ∈ Finset.Icc 1 (R - 1), eulerMuQ a * F a R) +
    eulerMuQ R ^ 2 * F R R := by
  have hi (b : ℕ) :
      (∑ a ∈ Finset.Icc 1 R, eulerMuQ a * F a b) =
      (∑ a ∈ Finset.Icc 1 (R - 1), eulerMuQ a * F a b) +
        eulerMuQ R * F R b :=
    euler_sum_Icc_top R hR _
  have hs :
      (∑ b ∈ Finset.Icc 1 (R - 1),
          eulerMuQ b * (eulerMuQ R * F R b)) =
        eulerMuQ R * (∑ a ∈ Finset.Icc 1 (R - 1),
          eulerMuQ a * F a R) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _hb
    rw [hsym R b]
    ring
  calc
    _ = (∑ b ∈ Finset.Icc 1 (R - 1),
          eulerMuQ b * (∑ a ∈ Finset.Icc 1 R,
            eulerMuQ a * F a b)) +
        eulerMuQ R * (∑ a ∈ Finset.Icc 1 R,
            eulerMuQ a * F a R) := by
          rw [euler_sum_Icc_top R hR]
    _ = (∑ b ∈ Finset.Icc 1 (R - 1),
          eulerMuQ b * ((∑ a ∈ Finset.Icc 1 (R - 1),
            eulerMuQ a * F a b) + eulerMuQ R * F R b)) +
        eulerMuQ R * ((∑ a ∈ Finset.Icc 1 (R - 1),
          eulerMuQ a * F a R) + eulerMuQ R * F R R) := by
          simp_rw [hi]
    _ = _ := by
          simp_rw [mul_add, Finset.sum_add_distrib]
          rw [hs]
          ring

/-- The actual second square-wall is R*(R+2), with no rounding. -/
theorem eulerHistoricalSquareWindow_upper
    (R : ℕ) :
    squareRootEndpoint (R + 1) = R * (R + 2) := by
  unfold squareRootEndpoint
  have hp : (R + 1) ^ 2 = R * (R + 2) + 1 := by ring
  rw [hp]
  omega

/-- Cancel the new row's root factor exactly before flooring. -/
theorem eulerHistoricalSquareWindow_newRowFloor
    (R a : ℕ) (hR : 1 ≤ R) :
    squareRootEndpoint (R + 1) / (a * R) =
      (R + 2) / a := by
  rw [eulerHistoricalSquareWindow_upper, Nat.mul_comm a R]
  exact Nat.mul_div_mul_left (m := R) (R + 2) a (by omega)

/-- The new diagonal is 1 for all R>=3. -/
theorem eulerHistoricalSquareWindow_newDiagonal
    (R : ℕ) (hR : 3 ≤ R) :
    squareRootEndpoint (R + 1) / (R * R) = 1 := by
  rw [eulerHistoricalSquareWindow_upper]
  apply Nat.div_eq_of_lt_le
  · nlinarith
  · nlinarith

private theorem eulerHistoricalSquareWindow_upperThreeFloor
    (R j : ℕ) (hR : 3 ≤ R) (hj : j ≤ 2) :
    (R + 2) / (R + j) = 1 := by
  apply Nat.div_eq_of_lt_le
  · omega
  · omega

/-- The whole new row is determined by just the next three Mobius signs,
using the *already certified* full Möbius divisor-floor inversion. -/
theorem eulerHistoricalSquareWindow_newRowIdentity
    (R : ℕ) (hR : 3 ≤ R) :
    (∑ a ∈ Finset.Icc 1 (R - 1),
        eulerMuQ a * eulerFloorQ (R + 1) a R) =
      1 - eulerMuQ R - eulerMuQ (R + 1) -
        eulerMuQ (R + 2) := by
  have hfull := eulerHistoricalFloorInversionQ (R + 3) (by omega)
  have htop2 := euler_sum_Icc_top (R + 2) (by omega)
      (fun a => eulerMuQ a * (((R + 2) / a : ℕ) : ℚ))
  have htop1 := euler_sum_Icc_top (R + 1) (by omega)
      (fun a => eulerMuQ a * (((R + 2) / a : ℕ) : ℚ))
  have htop0 := euler_sum_Icc_top R (by omega)
      (fun a => eulerMuQ a * (((R + 2) / a : ℕ) : ℚ))
  have hp : R + 3 - 1 = R + 2 := by omega
  have hq0 : (R + 2) / R = 1 := by
    simpa using eulerHistoricalSquareWindow_upperThreeFloor R 0 hR (by omega)
  have hq1 : (R + 2) / (R + 1) = 1 := by
    simpa using eulerHistoricalSquareWindow_upperThreeFloor R 1 hR (by omega)
  have hq2 : (R + 2) / (R + 2) = 1 := by
    simpa using eulerHistoricalSquareWindow_upperThreeFloor R 2 hR (by omega)
  have hrow :
      (∑ a ∈ Finset.Icc 1 (R - 1),
          eulerMuQ a * (((R + 2) / a : ℕ) : ℚ)) =
      1 - eulerMuQ R - eulerMuQ (R + 1) -
        eulerMuQ (R + 2) := by
    rw [hp, htop2, htop1, htop0, hq0, hq1, hq2] at hfull
    norm_num at hfull
    linear_combination -hfull
  calc
    _ = ∑ a ∈ Finset.Icc 1 (R - 1),
          eulerMuQ a * (((R + 2) / a : ℕ) : ℚ) := by
          apply Finset.sum_congr rfl
          intro a ha
          unfold eulerFloorQ
          rw [eulerHistoricalSquareWindow_newRowFloor R a (by omega)]
    _ = _ := hrow

/-- The moving-history gate is uniformly bounded by 5. -/
theorem eulerHistoricalSquareGateQ_abs_le_five (R : ℕ) :
    |eulerHistoricalSquareGateQ R| ≤ 5 := by
  rcases ArithmeticFunction.moebius_eq_or R with h | h | h <;>
    rcases ArithmeticFunction.moebius_eq_or (R + 1) with h1 | h1 | h1 <;>
      rcases ArithmeticFunction.moebius_eq_or (R + 2) with h2 | h2 | h2 <;>
        norm_num [eulerHistoricalSquareGateQ, eulerMuQ, h, h1, h2]

/-- Original self-dual Euler source moves by its HISTORICAL floor window
plus the exact O(1) new-history boundary. -/
theorem eulerHistoricalSquareWindow_bilinear_step
    (R : ℕ) (hR : 3 ≤ R) :
    eulerFloorBilinearQ (R + 1) - eulerFloorBilinearQ R =
      eulerHistoricalSquareWindowQ R + 2 * eulerMuQ R -
        eulerHistoricalSquareGateQ R := by
  have hsym (a b : ℕ) :
      eulerFloorQ (R + 1) a b =
        eulerFloorQ (R + 1) b a := by
    unfold eulerFloorQ
    rw [Nat.mul_comm]
  have hsplit := euler_historical_double_sum_top R (by omega)
      (fun a b => eulerFloorQ (R + 1) a b) hsym
  have hfixed :
      (∑ b ∈ Finset.Icc 1 (R - 1), eulerMuQ b *
        ∑ a ∈ Finset.Icc 1 (R - 1), eulerMuQ a *
          eulerFloorQ (R + 1) a b) -
          eulerFloorBilinearQ R =
        eulerHistoricalSquareWindowQ R := by
    unfold eulerFloorBilinearQ eulerHistoricalSquareWindowQ
    simp_rw [mul_sub, Finset.sum_sub_distrib]
  have hgate := eulerHistoricalSquareWindow_newRowIdentity R hR
  have hdiag : eulerFloorQ (R + 1) R R = 1 := by
    unfold eulerFloorQ
    exact_mod_cast (eulerHistoricalSquareWindow_newDiagonal R hR)
  have hpred : R + 1 - 1 = R := by omega
  change eulerFloorBilinearQ (R + 1) - eulerFloorBilinearQ R =
      eulerHistoricalSquareWindowQ R + 2 * eulerMuQ R -
        eulerHistoricalSquareGateQ R
  unfold eulerFloorBilinearQ at hsplit
  rw [hpred] at hsplit
  rw [hgate, hdiag] at hsplit
  unfold eulerHistoricalSquareGateQ
  linear_combination hsplit + hfixed

/-- Square-shell Mertens increment equals the old historical divisor-window
process up to a uniformly bounded *local* gate, with no random signs. -/
theorem eulerHistoricalSquareWindow_mertens_step
    (R : ℕ) (hR : 3 ≤ R) :
    mertensSummatory (squareRootEndpoint (R + 1)) -
        mertensSummatory (squareRootEndpoint R) =
      ((eulerHistoricalSquareGateQ R -
        eulerHistoricalSquareWindowQ R : ℚ) : ℂ) := by
  have hQnew :=
    eulerSelfDualBilinear_eq_two_mertens_sub_endpoint (R + 1) (by omega)
  have hQold := eulerSelfDualBilinear_eq_two_mertens_sub_endpoint R
    (by omega)
  have hQstep := eulerHistoricalSquareWindow_bilinear_step R hR
  have hQstepC := congrArg (fun z : ℚ => (z : ℂ)) hQstep
  rw [Rat.cast_sub, eulerFloorBilinearQ_cast_eq_original,
    eulerFloorBilinearQ_cast_eq_original] at hQstepC
  rw [hQnew, hQold] at hQstepC
  have hm : mertensSummatory R =
      mertensSummatory (R - 1) + (((μ R : ℤ) : ℂ)) := by
    have hpred : R - 1 + 1 = R := by omega
    rw [← hpred, mertensSummatory_succ]
  rw [hm] at hQstepC
  unfold eulerMuQ at hQstepC
  push_cast at hQstepC
  linear_combination -hQstepC

#print axioms eulerHistoricalSquareWindow_newRowIdentity
#print axioms eulerHistoricalSquareGateQ_abs_le_five
#print axioms eulerHistoricalSquareWindow_bilinear_step
#print axioms eulerHistoricalSquareWindow_mertens_step

end RHLean.Proof
