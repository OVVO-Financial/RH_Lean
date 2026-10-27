import Mathlib
import «research.EULER_FRACTIONAL_COUPLED_20261027»

/-!
# Historical Euler rank-one floor subtraction, with exact divisor-row cancellation

At X=(R-1)(R+1), Mobius inversion says
  sum_{a<R} mu(a) floor((R-1)/a) = 1.
Subtract this LITERAL one-sided row from the true floor bilinear.
The resulting kernel equals a (rank-one) historical sawtooth minus the
original two-index fractional sawtooth, at every positive a,b.
A row indexed by a | (R-1) has exact value -{X/(ab)}.

No smallness of the full non-divisor-row remainder is asserted.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof
open RHLean.Analysis

/-- Original rank-one-subtracted floor, with genuine quotient and rational b. -/
def eulerRankOneFloorKernelQ (R a b : ℕ) : ℚ :=
  eulerFloorQ R a b -
    ((R + 1 : ℕ) : ℚ) / (b : ℚ) * (((R - 1) / a : ℕ) : ℚ)

/-- The historical one-index fractional part at the LOWER endpoint N=R-1. -/
def eulerHistoricalFracQ (R a : ℕ) : ℚ :=
  (((R - 1 : ℕ) : ℚ) / (a : ℚ)) - (((R - 1) / a : ℕ) : ℚ)

/-- Complete original two-index residual, not a formal name for Q itself. -/
def eulerRankOneResidualQ (R : ℕ) : ℚ :=
  ∑ b ∈ Finset.Icc 1 (R - 1), eulerMuQ b *
    ∑ a ∈ Finset.Icc 1 (R - 1),
      eulerMuQ a * eulerRankOneFloorKernelQ R a b

/-- Physical square horizon factors exactly, without a continuous approximation. -/
theorem eulerRootEndpoint_factor (R : ℕ) (hR : 2 ≤ R) :
    squareRootEndpoint R = (R + 1) * (R - 1) := by
  cases R with
  | zero => omega
  | succ n =>
      change (n + 1) ^ 2 - 1 = (n + 1 + 1) * n
      have hsq : (n + 1) ^ 2 = (n + 1 + 1) * n + 1 := by ring
      rw [hsq]
      omega

/-- The rank-one subtraction couples BOTH fractional modes, exactly. -/
theorem eulerRankOneFloorKernel_eq_coupled_fracs
    (R a b : ℕ) (hR : 2 ≤ R) :
    eulerRankOneFloorKernelQ R a b =
      ((R + 1 : ℕ) : ℚ) / (b : ℚ) * eulerHistoricalFracQ R a -
        eulerFractionQ R a b := by
  unfold eulerRankOneFloorKernelQ eulerHistoricalFracQ
    eulerFractionQ eulerContinuousQ
  rw [eulerRootEndpoint_factor R hR]
  simp only [Nat.cast_mul, div_eq_mul_inv, mul_inv_rev]
  ring

/-- Exact finite genuine Mobius inversion: the historical lower-floor row is 1. -/
theorem eulerHistoricalFloorInversionQ (R : ℕ) (hR : 2 ≤ R) :
    (∑ a ∈ Finset.Icc 1 (R - 1), eulerMuQ a *
      (((R - 1) / a : ℕ) : ℚ)) = 1 := by
  have h := RHLean.Analysis.nativeSumMoebiusMulFloor (R - 1) (by omega)
  have hQ := congrArg (fun z : ℤ => (z : ℚ)) h
  simpa [eulerMuQ] using hQ

/-- The exact original Q_R minus an independently bounded linear root mode. -/
theorem eulerRankOneResidualQ_eq_floor_sub_linear
    (R : ℕ) (hR : 2 ≤ R) :
    eulerRankOneResidualQ R =
      eulerFloorBilinearQ R -
        ((R + 1 : ℕ) : ℚ) * eulerReciprocalHistoricalQ R := by
  let S := Finset.Icc 1 (R - 1)
  have hInversion := eulerHistoricalFloorInversionQ R hR
  have hcor (b : ℕ) :
      (∑ a ∈ S,
        eulerMuQ a *
          (((R + 1 : ℕ) : ℚ) / (b : ℚ) * (((R - 1) / a : ℕ) : ℚ))) =
        ((R + 1 : ℕ) : ℚ) / (b : ℚ) := by
    calc
      _ = ((R + 1 : ℕ) : ℚ) / (b : ℚ) *
            (∑ a ∈ S, eulerMuQ a * (((R - 1) / a : ℕ) : ℚ)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _ha
          ring
      _ = _ := by
        change ((R + 1 : ℕ) : ℚ) / (b : ℚ) *
            (∑ a ∈ Finset.Icc 1 (R - 1),
              eulerMuQ a * (((R - 1) / a : ℕ) : ℚ)) =
          ((R + 1 : ℕ) : ℚ) / (b : ℚ)
        rw [hInversion]
        ring
  unfold eulerRankOneResidualQ eulerRankOneFloorKernelQ
    eulerFloorBilinearQ eulerReciprocalHistoricalQ
  calc
    (∑ b ∈ S, eulerMuQ b *
      ∑ a ∈ S, eulerMuQ a *
        (eulerFloorQ R a b -
          ((R + 1 : ℕ) : ℚ) / (b : ℚ) *
            (((R - 1) / a : ℕ) : ℚ))) =
      (∑ b ∈ S, eulerMuQ b *
        (∑ a ∈ S, eulerMuQ a * eulerFloorQ R a b)) -
      (∑ b ∈ S, eulerMuQ b *
        ((R + 1 : ℕ) : ℚ) / (b : ℚ)) := by
          simp_rw [mul_sub, Finset.sum_sub_distrib]
          simp_rw [mul_sub, Finset.sum_sub_distrib]
          simp_rw [hcor]
    _ = (∑ b ∈ S, eulerMuQ b *
        ∑ a ∈ S, eulerMuQ a * eulerFloorQ R a b) -
      ((R + 1 : ℕ) : ℚ) * (∑ a ∈ S, eulerMuQ a / (a : ℚ)) := by
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b _hb
          ring

/-- Divisor rows have EXACTLY minus the fractional kernel.
This is a direct quantitative reduction on a nonempty arithmetic sector. -/
theorem eulerRankOneFloorKernel_divisor_row
    (R a b : ℕ) (hR : 2 ≤ R) (ha : 0 < a)
    (hadiv : a ∣ R - 1) :
    eulerRankOneFloorKernelQ R a b = -eulerFractionQ R a b := by
  have hmod : (R - 1) % a = 0 := Nat.mod_eq_zero_of_dvd hadiv
  have hn := Nat.mod_add_div (R - 1) a
  rw [hmod, zero_add] at hn
  have hnQ : (a : ℚ) * (((R - 1) / a : ℕ) : ℚ) = ((R - 1 : ℕ) : ℚ) := by
    exact_mod_cast hn
  have ha0 : (a : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ha)
  have hfrac : eulerHistoricalFracQ R a = 0 := by
    unfold eulerHistoricalFracQ
    have hdiv : (((R - 1 : ℕ) : ℚ) / (a : ℚ)) =
        (((R - 1) / a : ℕ) : ℚ) := by
      apply (div_eq_iff ha0).2
      calc
        ((R - 1 : ℕ) : ℚ) =
            (a : ℚ) * (((R - 1) / a : ℕ) : ℚ) := hnQ.symm
        _ = _ := mul_comm _ _
    rw [hdiv]
    ring
  rw [eulerRankOneFloorKernel_eq_coupled_fracs R a b hR, hfrac]
  ring

#print axioms eulerRankOneFloorKernel_eq_coupled_fracs
#print axioms eulerHistoricalFloorInversionQ
#print axioms eulerRankOneResidualQ_eq_floor_sub_linear
#print axioms eulerRankOneFloorKernel_divisor_row

end RHLean.Proof
