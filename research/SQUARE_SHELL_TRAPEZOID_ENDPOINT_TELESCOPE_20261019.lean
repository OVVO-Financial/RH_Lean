import Mathlib
import «research.SQUARE_SHELL_TRAPEZOID_CORRECTED_20261018»

/-!
# Endpoint-strength trapezoidal telescope (not an L2 loss)

The same half-open square-shell construction has a sharper effect on the
*complete signed sum of consecutive shells* than it does on a shell-by-shell
second moment. The residual is already a discrete derivative of the endpoint
sawtooth; summing it across the dyadic square block costs only O(T), rather
than O(H*T) from Cauchy--Schwarz applied to the collar energy.

These are exact finite identities for an arbitrary integer prefix primitive
P, and deterministic inequalities for a unit-Lipschitz primitive. They do
not prove the needed signed Mertens estimate. The endpoint method is not
forced to choose T=floor(H^(2/3)): any T within the original window-separation
condition remains arithmetically eligible.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

private theorem sum_difference_Ico
    (F : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    (∑ r ∈ Finset.Ico a b, (F r - F (r + 1))) = F a - F b := by
  have hforward :
      (∑ r ∈ Finset.Ico a b, (F (r + 1) - F r)) = F b - F a := by
    rw [Finset.sum_Ico_eq_sub _ hab,
      Finset.sum_range_sub F b, Finset.sum_range_sub F a]
    ring
  calc
    (∑ r ∈ Finset.Ico a b, (F r - F (r + 1))) =
        -(∑ r ∈ Finset.Ico a b, (F (r + 1) - F r)) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro r hr
          ring
    _ = -(F b - F a) := by rw [hforward]
    _ = F a - F b := by ring

/-- Exact two-wall cancellation: all interior sawtooths disappear. -/
theorem shellTrapezoidResidual_sum_eq_endpoint_saws
    (P : ℤ → ℝ) (a b T : ℕ) (hab : a ≤ b) :
    (∑ r ∈ Finset.Ico a b, shellTrapezoidResidual P r T) =
      shellTrapezoidSaw P (shellTrapezoidSquare a) T -
      shellTrapezoidSaw P (shellTrapezoidSquare b) T := by
  simp_rw [shellTrapezoidResidual_eq_saw_difference]
  exact sum_difference_Ico
    (fun r => shellTrapezoidSaw P (shellTrapezoidSquare r) T) hab

/-- Endpoint collar bound independent of the number b-a of square shells.
The stronger Mobius-specific T-bound comes from triangular weights; this
generic 2T-bound already improves on the H*T Cauchy estimate. -/
theorem shellTrapezoidResidual_sum_abs_le_two_radius
    (P : ℤ → ℝ) (hLip : ShellTrapezoidUnitLipschitz P)
    (a b T : ℕ) (hab : a ≤ b) :
    |∑ r ∈ Finset.Ico a b, shellTrapezoidResidual P r T| ≤
      2 * (T : ℝ) := by
  rw [shellTrapezoidResidual_sum_eq_endpoint_saws P a b T hab]
  have ha := shellTrapezoidSaw_abs_le_radius
    P hLip (shellTrapezoidSquare a) T
  have hb := shellTrapezoidSaw_abs_le_radius
    P hLip (shellTrapezoidSquare b) T
  have htri := abs_sub_le
    (shellTrapezoidSaw P (shellTrapezoidSquare a) T) 0
    (shellTrapezoidSaw P (shellTrapezoidSquare b) T)
  simp only [sub_zero, zero_sub, abs_neg] at htri
  linarith

/-- Consecutive sharp half-open shells telescope to the two square endpoints. -/
theorem shellTrapezoidSharp_sum_eq_prefix_difference
    (P : ℤ → ℝ) (a b : ℕ) (hab : a ≤ b) :
    (∑ r ∈ Finset.Ico a b, shellTrapezoidSharp P r) =
      P (shellTrapezoidSquare b) - P (shellTrapezoidSquare a) := by
  have h := sum_difference_Ico
    (fun r => P (shellTrapezoidSquare r)) hab
  calc
    (∑ r ∈ Finset.Ico a b, shellTrapezoidSharp P r) =
        -(∑ r ∈ Finset.Ico a b,
          (P (shellTrapezoidSquare r) -
            P (shellTrapezoidSquare (r + 1)))) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro r hr
          unfold shellTrapezoidSharp
          ring
    _ = -(P (shellTrapezoidSquare a) -
          P (shellTrapezoidSquare b)) := by rw [h]
    _ = P (shellTrapezoidSquare b) -
          P (shellTrapezoidSquare a) := by ring

/-- Sum of all smoothed shells is the same endpoint prefix difference with
only the two endpoint sawtooths restored. There is NO interior error sum. -/
theorem shellTrapezoidSmoothed_sum_eq_endpoint_corrected
    (P : ℤ → ℝ) (a b T : ℕ) (hab : a ≤ b) :
    (∑ r ∈ Finset.Ico a b, shellTrapezoidSmoothed P r T) =
      P (shellTrapezoidSquare b) - P (shellTrapezoidSquare a) -
        (shellTrapezoidSaw P (shellTrapezoidSquare a) T -
          shellTrapezoidSaw P (shellTrapezoidSquare b) T) := by
  have hr := shellTrapezoidResidual_sum_eq_endpoint_saws P a b T hab
  have hs := shellTrapezoidSharp_sum_eq_prefix_difference P a b hab
  unfold shellTrapezoidResidual at hr
  rw [Finset.sum_sub_distrib, hs] at hr
  linarith

/-- If a genuinely independent bound pays the complete smoothed endpoint
block, the original sharp block inherits it at the cost 2T. This is NOT a
proof of such an independent arithmetic bound. -/
theorem shellTrapezoidSharp_endpoint_abs_le_of_smoothed
    (P : ℤ → ℝ) (hLip : ShellTrapezoidUnitLipschitz P)
    (a b T : ℕ) (hab : a ≤ b) (K : ℝ)
    (hSmoothed :
      |∑ r ∈ Finset.Ico a b, shellTrapezoidSmoothed P r T| ≤ K) :
    |P (shellTrapezoidSquare b) - P (shellTrapezoidSquare a)| ≤
      K + 2 * (T : ℝ) := by
  have he := shellTrapezoidResidual_sum_abs_le_two_radius P hLip a b T hab
  have hsum :
      (∑ r ∈ Finset.Ico a b, shellTrapezoidSharp P r) =
        (∑ r ∈ Finset.Ico a b, shellTrapezoidSmoothed P r T) +
        (∑ r ∈ Finset.Ico a b, shellTrapezoidResidual P r T) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    unfold shellTrapezoidResidual
    ring
  rw [shellTrapezoidSharp_sum_eq_prefix_difference P a b hab] at hsum
  rw [hsum]
  have htri := abs_add_le
    (∑ r ∈ Finset.Ico a b, shellTrapezoidSmoothed P r T)
    (∑ r ∈ Finset.Ico a b, shellTrapezoidResidual P r T)
  linarith

#print axioms shellTrapezoidResidual_sum_eq_endpoint_saws
#print axioms shellTrapezoidResidual_sum_abs_le_two_radius
#print axioms shellTrapezoidSmoothed_sum_eq_endpoint_corrected
#print axioms shellTrapezoidSharp_endpoint_abs_le_of_smoothed

end RHLean.Analysis
