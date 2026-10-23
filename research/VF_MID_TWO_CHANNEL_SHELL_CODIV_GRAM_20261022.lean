import Mathlib
import «research.VF_MID_SHELL_COFACTOR_FIBER_GATE_SWITCH_20261022»
import «research.VF_919_SEVEN_EIGHTHS_SIGNED_COVARIANCE_20261019»

/-!
# Complete fixed-wheel multi-shell conservation and Co-Div consumer

For shells a<=R<b, with a>=2, define the ORIGINAL physical
smooth/innovation shell differences A and B and the gate charge Gamma.
Then
  A = F_b(X_b)-F_a(X_a) + Gamma
  B = G_b(X_b)-G_a(X_a) - Gamma
  A+B = M(X_b)-M(X_a).
No gate correction is discarded or assumed statistically small.

The full zero-target Gram at X_b is the square of
M(X_a)+A+B, including the starting anchor M(X_a).
There is NO signed analytic gain in these finite equalities.
-/

noncomputable section
open scoped BigOperators
namespace RHLean.Analysis

def buchstabSmoothShellWindow (a b : ℕ) : ℂ :=
  ∑ R ∈ Finset.Ico a b, buchstabFloorLiSquareShellSmoothDelta R

def buchstabInnovationShellWindow (a b : ℕ) : ℂ :=
  ∑ R ∈ Finset.Ico a b, buchstabFloorLiSquareShellInnovationDelta R

def buchstabGateChargeWindow (a b : ℕ) : ℂ :=
  ∑ R ∈ Finset.Ico a b, buchstabShellGateCharge R

/-- The first endpoint bracket of each shell, with its OWN fixed wheel. -/
def buchstabSmoothShellBoundary (R : ℕ) : ℂ :=
  buchstabFloorLiSmoothBracket R (buchstabSquareShellLower R)

def buchstabInnovationShellBoundary (R : ℕ) : ℂ :=
  buchstabFloorLiInnovationBracket R (buchstabSquareShellLower R)

/-- The within-shell smooth increment is a telescoping boundary
increment PLUS the gate-switch charge at the right endpoint. -/
theorem buchstab_smoothShellDelta_eq_boundaryDiff_add_gate
    (R : ℕ) (hR : 2 ≤ R) :
    buchstabFloorLiSquareShellSmoothDelta R =
      (buchstabSmoothShellBoundary (R + 1) -
        buchstabSmoothShellBoundary R) +
      buchstabShellGateCharge R := by
  have hgate := buchstab_gate_switch_smooth R hR
  unfold buchstabFloorLiSquareShellSmoothDelta
    buchstabSmoothShellBoundary
  linear_combination -hgate

/-- The within-shell innovation increment is the matching
boundary increment MINUS the same exact signed gate charge. -/
theorem buchstab_innovationShellDelta_eq_boundaryDiff_sub_gate
    (R : ℕ) (hR : 2 ≤ R) :
    buchstabFloorLiSquareShellInnovationDelta R =
      (buchstabInnovationShellBoundary (R + 1) -
        buchstabInnovationShellBoundary R) -
      buchstabShellGateCharge R := by
  have hgate := buchstab_gate_switch_innovation R hR
  unfold buchstabFloorLiSquareShellInnovationDelta
    buchstabInnovationShellBoundary
  linear_combination -hgate

/-- Multi-shell smooth telescope with the gate charge INCLUDED. -/
theorem buchstab_multiShell_smooth_telescope
    (a b : ℕ) (ha : 2 ≤ a) (hab : a ≤ b) :
    buchstabSmoothShellWindow a b =
      buchstabSmoothShellBoundary b -
        buchstabSmoothShellBoundary a +
      buchstabGateChargeWindow a b := by
  unfold buchstabSmoothShellWindow buchstabGateChargeWindow
  calc
    (∑ R ∈ Finset.Ico a b, buchstabFloorLiSquareShellSmoothDelta R) =
        ∑ R ∈ Finset.Ico a b,
          ((buchstabSmoothShellBoundary (R + 1) -
              buchstabSmoothShellBoundary R) +
             buchstabShellGateCharge R) := by
      apply Finset.sum_congr rfl
      intro R hR
      exact buchstab_smoothShellDelta_eq_boundaryDiff_add_gate
        R (ha.trans (Finset.mem_Ico.mp hR).1)
    _ = (∑ R ∈ Finset.Ico a b,
            (buchstabSmoothShellBoundary (R + 1) -
              buchstabSmoothShellBoundary R)) +
          ∑ R ∈ Finset.Ico a b, buchstabShellGateCharge R := by
      rw [Finset.sum_add_distrib]
    _ = _ := by
      rw [Finset.sum_Ico_sub buchstabSmoothShellBoundary hab]
      ring

/-- Multi-shell innovation telescope with the OPPOSITE gate charge. -/
theorem buchstab_multiShell_innovation_telescope
    (a b : ℕ) (ha : 2 ≤ a) (hab : a ≤ b) :
    buchstabInnovationShellWindow a b =
      buchstabInnovationShellBoundary b -
        buchstabInnovationShellBoundary a -
      buchstabGateChargeWindow a b := by
  unfold buchstabInnovationShellWindow buchstabGateChargeWindow
  calc
    (∑ R ∈ Finset.Ico a b, buchstabFloorLiSquareShellInnovationDelta R) =
        ∑ R ∈ Finset.Ico a b,
          ((buchstabInnovationShellBoundary (R + 1) -
              buchstabInnovationShellBoundary R) -
             buchstabShellGateCharge R) := by
      apply Finset.sum_congr rfl
      intro R hR
      exact buchstab_innovationShellDelta_eq_boundaryDiff_sub_gate
        R (ha.trans (Finset.mem_Ico.mp hR).1)
    _ = (∑ R ∈ Finset.Ico a b,
            (buchstabInnovationShellBoundary (R + 1) -
              buchstabInnovationShellBoundary R)) -
          ∑ R ∈ Finset.Ico a b, buchstabShellGateCharge R := by
      rw [Finset.sum_sub_distrib]
    _ = _ := by
      rw [Finset.sum_Ico_sub buchstabInnovationShellBoundary hab]

/-- The complete signed window is exactly the Mertens endpoint
difference. The two gate-switch sums cancel in THIS identity. -/
theorem buchstab_multiShell_signed_mertens
    (a b : ℕ) (ha : 2 ≤ a) (hab : a ≤ b) :
    buchstabSmoothShellWindow a b + buchstabInnovationShellWindow a b =
      mertensSummatory (buchstabSquareShellLower b) -
        mertensSummatory (buchstabSquareShellLower a) := by
  rw [buchstab_multiShell_smooth_telescope a b ha hab,
    buchstab_multiShell_innovation_telescope a b ha hab]
  have hleft :=
    buchstab_mertens_eq_floorLi_smooth_add_innovation_of_sqrt_le
      a (buchstabSquareShellLower a) (by omega)
      (le_of_lt (buchstab_squareShell_lower_sqrt_lt a ha))
  have hright :=
    buchstab_mertens_eq_floorLi_smooth_add_innovation_of_sqrt_le
      b (buchstabSquareShellLower b) (by omega) (by
        by_cases hb : 2 ≤ b
        · exact le_of_lt (buchstab_squareShell_lower_sqrt_lt b hb)
        · omega)
  unfold buchstabSmoothShellBoundary buchstabInnovationShellBoundary
  linear_combination hright - hleft

/-- Exact algebraic two-channel square, retaining the mixed interaction. -/
theorem buchstab_twoChannel_signed_gram (a b : ℕ) :
    (buchstabSmoothShellWindow a b + buchstabInnovationShellWindow a b) ^ 2 =
      buchstabSmoothShellWindow a b ^ 2 +
        2 * buchstabSmoothShellWindow a b *
          buchstabInnovationShellWindow a b +
        buchstabInnovationShellWindow a b ^ 2 := by
  ring

/-- The full original diagonal plus ALL positive-lag signed pairs.
Unlike an unanchored shell window, the original M(X_a) is INCLUDED. -/
theorem buchstab_full_mobius_codiv_anchored_window
    (a b : ℕ) (ha : 2 ≤ a) (hab : a ≤ b) :
    realMertensDiagonal (buchstabSquareShellLower b + 1) +
        2 * realMertensPositiveLagPairSum
          (buchstabSquareShellLower b + 1) =
      ‖mertensSummatory (buchstabSquareShellLower a) +
          buchstabSmoothShellWindow a b +
          buchstabInnovationShellWindow a b‖ ^ 2 := by
  have hwindow := buchstab_multiShell_signed_mertens a b ha hab
  have hmass :
      mertensSummatory (buchstabSquareShellLower b) =
        mertensSummatory (buchstabSquareShellLower a) +
          buchstabSmoothShellWindow a b +
          buchstabInnovationShellWindow a b := by
    linear_combination -hwindow
  rw [← vf919_mertens_sq_eq_signedPair (buchstabSquareShellLower b), hmass]

/-- Exact algebraic cancellation of both window gate migrations. -/
theorem buchstab_gate_charges_cancel (a b : ℕ) :
    buchstabGateChargeWindow a b +
      (-buchstabGateChargeWindow a b) = 0 := by
  ring

#print axioms buchstab_multiShell_smooth_telescope
#print axioms buchstab_multiShell_innovation_telescope
#print axioms buchstab_multiShell_signed_mertens
#print axioms buchstab_full_mobius_codiv_anchored_window
#print axioms buchstab_gate_charges_cancel

end RHLean.Analysis
