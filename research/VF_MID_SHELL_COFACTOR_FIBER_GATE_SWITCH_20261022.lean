import Mathlib
import «research.VF_MID_FLOOR_LI_BUCHSTAB_EXACT_BRACKETS_20261022»

/-!
# Square shell: exact fixed-root gate-switch and the centered cofactor profile

The prime wheel y=R remains fixed on both shell endpoints
X_R=R^2-1, X_(R+1)=(R+1)^2-1. At the UPPER endpoint,
changing the wheel from R to R+1 charges precisely one
weighted prime-minus-floor-Li innovation at q=R+1.

This is algebraic conservation, NOT a signed rate estimate.
-/

noncomputable section
open scoped BigOperators
namespace RHLean.Analysis

/-- Physical signed prime-minus-integer-floor-Li gate switch. -/
def buchstabShellGateCharge (R : ℕ) : ℂ :=
  vfMidFloorLiMismatchFrequencyWeight (R + 1) * mertensSummatory R

/-- The upper shell endpoint is exactly R*(R+2). -/
theorem buchstab_squareShell_upper_eq_mul (R : ℕ) :
    buchstabSquareShellUpper R = R * (R + 2) := by
  unfold buchstabSquareShellUpper
  have hpos : 1 ≤ (R + 1) ^ 2 := by positivity
  have hsub : (R + 1) ^ 2 - 1 + 1 = (R + 1) ^ 2 :=
    Nat.sub_add_cancel hpos
  nlinarith

/-- At X_(R+1), the FIRST newly excluded q=R+1 has quotient R. -/
theorem buchstab_squareShell_upper_div_succ
    (R : ℕ) (hR : 2 ≤ R) :
    buchstabSquareShellUpper R / (R + 1) = R := by
  rw [buchstab_squareShell_upper_eq_mul]
  apply Nat.div_eq_of_lt_le
  · nlinarith
  · nlinarith

/-- The q=R+1 atom is the sole difference of the two high-prime
innovation tails; no indicator-based special casing is necessary. -/
theorem buchstab_gate_switch_innovation
    (R : ℕ) (hR : 2 ≤ R) :
    buchstabFloorLiInnovationBracket (R + 1) (buchstabSquareShellUpper R) -
      buchstabFloorLiInnovationBracket R (buchstabSquareShellUpper R) =
      buchstabShellGateCharge R := by
  let Z := buchstabSquareShellUpper R
  have hRZ : R < Z := by
    dsimp [Z]
    rw [buchstab_squareShell_upper_eq_mul]
    nlinarith
  have hset :
      Finset.Ioc R Z = insert (R + 1) (Finset.Ioc (R + 1) Z) :=
    (Finset.insert_Ioc_add_one_left_eq_Ioc hRZ).symm
  have hnot : R + 1 ∉ Finset.Ioc (R + 1) Z := by simp
  have hdiv : Z / (R + 1) = R :=
    buchstab_squareShell_upper_div_succ R hR
  unfold buchstabFloorLiInnovationBracket
    buchstabFloorLiMismatchTail buchstabShellGateCharge
  rw [hset, Finset.sum_insert hnot, hdiv]
  ring

/-- The smooth/reference bracket pays the OPPOSITE q=R+1
charge. Proof reuses only the exact source split at both legal
cutoffs; it assumes no probabilistic balance or new source saving. -/
theorem buchstab_gate_switch_smooth
    (R : ℕ) (hR : 2 ≤ R) :
    buchstabFloorLiSmoothBracket (R + 1) (buchstabSquareShellUpper R) -
      buchstabFloorLiSmoothBracket R (buchstabSquareShellUpper R) =
      -buchstabShellGateCharge R := by
  have hroot := buchstab_squareShell_upper_sqrt_le R hR
  have hRfull :=
    buchstab_mertens_eq_floorLi_smooth_add_innovation_of_sqrt_le
      R (buchstabSquareShellUpper R) (by omega) hroot
  have hSuccFull :=
    buchstab_mertens_eq_floorLi_smooth_add_innovation_of_sqrt_le
      (R + 1) (buchstabSquareShellUpper R) (by omega) (by omega)
  have hSwitch := buchstab_gate_switch_innovation R hR
  linear_combination hRfull - hSuccFull - hSwitch

/-- Exact opposite-sign gate migration (NO smallness claim). -/
theorem buchstab_gate_switch_sum_zero
    (R : ℕ) (hR : 2 ≤ R) :
    (buchstabFloorLiSmoothBracket (R + 1) (buchstabSquareShellUpper R) -
       buchstabFloorLiSmoothBracket R (buchstabSquareShellUpper R)) +
      (buchstabFloorLiInnovationBracket (R + 1) (buchstabSquareShellUpper R) -
       buchstabFloorLiInnovationBracket R (buchstabSquareShellUpper R)) = 0 := by
  rw [buchstab_gate_switch_smooth R hR,
    buchstab_gate_switch_innovation R hR]
  ring

/-- Explicit clipped lower cofactor wall: at the left shell endpoint,
the k=R quotient is BELOW the prime cutoff R. -/
theorem buchstab_squareShell_lower_lastFiber_clipped
    (R : ℕ) (hR : 2 ≤ R) :
    (buchstabSquareShellLower R / R) < R := by
  have hsmall : buchstabSquareShellLower R < R * R := by
    unfold buchstabSquareShellLower
    have hpos : 1 ≤ R ^ 2 := by positivity
    omega
  exact (Nat.div_lt_iff_lt_mul (by omega : 0 < R)).2 (by simpa [Nat.mul_comm] using hsmall)

/-- The last (k=R) fiber at the right endpoint reaches R+2. -/
theorem buchstab_squareShell_upper_lastFiber
    (R : ℕ) (hR : 2 ≤ R) :
    buchstabSquareShellUpper R / R = R + 2 := by
  rw [buchstab_squareShell_upper_eq_mul]
  simp [Nat.mul_div_cancel_left, show 0 < R by omega]

#print axioms buchstab_squareShell_upper_eq_mul
#print axioms buchstab_gate_switch_innovation
#print axioms buchstab_gate_switch_smooth
#print axioms buchstab_gate_switch_sum_zero
#print axioms buchstab_squareShell_lower_lastFiber_clipped
#print axioms buchstab_squareShell_upper_lastFiber

end RHLean.Analysis
