import Mathlib

/-!
# First-bad minimal payment — exact parity-compressed algebra

This is a SMALL, warning-fatal, Mathlib-only kernel test. It does not import
the expensive native StrongPNT/research graph. The native definitions are
w_R = V_R / R, C_R = R - P_R and D_R = pi(R^2)-VF_mid(R^2).

The ONLY open mathematical requirement is to establish the final balance
on ACTUAL primes under an ACTUAL first-bad hypothesis. Every theorem here
is an unconditional algebraic identity, not that requirement.
-/

noncomputable section

namespace RHLean.Analysis

/-- Upper zero-target partial mass: actual odd composites plus the negative
historical endpoint anchor. NO EVEN SITES are introduced. -/
def vfV2Upper (D w C : ℝ) : ℝ :=
  (|D| - D) / 2 + w * C

/-- Lower zero-target partial mass: actual odd prime seats plus the positive
historical endpoint anchor. -/
def vfV2Lower (D w P : ℝ) : ℝ :=
  (|D| + D) / 2 + (1 - w) * P

/-- Next actual signed endpoint defect after a block with P primes and
C composites on its R=P+C odd physical seats. -/
def vfV2Next (D w P C : ℝ) : ℝ :=
  D + P - w * (P + C)

/-- The squared anchored L1 NNS mass, NOT a statistical variance. -/
def vfV2OriginalMass (D w P C : ℝ) : ℝ :=
  (|D| + w * C + (1 - w) * P) ^ 2

/-- The exact ORIGINAL one-half contraction slack. -/
def vfV2Balance (D w P C : ℝ) : ℝ :=
  (vfV2Upper D w C + vfV2Lower D w P) ^ 2 -
    2 * (vfV2Upper D w C - vfV2Lower D w P) ^ 2

theorem vfV2Upper_sub_lower_eq_neg_next (D w P C : ℝ) :
    vfV2Upper D w C - vfV2Lower D w P =
      -vfV2Next D w P C := by
  unfold vfV2Upper vfV2Lower vfV2Next
  ring

theorem vfV2Upper_add_lower_eq_original_abs (D w P C : ℝ) :
    vfV2Upper D w C + vfV2Lower D w P =
      |D| + w * C + (1 - w) * P := by
  unfold vfV2Upper vfV2Lower
  ring

/-- Every bit of reference mass R*w is absorbed into R odd physical seats.
The even lattice is already included in V_R=R*w. -/
theorem vfV2ReferenceCompressedToOdd (R w V : ℝ)
    (hcalibrated : V = R * w) :
    R * w = V := by
  rw [hcalibrated]

/-- Algebraic original-budget weld: the source is NEXT DEFECT squared,
and the original NNS denominator is never enlarged. -/
theorem vfV2Balance_eq_originalMass_sub_two_next_sq (D w P C : ℝ) :
    vfV2Balance D w P C =
      vfV2OriginalMass D w P C -
        2 * (vfV2Next D w P C) ^ 2 := by
  unfold vfV2Balance vfV2OriginalMass
  rw [vfV2Upper_add_lower_eq_original_abs]
  rw [vfV2Upper_sub_lower_eq_neg_next]
  ring

/-- The hbalance obligation, with no extra sites and no unproved arithmetic
condition smuggled into the definition. -/
theorem vfV2Payment_iff_exactSignedBalance (D w P C : ℝ) :
    0 ≤ vfV2Balance D w P C ↔
      2 * (vfV2Next D w P C) ^ 2 ≤
        vfV2OriginalMass D w P C := by
  rw [vfV2Balance_eq_originalMass_sub_two_next_sq]
  constructor <;> intro h <;> linarith

/-- The equivalent nonnegative co-partial versus divergent two-sector payment. -/
theorem vfV2Balance_eq_neg_coDivExcess (D w P C : ℝ) :
    vfV2Balance D w P C =
      -(vfV2Upper D w C ^ 2 + vfV2Lower D w P ^ 2 -
        6 * vfV2Upper D w C * vfV2Lower D w P) := by
  unfold vfV2Balance
  ring

theorem vfV2Payment_iff_twoSector (D w P C : ℝ) :
    0 ≤ vfV2Balance D w P C ↔
      vfV2Upper D w C ^ 2 + vfV2Lower D w P ^ 2 ≤
        6 * vfV2Upper D w C * vfV2Lower D w P := by
  rw [vfV2Balance_eq_neg_coDivExcess]
  constructor <;> intro h <;> linarith

/-! ## True prime-minus-discrete-Li signed margins ## -/

def vfV2LiPlus (D w F R : Real) : Real :=
  |D| + w*R + (1-2*w)*F + Real.sqrt 2*(D+F-w*R)

def vfV2LiMinus (D w F R : Real) : Real :=
  |D| + w*R + (1-2*w)*F - Real.sqrt 2*(D+F-w*R)

theorem vfV2LiPlus_actual (D w F d R : Real) :
    vfV2Upper D w (R-(F+d)) + vfV2Lower D w (F+d) +
        Real.sqrt 2*vfV2Next D w (F+d) (R-(F+d)) =
      vfV2LiPlus D w F R + (1-2*w+Real.sqrt 2)*d := by
  rw [vfV2Upper_add_lower_eq_original_abs]
  unfold vfV2Next vfV2LiPlus
  ring

theorem vfV2LiMinus_actual (D w F d R : Real) :
    vfV2Upper D w (R-(F+d)) + vfV2Lower D w (F+d) -
        Real.sqrt 2*vfV2Next D w (F+d) (R-(F+d)) =
      vfV2LiMinus D w F R + (1-2*w-Real.sqrt 2)*d := by
  rw [vfV2Upper_add_lower_eq_original_abs]
  unfold vfV2Next vfV2LiMinus
  ring

/-- Factored original NNS payment; no new reference mass. -/
theorem vfV2Balance_factor (D w P C : Real) :
    vfV2Balance D w P C =
      (vfV2Upper D w C + vfV2Lower D w P +
        Real.sqrt 2*vfV2Next D w P C) *
      (vfV2Upper D w C + vfV2Lower D w P -
        Real.sqrt 2*vfV2Next D w P C) := by
  have hs : Real.sqrt (2 : Real) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num : (0 : Real) <= 2)
  unfold vfV2Balance
  rw [vfV2Upper_sub_lower_eq_neg_next]
  calc
    (vfV2Upper D w C + vfV2Lower D w P)^2 -
        2 * (-vfV2Next D w P C)^2 =
      (vfV2Upper D w C + vfV2Lower D w P)^2 -
        (Real.sqrt 2 * vfV2Next D w P C)^2 := by
          rw [mul_pow, hs]
          ring
    _ = _ := by ring

/-- An exact CONDITIONAL certificate using the SIGNED ACTUAL prime
error d = (pi(X)-Q(X))-(pi(R^2)-Q(R^2)), with Q=floor Li2.
The conditions themselves require true prime arithmetic. -/
theorem vfV2Payment_of_floorLi_actual_signed_bounds
    (D w F d R : Real)
    (hplus : 0 <= vfV2LiPlus D w F R + (1-2*w+Real.sqrt 2)*d)
    (hminus : 0 <= vfV2LiMinus D w F R + (1-2*w-Real.sqrt 2)*d) :
    0 <= vfV2Balance D w (F+d) (R-(F+d)) := by
  rw [vfV2Balance_factor]
  rw [vfV2LiPlus_actual, vfV2LiMinus_actual]
  exact mul_nonneg hplus hminus

/-- The cost of changing an anchored denominator from M to M+delta.
It is not additional physical budget. -/
theorem vfV2ParityRepacking_squares_cost (M delta : ℝ) :
    (M + delta) ^ 2 - M ^ 2 = 2 * M * delta + delta ^ 2 := by
  ring

/-- WARNING: a universal all-state one-half cone is FALSE even with
0 <= w <= 1, P,C >= 0. Arithmetic about actual primes is indispensable.
This concrete w=1/4, P=0, C=8 has negative slack. -/
theorem vfV2NoUnconditionalAllStateCone :
    ¬ ∀ D w P C : ℝ, 0 ≤ vfV2Balance D w P C := by
  intro hall
  have h := hall 0 (1 / 4) 0 8
  norm_num [vfV2Balance, vfV2Upper, vfV2Lower] at h

end RHLean.Analysis
