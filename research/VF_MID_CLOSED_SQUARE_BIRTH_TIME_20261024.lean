import Mathlib
import RHLean.Analysis.NativePNTMertens

/-!
# Closed-square fixed-square prefix and birth-time Mobius algebra

Finite exact identities; no exponent improvement claimed. The moving shell
source and the open/closed endpoint bridge are separate follow-up targets.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators
namespace RHLean.Analysis

def closedSquareShellMu (k : ℕ) : ℤ := ArithmeticFunction.moebius k

def closedSquareShellHarmonic (A : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 A, (ArithmeticFunction.moebius a : ℝ) / (a : ℝ)

theorem closedSquareShell_squarePrefix_drift_eq_sq
    (f : ℕ → ℝ) (Y : ℕ) :
    (∑ a ∈ Finset.Icc 1 Y,
      ∑ b ∈ Finset.Icc 1 Y, f a * f b) =
      (∑ a ∈ Finset.Icc 1 Y, f a) ^ 2 := by
  calc
    (∑ a ∈ Finset.Icc 1 Y, ∑ b ∈ Finset.Icc 1 Y, f a * f b) =
        ∑ a ∈ Finset.Icc 1 Y, f a * (∑ b ∈ Finset.Icc 1 Y, f b) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.mul_sum]
    _ = (∑ a ∈ Finset.Icc 1 Y, f a) *
        (∑ b ∈ Finset.Icc 1 Y, f b) := by rw [Finset.sum_mul]
    _ = (∑ a ∈ Finset.Icc 1 Y, f a) ^ 2 := by ring

theorem closedSquareShell_actual_squarePrefix_drift_eq_sq (Y : ℕ) :
    (∑ a ∈ Finset.Icc 1 Y,
      ∑ b ∈ Finset.Icc 1 Y,
        ((ArithmeticFunction.moebius a : ℝ) / (a : ℝ)) *
          ((ArithmeticFunction.moebius b : ℝ) / (b : ℝ))) =
      closedSquareShellHarmonic Y ^ 2 := by
  exact closedSquareShell_squarePrefix_drift_eq_sq
    (fun a => (ArithmeticFunction.moebius a : ℝ) / (a : ℝ)) Y

theorem closedSquareShell_sawtooth_window_telescope
    (ψ : ℕ → ℝ) (A B : ℕ) (hAB : A ≤ B) :
    (∑ r ∈ Finset.Ico A B, (ψ (r ^ 2) - ψ ((r + 1) ^ 2))) =
      ψ (A ^ 2) - ψ (B ^ 2) := by
  have h := Finset.sum_Ico_sub (fun r => ψ (r ^ 2)) hAB
  calc
    (∑ r ∈ Finset.Ico A B, (ψ (r ^ 2) - ψ ((r + 1) ^ 2))) =
        (∑ r ∈ Finset.Ico A B, ψ (r ^ 2)) -
        (∑ r ∈ Finset.Ico A B, ψ ((r + 1) ^ 2)) := by
          rw [Finset.sum_sub_distrib]
    _ = -((∑ r ∈ Finset.Ico A B, ψ ((r + 1) ^ 2)) -
          (∑ r ∈ Finset.Ico A B, ψ (r ^ 2))) := by ring
    _ = ψ (A ^ 2) - ψ (B ^ 2) := by
          rw [← Finset.sum_sub_distrib, h]
          ring

theorem closedSquareShell_pair_birth_telescope
    (f : ℕ → ℤ) (k B : ℕ) (hkB : k ≤ B) :
    (∑ r ∈ Finset.Ico k B, (f (r + 1) - f r)) = f B - f k := by
  simpa only [] using Finset.sum_Ico_sub f hkB

theorem closedSquareShell_native_floor_unit (k : ℕ) (hk : 1 ≤ k) :
    (∑ b ∈ Finset.Icc 1 k,
      closedSquareShellMu b * (((k / b : ℕ) : ℤ))) = 1 := by
  simpa only [closedSquareShellMu] using nativeSumMoebiusMulFloor k hk

theorem closedSquareShell_floor_before_birth (k : ℕ) (hk : 1 ≤ k) :
    (∑ b ∈ Finset.Icc 1 (k - 1),
      closedSquareShellMu b * (((k / b : ℕ) : ℤ))) = 1 - closedSquareShellMu k := by
  let f : ℕ → ℤ := fun b => closedSquareShellMu b * (((k / b : ℕ) : ℤ))
  have hfull : (∑ b ∈ Finset.Icc 1 k, f b) = 1 := by
    simpa [f] using closedSquareShell_native_floor_unit k hk
  have hsplit :
      (∑ b ∈ Finset.Icc 1 k, f b) =
        (∑ b ∈ Finset.Icc 1 (k - 1), f b) + f k := by
    have hsucc : k - 1 + 1 = k := by omega
    conv_lhs => rw [← hsucc]
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k - 1 + 1)]
    simp only [hsucc]
  have htop : f k = closedSquareShellMu k := by
    change closedSquareShellMu k * (((k / k : ℕ) : ℤ)) = closedSquareShellMu k
    rw [Nat.div_self (by omega : 0 < k)]
    norm_num
  change (∑ b ∈ Finset.Icc 1 (k - 1), f b) = 1 - closedSquareShellMu k
  rw [htop] at hsplit
  omega

def closedSquareShellBirthBill (k : ℕ) : ℤ :=
    (∑ b ∈ Finset.Icc 1 (k - 1),
      closedSquareShellMu k * closedSquareShellMu b * (((k / b : ℕ) : ℤ))) +
    (∑ a ∈ Finset.Icc 1 (k - 1),
      closedSquareShellMu a * closedSquareShellMu k * (((k / a : ℕ) : ℤ))) +
    (closedSquareShellMu k) ^ 2

theorem closedSquareShell_birthTime_floor_eq_two_mu_sub_mu_sq
    (k : ℕ) (hk : 1 ≤ k) :
    closedSquareShellBirthBill k =
      2 * closedSquareShellMu k - (closedSquareShellMu k) ^ 2 := by
  have hlow := closedSquareShell_floor_before_birth k hk
  unfold closedSquareShellBirthBill
  have hfirst :
      (∑ b ∈ Finset.Icc 1 (k - 1),
        closedSquareShellMu k * closedSquareShellMu b * (((k / b : ℕ) : ℤ))) =
      closedSquareShellMu k * (∑ b ∈ Finset.Icc 1 (k - 1),
        closedSquareShellMu b * (((k / b : ℕ) : ℤ))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hsecond :
      (∑ a ∈ Finset.Icc 1 (k - 1),
        closedSquareShellMu a * closedSquareShellMu k * (((k / a : ℕ) : ℤ))) =
      closedSquareShellMu k * (∑ a ∈ Finset.Icc 1 (k - 1),
        closedSquareShellMu a * (((k / a : ℕ) : ℤ))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hfirst, hsecond, hlow]
  ring

theorem closedSquareShell_sum_birth_bills (A B : ℕ) :
    (∑ k ∈ Finset.Ico (A + 1) B, closedSquareShellBirthBill k) =
      2 * (∑ k ∈ Finset.Ico (A + 1) B, closedSquareShellMu k) -
        (∑ k ∈ Finset.Ico (A + 1) B, (closedSquareShellMu k) ^ 2) := by
  classical
  have hk : ∀ k ∈ Finset.Ico (A + 1) B, 1 ≤ k := by
    intro k h
    exact (by omega : 1 ≤ A + 1).trans (Finset.mem_Ico.mp h).1
  calc
    (∑ k ∈ Finset.Ico (A + 1) B, closedSquareShellBirthBill k) =
      ∑ k ∈ Finset.Ico (A + 1) B,
        (2 * closedSquareShellMu k - (closedSquareShellMu k) ^ 2) := by
          apply Finset.sum_congr rfl
          intro k h
          exact closedSquareShell_birthTime_floor_eq_two_mu_sub_mu_sq k (hk k h)
    _ = 2 * (∑ k ∈ Finset.Ico (A + 1) B, closedSquareShellMu k) -
      (∑ k ∈ Finset.Ico (A + 1) B, (closedSquareShellMu k) ^ 2) := by
        rw [Finset.sum_sub_distrib, Finset.mul_sum]

theorem closedSquareShell_birth_root_diagonal_cancel (A B : ℕ) :
    (∑ k ∈ Finset.Ico (A + 1) B, (closedSquareShellMu k) ^ 2) +
      (∑ k ∈ Finset.Ico (A + 1) B, (2 * closedSquareShellMu k - (closedSquareShellMu k) ^ 2)) =
      2 * (∑ k ∈ Finset.Ico (A + 1) B, closedSquareShellMu k) := by
  rw [← Finset.sum_add_distrib]
  simp_rw [show ∀ k : ℕ,
    closedSquareShellMu k ^ 2 + (2 * closedSquareShellMu k - closedSquareShellMu k ^ 2) =
      2 * closedSquareShellMu k from fun _ => by ring]
  rw [Finset.mul_sum]


/-- Literal closed-square quotient, with the root factor cancelled. -/
theorem closedSquareShell_birth_root_quotient_left
    (k b : ℕ) (hk : 0 < k) :
    k ^ 2 / (k * b) = k / b := by
  simpa only [pow_two] using
    (Nat.mul_div_mul_left (m := k) k b hk)

/-- The other, ordered birth leg is the same arithmetic quotient. -/
theorem closedSquareShell_birth_root_quotient_right
    (k a : ℕ) (hk : 0 < k) :
    k ^ 2 / (a * k) = k / a := by
  rw [Nat.mul_comm a k]
  exact closedSquareShell_birth_root_quotient_left k a hk

/-- The new square-corner floor is exactly one. -/
theorem closedSquareShell_birth_root_quotient_diag
    (k : ℕ) (hk : 0 < k) :
    k ^ 2 / (k * k) = 1 := by
  rw [pow_two]
  exact Nat.div_self (Nat.mul_pos hk hk)

/-- The already-paid root birth bill is the *literal* physical floor bill. -/
theorem closedSquareShell_birth_bill_eq_literal_root_floor
    (k : ℕ) (hk : 0 < k) :
    closedSquareShellBirthBill k =
      (∑ a ∈ Finset.Icc 1 (k - 1),
        closedSquareShellMu a * closedSquareShellMu k *
          (((k ^ 2 / (a * k) : ℕ) : ℤ))) +
      (∑ b ∈ Finset.Icc 1 (k - 1),
        closedSquareShellMu k * closedSquareShellMu b *
          (((k ^ 2 / (k * b) : ℕ) : ℤ))) +
        closedSquareShellMu k * closedSquareShellMu k *
          (((k ^ 2 / (k * k) : ℕ) : ℤ)) := by
  unfold closedSquareShellBirthBill
  rw [closedSquareShell_birth_root_quotient_diag k hk]
  simp only [closedSquareShell_birth_root_quotient_left k _ hk,
    closedSquareShell_birth_root_quotient_right k _ hk]
  ring


#print axioms closedSquareShell_squarePrefix_drift_eq_sq
#print axioms closedSquareShell_actual_squarePrefix_drift_eq_sq
#print axioms closedSquareShell_sawtooth_window_telescope
#print axioms closedSquareShell_pair_birth_telescope
#print axioms closedSquareShell_native_floor_unit
#print axioms closedSquareShell_floor_before_birth
#print axioms closedSquareShell_birth_root_quotient_left
#print axioms closedSquareShell_birth_root_quotient_right
#print axioms closedSquareShell_birth_root_quotient_diag
#print axioms closedSquareShell_birth_bill_eq_literal_root_floor
#print axioms closedSquareShell_birthTime_floor_eq_two_mu_sub_mu_sq
#print axioms closedSquareShell_sum_birth_bills
#print axioms closedSquareShell_birth_root_diagonal_cancel

end RHLean.Analysis
