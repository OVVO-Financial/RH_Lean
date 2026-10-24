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

private def shellMu (k : ℕ) : ℤ := ArithmeticFunction.moebius k

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
  simpa only [] using Finset.sum_Ico_sub (fun r => ψ (r ^ 2)) hAB

theorem closedSquareShell_pair_birth_telescope
    (f : ℕ → ℤ) (k B : ℕ) (hkB : k ≤ B) :
    (∑ r ∈ Finset.Ico k B, (f (r + 1) - f r)) = f B - f k := by
  simpa only [] using Finset.sum_Ico_sub f hkB

theorem closedSquareShell_native_floor_unit (k : ℕ) (hk : 1 ≤ k) :
    (∑ b ∈ Finset.Icc 1 k,
      shellMu b * (((k / b : ℕ) : ℤ))) = 1 := by
  simpa only [shellMu] using nativeSumMoebiusMulFloor k hk

theorem closedSquareShell_floor_before_birth (k : ℕ) (hk : 1 ≤ k) :
    (∑ b ∈ Finset.Icc 1 (k - 1),
      shellMu b * (((k / b : ℕ) : ℤ))) = 1 - shellMu k := by
  let f : ℕ → ℤ := fun b => shellMu b * (((k / b : ℕ) : ℤ))
  have hfull : (∑ b ∈ Finset.Icc 1 k, f b) = 1 := by
    simpa [f] using closedSquareShell_native_floor_unit k hk
  have hsplit :
      (∑ b ∈ Finset.Icc 1 k, f b) =
        (∑ b ∈ Finset.Icc 1 (k - 1), f b) + f k := by
    have hsucc : k - 1 + 1 = k := by omega
    conv_lhs => rw [← hsucc]
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k - 1 + 1)]
    simp only [hsucc]
  have htop : f k = shellMu k := by
    dsimp [f]
    simp [Nat.div_self (by omega : 0 < k)]
  change (∑ b ∈ Finset.Icc 1 (k - 1), f b) = 1 - shellMu k
  rw [htop] at hsplit
  omega

def closedSquareShellBirthBill (k : ℕ) : ℤ :=
    (∑ b ∈ Finset.Icc 1 (k - 1),
      shellMu k * shellMu b * (((k / b : ℕ) : ℤ))) +
    (∑ a ∈ Finset.Icc 1 (k - 1),
      shellMu a * shellMu k * (((k / a : ℕ) : ℤ))) +
    (shellMu k) ^ 2

theorem closedSquareShell_birthTime_floor_eq_two_mu_sub_mu_sq
    (k : ℕ) (hk : 1 ≤ k) :
    closedSquareShellBirthBill k =
      2 * shellMu k - (shellMu k) ^ 2 := by
  have hlow := closedSquareShell_floor_before_birth k hk
  unfold closedSquareShellBirthBill
  have hfirst :
      (∑ b ∈ Finset.Icc 1 (k - 1),
        shellMu k * shellMu b * (((k / b : ℕ) : ℤ))) =
      shellMu k * (∑ b ∈ Finset.Icc 1 (k - 1),
        shellMu b * (((k / b : ℕ) : ℤ))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hsecond :
      (∑ a ∈ Finset.Icc 1 (k - 1),
        shellMu a * shellMu k * (((k / a : ℕ) : ℤ))) =
      shellMu k * (∑ a ∈ Finset.Icc 1 (k - 1),
        shellMu a * (((k / a : ℕ) : ℤ))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hfirst, hsecond, hlow]
  ring

theorem closedSquareShell_sum_birth_bills (A B : ℕ) :
    (∑ k ∈ Finset.Ico (A + 1) B, closedSquareShellBirthBill k) =
      2 * (∑ k ∈ Finset.Ico (A + 1) B, shellMu k) -
        (∑ k ∈ Finset.Ico (A + 1) B, (shellMu k) ^ 2) := by
  classical
  have hk : ∀ k ∈ Finset.Ico (A + 1) B, 1 ≤ k := by
    intro k h; omega
  calc
    (∑ k ∈ Finset.Ico (A + 1) B, closedSquareShellBirthBill k) =
      ∑ k ∈ Finset.Ico (A + 1) B,
        (2 * shellMu k - (shellMu k) ^ 2) := by
          apply Finset.sum_congr rfl
          intro k h
          exact closedSquareShell_birthTime_floor_eq_two_mu_sub_mu_sq k (hk k h)
    _ = 2 * (∑ k ∈ Finset.Ico (A + 1) B, shellMu k) -
      (∑ k ∈ Finset.Ico (A + 1) B, (shellMu k) ^ 2) := by
        rw [Finset.sum_sub_distrib, Finset.mul_sum]

theorem closedSquareShell_birth_root_diagonal_cancel (A B : ℕ) :
    (∑ k ∈ Finset.Ico (A + 1) B, (shellMu k) ^ 2) +
      (∑ k ∈ Finset.Ico (A + 1) B, (2 * shellMu k - (shellMu k) ^ 2)) =
      2 * (∑ k ∈ Finset.Ico (A + 1) B, shellMu k) := by
  rw [← Finset.sum_add_distrib]
  simp_rw [show ∀ k : ℕ,
    shellMu k ^ 2 + (2 * shellMu k - shellMu k ^ 2) =
      2 * shellMu k from fun _ => by ring]
  rw [Finset.mul_sum]

#print axioms closedSquareShell_squarePrefix_drift_eq_sq
#print axioms closedSquareShell_actual_squarePrefix_drift_eq_sq
#print axioms closedSquareShell_sawtooth_window_telescope
#print axioms closedSquareShell_pair_birth_telescope
#print axioms closedSquareShell_native_floor_unit
#print axioms closedSquareShell_floor_before_birth
#print axioms closedSquareShell_birth_root_quotient_left
#print axioms closedSquareShell_birth_root_quotient_right
#print axioms closedSquareShell_birth_bill_eq_literal_root_floor
#print axioms closedSquareShell_birthTime_floor_eq_two_mu_sub_mu_sq
#print axioms closedSquareShell_sum_birth_bills
#print axioms closedSquareShell_birth_root_diagonal_cancel

end RHLean.Analysis
