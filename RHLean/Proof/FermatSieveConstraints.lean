import Mathlib
import RHLean.Proof.DeathShellCardinalityAndCentering

/-!
# Fermat sieve constraints for death-shell factor pairs

This module records the exact parity and terminal-digit restrictions for a
Fermat representation

`N = a^2 - b^2 = (a-b)(a+b)`

of an odd integer. These finite congruence classifications are intended for
use in the semiprime-cofactor part of the death-shell analysis.
-/

noncomputable section

namespace RHLean.Proof

/-- Terminal digits viewed modulo ten. -/
abbrev FermatDigit := Fin 10

/-- The terminal-digit Fermat congruence `a^2 - b^2 = N (mod 10)`. -/
def FermatDigitCongruence
    (N a b : FermatDigit) : Prop :=
  ((a.val : ZMod 10) ^ 2 - (b.val : ZMod 10) ^ 2) = (N.val : ZMod 10)

/-- The `N ≡ 1 (mod 10)` Fermat digit table in the `N ≡ 1 (mod 4)` parity lane. -/
theorem fermatDigitCongruence_one_iff
    (a b : FermatDigit) :
    FermatDigitCongruence ⟨1, by decide⟩ a b ∧
        a.val % 2 = 1 ∧ b.val % 2 = 0 ↔
      (a.val = 1 ∧ b.val = 0) ∨
      (a.val = 5 ∧ b.val = 2) ∨
      (a.val = 5 ∧ b.val = 8) ∨
      (a.val = 9 ∧ b.val = 0) := by
  fin_cases a <;> fin_cases b <;> native_decide

/-- The `N ≡ 3 (mod 10)` Fermat digit table in the `N ≡ 3 (mod 4)` parity lane. -/
theorem fermatDigitCongruence_three_iff
    (a b : FermatDigit) :
    FermatDigitCongruence ⟨3, by decide⟩ a b ∧
        a.val % 2 = 0 ∧ b.val % 2 = 1 ↔
      (a.val = 2 ∧ b.val = 1) ∨
      (a.val = 2 ∧ b.val = 9) ∨
      (a.val = 8 ∧ b.val = 1) ∨
      (a.val = 8 ∧ b.val = 9) := by
  fin_cases a <;> fin_cases b <;> native_decide

/-- The `N ≡ 7 (mod 10)` Fermat digit table in the `N ≡ 3 (mod 4)` parity lane. -/
theorem fermatDigitCongruence_seven_iff
    (a b : FermatDigit) :
    FermatDigitCongruence ⟨7, by decide⟩ a b ∧
        a.val % 2 = 0 ∧ b.val % 2 = 1 ↔
      (a.val = 4 ∧ b.val = 3) ∨
      (a.val = 4 ∧ b.val = 7) ∨
      (a.val = 6 ∧ b.val = 3) ∨
      (a.val = 6 ∧ b.val = 7) := by
  fin_cases a <;> fin_cases b <;> native_decide

/-- The `N ≡ 9 (mod 10)` Fermat digit table in the `N ≡ 1 (mod 4)` parity lane. -/
theorem fermatDigitCongruence_nine_iff
    (a b : FermatDigit) :
    FermatDigitCongruence ⟨9, by decide⟩ a b ∧
        a.val % 2 = 1 ∧ b.val % 2 = 0 ↔
      (a.val = 3 ∧ b.val = 0) ∨
      (a.val = 5 ∧ b.val = 4) ∨
      (a.val = 5 ∧ b.val = 6) ∨
      (a.val = 7 ∧ b.val = 0) := by
  fin_cases a <;> fin_cases b <;> native_decide

/-- Finite mod-four classification: an odd Fermat difference congruent to one
modulo four lies in the odd-even lane. -/
theorem fermatParity_one_mod_four
    (a b : Fin 4)
    (h : ((a.val : ZMod 4) ^ 2 - (b.val : ZMod 4) ^ 2) = 1) :
    a.val % 2 = 1 ∧ b.val % 2 = 0 := by
  fin_cases a <;> fin_cases b <;> native_decide

/-- Finite mod-four classification: an odd Fermat difference congruent to three
modulo four lies in the even-odd lane. -/
theorem fermatParity_three_mod_four
    (a b : Fin 4)
    (h : ((a.val : ZMod 4) ^ 2 - (b.val : ZMod 4) ^ 2) = 3) :
    a.val % 2 = 0 ∧ b.val % 2 = 1 := by
  fin_cases a <;> fin_cases b <;> native_decide

/-- In either odd Fermat parity lane, the doubled product `2ab` is divisible by
four. -/
theorem four_dvd_two_mul_of_fermatParity
    {a b : ℕ}
    (h : (Odd a ∧ Even b) ∨ (Even a ∧ Odd b)) :
    4 ∣ 2 * a * b := by
  rcases h with ⟨_, hb⟩ | ⟨ha, _⟩
  · rcases hb with ⟨k, rfl⟩
    exact ⟨a * k, by omega⟩
  · rcases ha with ⟨k, rfl⟩
    exact ⟨k * b, by omega⟩

end RHLean.Proof
