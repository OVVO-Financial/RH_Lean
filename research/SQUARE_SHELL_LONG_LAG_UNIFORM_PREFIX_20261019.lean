import Mathlib
import «research.SQUARE_SHELL_LONG_LAG_FIVE_SIXTHS_20261019»

/-!
# Uniform prefix version of the long-lag 5/6 reduction

The completed dyadic root band alone controls only selected square endpoints.
A global Mertens exponent needs every partial band H <= r < H+K,
0 <= K <= H. This module makes K a separate independent parameter and
instantiates the generic near-lag lemma with actual genuine Mobius square-shell
increments. Both diagonal and near lag are paid without PNT or cancellation.

The long-lag correlation upper bound (uniform in K) remains OPEN.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

/-- Transport the existing generic K-row lemma to a physical start H. -/
def shellLagPrefixLift (f : ℕ → ℝ) (H K n : ℕ) : ℝ :=
  f (H + (n - K))

/-- The physically separated long-lag pair sum inside [H,H+K). -/
def shellLagPrefixFar (f : ℕ → ℝ) (H K L : ℕ) : ℝ :=
  shellLagFar (shellLagPrefixLift f H K) K L

/-- The complementary near-lag pair sum inside [H,H+K). -/
def shellLagPrefixNear (f : ℕ → ℝ) (H K L : ℕ) : ℝ :=
  shellLagNear (shellLagPrefixLift f H K) K L

/-- This is a literal physical-index row, not a different surrogate. -/
theorem shellLagPrefixLift_row (f : ℕ → ℝ) (H K : ℕ) :
    shellLagDyadicRow (shellLagPrefixLift f H K) K =
      fun j => f (H + j) := by
  funext j
  simp [shellLagDyadicRow, shellLagPrefixLift]

theorem shellLagPrefixFar_eq_physical
    (f : ℕ → ℝ) (H K L : ℕ) :
    shellLagPrefixFar f H K L =
      ∑ j ∈ Finset.range K,
        ∑ i ∈ Finset.range (j - L), f (H + i) * f (H + j) := by
  unfold shellLagPrefixFar shellLagFar shellLagPrefixLift
  simp only [Nat.add_sub_cancel_left]

theorem shellLagPrefixNear_eq_physical
    (f : ℕ → ℝ) (H K L : ℕ) :
    shellLagPrefixNear f H K L =
      ∑ j ∈ Finset.range K,
        ∑ i ∈ Finset.Ico (j - L) j, f (H + i) * f (H + j) := by
  unfold shellLagPrefixNear shellLagNear shellLagPrefixLift
  simp only [Nat.add_sub_cancel_left]

/-- Exact uniform-prefix Gram, no arithmetic approximation. -/
theorem shellLagPrefix_sq_eq_diagonal_near_far
    (f : ℕ → ℝ) (H K L : ℕ) :
    signedBlockPrefix (fun j => f (H + j)) K ^ 2 =
      signedBlockEnergy (fun j => f (H + j)) K +
        2 * shellLagPrefixNear f H K L +
        2 * shellLagPrefixFar f H K L := by
  have h := shellLagDyadicBlock_sq_eq_diagonal_add_near_add_far
    (shellLagPrefixLift f H K) K L
  simpa only [shellLagPrefixLift_row, shellLagPrefixNear,
    shellLagPrefixFar] using h

/-- Physical atoms of every partial dyadic root interval have envelope C. -/
def ShellLagPrefixAtomsBounded
    (f : ℕ → ℝ) (H K : ℕ) (C : ℝ) : Prop :=
  ∀ j : ℕ, j < K → |f (H + j)| ≤ C

/-- The coefficient K in this theorem is the actual partial length, and
the start H remains independent. The long-lag term keeps its sign. -/
theorem shellLagPrefix_sq_le_far_pay
    (f : ℕ → ℝ) (H K L : ℕ) (C : ℝ)
    (hC : 0 ≤ C) (hb : ShellLagPrefixAtomsBounded f H K C) :
    signedBlockPrefix (fun j => f (H + j)) K ^ 2 ≤
      (K : ℝ) * C ^ 2 +
        2 * (K : ℝ) * (L : ℝ) * C ^ 2 +
        2 * shellLagPrefixFar f H K L := by
  have hbLift :
      ShellLagAtomsBounded (shellLagPrefixLift f H K) K C := by
    intro j hj
    simpa [shellLagPrefixLift, Nat.add_sub_cancel_left] using hb j hj
  have h := shellLagDyadicBlock_sq_le_far_pay
    (shellLagPrefixLift f H K) K L C hC hbLift
  simpa only [shellLagPrefixLift_row, shellLagPrefixFar] using h

/-- Every true Mobius atom is absolutely at most 1. -/
private theorem shellLag_moebius_atom_abs_le_one (n : ℕ) :
    |realMoebiusStep n| ≤ 1 := by
  unfold realMoebiusStep
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)

/-- An actual Mobius shell has at most 2*r+1 seats, each of absolute
weight <= 1. This binds the new analysis to genuine physical Mobius. -/
theorem shellLag_realSquareBlockMass_abs_le_length (r : ℕ) :
    |realSquareBlockMass r| ≤ (2 * r + 1 : ℕ) := by
  unfold realSquareBlockMass
  have hcard : (Finset.Ico (r ^ 2) ((r + 1) ^ 2)).card = 2 * r + 1 := by
    rw [Nat.card_Ico]
    have hsq : (r + 1) ^ 2 = r ^ 2 + (2 * r + 1) := by ring
    rw [hsq]
    omega
  calc
    |∑ n ∈ Finset.Ico (r ^ 2) ((r + 1) ^ 2), realMoebiusStep n| ≤
        ∑ n ∈ Finset.Ico (r ^ 2) ((r + 1) ^ 2),
          |realMoebiusStep n| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Finset.Ico (r ^ 2) ((r + 1) ^ 2), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        exact shellLag_moebius_atom_abs_le_one n
    _ = (2 * r + 1 : ℕ) := by simp [hcard]

/-- Genuine Mobius shells throughout every partial block
H <= r < H+K <= 2H have the unconditional uniform 4H envelope. -/
theorem shellLag_actualMobius_partialAtomsBounded
    (H K : ℕ) (hK : K ≤ H) (_hH : 1 ≤ H) :
    ShellLagPrefixAtomsBounded realSquareBlockMass H K (4 * (H : ℝ)) := by
  intro j hj
  have hlen := shellLag_realSquareBlockMass_abs_le_length (H + j)
  have hnat : 2 * (H + j) + 1 ≤ 4 * H := by omega
  have hreal : (((2 * (H + j) + 1 : ℕ) : ℝ)) ≤ 4 * (H : ℝ) := by
    exact_mod_cast hnat
  exact hlen.trans hreal

/-- **Uniform K <= H**: diagonal and all short lags are already within
the endpoint 5/6 exponent budget, before any Mobius sign cancellation. -/
theorem shellLag_actualMobius_partial_sq_le_far
    (H K L : ℕ) (hK : K ≤ H) (hH : 1 ≤ H) :
    signedBlockPrefix (fun j => realSquareBlockMass (H + j)) K ^ 2 ≤
      16 * (K : ℝ) * (H : ℝ) ^ 2 +
        32 * (K : ℝ) * (L : ℝ) * (H : ℝ) ^ 2 +
        2 * shellLagPrefixFar realSquareBlockMass H K L := by
  have hb := shellLag_actualMobius_partialAtomsBounded H K hK hH
  have h := shellLagPrefix_sq_le_far_pay realSquareBlockMass
    H K L (4 * (H : ℝ)) (by positivity) hb
  convert h using 1
  ring

#print axioms shellLagPrefix_sq_eq_diagonal_near_far
#print axioms shellLagPrefix_sq_le_far_pay
#print axioms shellLag_realSquareBlockMass_abs_le_length
#print axioms shellLag_actualMobius_partial_sq_le_far

end RHLean.Analysis
