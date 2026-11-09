import Mathlib
import RHLean.Arithmetic.FourPrimeWheelCancellation

/-!
# Four fixed primes: parity cancellation versus square-killing physical drift

All prime coordinates remain exactly {2,3,5,7}. The 210-periodic parity
wheel has zero complete-cell sum. The physical square-killing wheel has
period 44100 and positive complete-cell sum 2304.

At square roots R=44100*t, its signed square-block mass is exactly 4608*t.
This shows why parity-only near-uniformity cannot itself control the actual
Mobius square-block source. Actual higher-prime cofactor signs remain in a
separate, necessary signed compensation ledger.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Arithmetic

def fourPrimeSquarekillPeriod : ℕ := 44100

/-- Four-prime squarefree sign on the true p^2-periodic residue clock. -/
def fourPrimeSquarekillSign (n : ℕ) : ℤ :=
  let r := n % fourPrimeSquarekillPeriod
  (if 4 ∣ r then (0 : ℤ) else if 2 ∣ r then -1 else 1) *
  (if 9 ∣ r then (0 : ℤ) else if 3 ∣ r then -1 else 1) *
  (if 25 ∣ r then (0 : ℤ) else if 5 ∣ r then -1 else 1) *
  (if 49 ∣ r then (0 : ℤ) else if 7 ∣ r then -1 else 1)

@[simp] theorem fourPrimeSquarekillSign_add_period (n : ℕ) :
    fourPrimeSquarekillSign (n + fourPrimeSquarekillPeriod) =
      fourPrimeSquarekillSign n := by
  unfold fourPrimeSquarekillSign
  rw [Nat.add_mod_right]

@[simp] theorem fourPrimeSquarekillSign_zero : fourPrimeSquarekillSign 0 = 0 := by
  norm_num [fourPrimeSquarekillSign, fourPrimeSquarekillPeriod]

/-- Finite CRT census: the actual four-prime square-killing wheel has
14976 positive, 12672 negative, and 16452 zero sites per 44100 residues.
Its net signed mass is 2304, unlike the parity-only zero-mean wheel. -/
theorem fourPrimeSquarekill_completePeriod :
    (∑ n ∈ Finset.range fourPrimeSquarekillPeriod,
      fourPrimeSquarekillSign n) = 2304 := by
  native_decide

/-- Multiplicative prefactor on a coherent linear cofactor mode. The
factor 8/35 is strictly positive, so the four-prime cube does not annihilate
linear growth merely because its unweighted corner sum vanishes. -/
theorem fourPrimeReciprocalLinearFactor :
    ((1 : ℚ) - 1 / 2) * (1 - 1 / 3) *
      (1 - 1 / 5) * (1 - 1 / 7) = 8 / 35 := by
  norm_num

/-- A general finite periodic sum on k complete cells. -/
private theorem sum_period_mul
    (P k : ℕ) (f : ℕ → ℤ)
    (hperiod : HasWheelPeriod P f) :
    (∑ n ∈ Finset.range (k * P), f n) =
      (k : ℤ) * (∑ n ∈ Finset.range P, f n) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih]
    have hcell :
        (∑ n ∈ Finset.range P, f (k * P + n)) =
          ∑ n ∈ Finset.range P, f n := by
      apply Finset.sum_congr rfl
      intro n _hn
      exact wheel_period_mul hperiod k n
    rw [hcell]
    push_cast
    ring

/-- Exact noncancellation on an infinite family of physical square blocks.
The root 44100*t starts at phase 0 and traverses 2*t whole 44100-periods
plus the zero residue. Hence the signed mass grows linearly with t. -/
theorem fourPrimeSquarekill_squareBlock_at_periodRoot (t : ℕ) :
    (∑ j ∈ Finset.range (2 * (fourPrimeSquarekillPeriod * t) + 1),
      fourPrimeSquarekillSign
        ((fourPrimeSquarekillPeriod * t) ^ 2 + j)) =
      (4608 : ℤ) * (t : ℤ) := by
  let P : ℕ := fourPrimeSquarekillPeriod
  have hp : HasWheelPeriod P fourPrimeSquarekillSign := by
    intro n
    exact fourPrimeSquarekillSign_add_period n
  have hshift (j : ℕ) :
      fourPrimeSquarekillSign ((P * t) ^ 2 + j) =
        fourPrimeSquarekillSign j := by
    have h := wheel_period_mul hp (P * t * t) j
    have he : (P * t) ^ 2 + j = (P * t * t) * P + j := by ring
    rw [he]
    exact h
  have hlen : 2 * (P * t) + 1 = (2 * t) * P + 1 := by ring
  have hcell :
      (∑ j ∈ Finset.range P, fourPrimeSquarekillSign j) = 2304 :=
    fourPrimeSquarekill_completePeriod
  have hzero : fourPrimeSquarekillSign ((2 * t) * P) = 0 := by
    have h := wheel_period_mul hp (2 * t) 0
    simpa using h
  calc
    (∑ j ∈ Finset.range (2 * (P * t) + 1),
        fourPrimeSquarekillSign ((P * t) ^ 2 + j)) =
      ∑ j ∈ Finset.range ((2 * t) * P + 1),
        fourPrimeSquarekillSign j := by
          rw [hlen]
          apply Finset.sum_congr rfl
          intro j _hj
          exact hshift j
    _ = (2 * t : ℤ) *
          (∑ j ∈ Finset.range P, fourPrimeSquarekillSign j) +
        fourPrimeSquarekillSign ((2 * t) * P) := by
          rw [Finset.sum_range_succ, sum_period_mul P (2 * t) fourPrimeSquarekillSign hp]
          push_cast
          ring
    _ = (4608 : ℤ) * (t : ℤ) := by
          rw [hcell, hzero]
          ring

/-- The complete four-prime physical model has positive square-block drift
on infinitely many exactly specified square-root scales. -/
theorem fourPrimeSquarekill_squareBlock_at_periodRoot_pos
    (t : ℕ) (ht : 0 < t) :
    0 < (∑ j ∈ Finset.range (2 * (fourPrimeSquarekillPeriod * t) + 1),
      fourPrimeSquarekillSign
        ((fourPrimeSquarekillPeriod * t) ^ 2 + j)) := by
  rw [fourPrimeSquarekill_squareBlock_at_periodRoot]
  have htz : (0 : ℤ) < (t : ℤ) := by exact_mod_cast ht
  positivity

end RHLean.Arithmetic
