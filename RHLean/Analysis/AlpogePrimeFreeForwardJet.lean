import Mathlib

/-!
# Prime-free forward jets: cancellation and the sharp coefficient cost

This module extracts the exact sequence operator and generic proofs from
`AlpogeSquareRootArithmeticMultiplicity`, preserving their declaration names.
Its only import is Mathlib. The arithmetic module imports this same operator.

The alternating integral sequence has zero sum on every even-length window,
while its order-k forward jet has absolute value exactly 2^k at every site.
Thus cancellation of the original window sum does not bound the high jet.
These are finite sequence statements, with no prime or RH hypotheses.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

/-- Order-k exact integer-clock arithmetic jet: Δ^k f(n).
Unlike a formal p-adic derivative, it operates on actual sequence values. -/
def alpogeNativeForwardJet (f : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, n => f n
  | k + 1, n =>
      alpogeNativeForwardJet f k (n + 1) -
        alpogeNativeForwardJet f k n

@[simp] theorem alpogeNativeForwardJet_zero
    (f : ℕ → ℝ) (n : ℕ) :
    alpogeNativeForwardJet f 0 n = f n := rfl

theorem alpogeNativeForwardJet_succ
    (f : ℕ → ℝ) (k n : ℕ) :
    alpogeNativeForwardJet f (k + 1) n =
      alpogeNativeForwardJet f k (n + 1) -
        alpogeNativeForwardJet f k n := rfl

/-- The k-th arithmetic jet of a first difference is literally the
(k+1)-st jet. No external asymptotics or random sign model. -/
theorem alpogeNativeForwardJet_succ_as_difference
    (f : ℕ → ℝ) (k n : ℕ) :
    alpogeNativeForwardJet f (k + 1) n =
      alpogeNativeForwardJet
        (fun t => f (t + 1) - f t) k n := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
      calc
        alpogeNativeForwardJet f ((k + 1) + 1) n =
          alpogeNativeForwardJet f (k + 1) (n + 1) -
            alpogeNativeForwardJet f (k + 1) n := rfl
        _ =
          alpogeNativeForwardJet (fun t => f (t + 1) - f t) k (n + 1) -
            alpogeNativeForwardJet (fun t => f (t + 1) - f t) k n := by
              rw [ih (n + 1), ih n]
        _ = alpogeNativeForwardJet
          (fun t => f (t + 1) - f t) (k + 1) n := rfl

/-- A constant is annihilated by every positive arithmetic jet. -/
theorem alpogeNativeForwardJet_const_succ
    (c : ℝ) (k n : ℕ) :
    alpogeNativeForwardJet (fun _ : ℕ => c) (k + 1) n = 0 := by
  induction k generalizing n with
  | zero => simp [alpogeNativeForwardJet]
  | succ k ih =>
      rw [alpogeNativeForwardJet_succ, ih (n + 1), ih n]
      ring

/-- The usual linear drift has an actual order-two zero. -/
theorem alpogeNativeForwardJet_linear_two (n : ℕ) :
    alpogeNativeForwardJet (fun t : ℕ => (t : ℝ)) 2 n = 0 := by
  change ((((n + 2 : ℕ) : ℝ) - ((n + 1 : ℕ) : ℝ)) -
    (((n + 1 : ℕ) : ℝ) - (n : ℝ))) = 0
  push_cast
  ring

/-- Raising the jet order cannot restore an affine signal. -/
theorem alpogeNativeForwardJet_linear_high (k n : ℕ) :
    alpogeNativeForwardJet
      (fun t : ℕ => (t : ℝ)) (k + 2) n = 0 := by
  induction k generalizing n with
  | zero => exact alpogeNativeForwardJet_linear_two n
  | succ k ih =>
      change
        alpogeNativeForwardJet (fun t : ℕ => (t : ℝ))
          (k + 2) (n + 1) -
          alpogeNativeForwardJet (fun t : ℕ => (t : ℝ))
            (k + 2) n = 0
      rw [ih (n + 1), ih n]
      ring

/-- Differencing an already-centered signal never pays another
constant: the next jet removes it EXACTLY. -/
theorem alpogeNativeForwardJet_sub_const_succ
    (f : ℕ → ℝ) (c : ℝ) (k n : ℕ) :
    alpogeNativeForwardJet (fun t => f t - c) (k + 1) n =
      alpogeNativeForwardJet f (k + 1) n := by
  rw [alpogeNativeForwardJet_succ_as_difference,
      alpogeNativeForwardJet_succ_as_difference]
  have h :
      (fun t : ℕ => (f (t + 1) - c) - (f t - c)) =
      (fun t : ℕ => f (t + 1) - f t) := by
    funext t
    ring
  rw [h]

/-- The upper bound on a single high jet grows by TWO PER ORDER.
This accounts for the coefficient-height price before any prime
cancellation theorem is invoked. -/
theorem alpogeNativeForwardJet_abs_le_exp
    (f : ℕ → ℝ) (M : ℝ)
    (hM : ∀ n, |f n| ≤ M) (k n : ℕ) :
    |alpogeNativeForwardJet f k n| ≤ (2 : ℝ) ^ k * M := by
  induction k generalizing n with
  | zero =>
      simpa only [alpogeNativeForwardJet_zero, pow_zero, one_mul]
        using hM n
  | succ k ih =>
      calc
        |alpogeNativeForwardJet f (k + 1) n| =
            |alpogeNativeForwardJet f k (n + 1) -
              alpogeNativeForwardJet f k n| := rfl
        _ ≤ |alpogeNativeForwardJet f k (n + 1)| +
              |alpogeNativeForwardJet f k n| := abs_sub _ _
        _ ≤ (2 : ℝ) ^ k * M + (2 : ℝ) ^ k * M :=
          add_le_add (ih (n + 1)) (ih n)
        _ = (2 : ℝ) ^ (k + 1) * M := by
          rw [pow_succ]
          ring

/-- The test field realizing the FULL coefficient-height loss. -/
def alpogeNativeAlternatingSignal (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n

@[simp] theorem alpogeNativeAlternatingSignal_succ (n : ℕ) :
    alpogeNativeAlternatingSignal (n + 1) =
      -alpogeNativeAlternatingSignal n := by
  simp [alpogeNativeAlternatingSignal, pow_succ]

/-- The sharp −2 spectral multiplier: no power-saving operator
bound can follow from the abstract R-step jet algebra alone. -/
theorem alpogeNativeForwardJet_alternating
    (k n : ℕ) :
    alpogeNativeForwardJet alpogeNativeAlternatingSignal k n =
      (-2 : ℝ) ^ k * alpogeNativeAlternatingSignal n := by
  induction k generalizing n with
  | zero => simp [alpogeNativeForwardJet]
  | succ k ih =>
      calc
        alpogeNativeForwardJet alpogeNativeAlternatingSignal (k + 1) n =
          alpogeNativeForwardJet alpogeNativeAlternatingSignal k (n + 1) -
            alpogeNativeForwardJet alpogeNativeAlternatingSignal k n := rfl
        _ = (-2 : ℝ) ^ k * alpogeNativeAlternatingSignal (n + 1) -
              (-2 : ℝ) ^ k * alpogeNativeAlternatingSignal n := by
                rw [ih (n + 1), ih n]
        _ = (-2 : ℝ) ^ (k + 1) * alpogeNativeAlternatingSignal n := by
            rw [alpogeNativeAlternatingSignal_succ, pow_succ]
            ring

/-- The exponential price is SHARP even for bounded integral values
(plus and minus one). -/
theorem alpogeNativeForwardJet_alternating_abs
    (k n : ℕ) :
    |alpogeNativeForwardJet alpogeNativeAlternatingSignal k n| =
      (2 : ℝ) ^ k := by
  rw [alpogeNativeForwardJet_alternating]
  simp [alpogeNativeAlternatingSignal, abs_mul]

/-- EXACT square-clock specialization: order R at X_R=R^2-1. -/
def alpogeSquareRootArithmeticJet (f : ℕ → ℝ) (R : ℕ) : ℝ :=
  alpogeNativeForwardJet f R (R ^ 2 - 1)

/-- The best possible UNIFORM bound for the purely arithmetic jet
is exponential in R, far exceeding the root-scale polynomial budget. -/
theorem alpogeSquareRootArithmeticJet_sharp
    (R : ℕ) :
    |alpogeSquareRootArithmeticJet alpogeNativeAlternatingSignal R| =
      (2 : ℝ) ^ R := by
  exact alpogeNativeForwardJet_alternating_abs R (R ^ 2 - 1)

/-- A two-site signed window cancels exactly. -/
theorem alpogeNativeAlternatingSignal_pair_sum (n : ℕ) :
    alpogeNativeAlternatingSignal n +
      alpogeNativeAlternatingSignal (n + 1) = 0 := by
  rw [alpogeNativeAlternatingSignal_succ, add_neg_cancel]

/-- Every even-length window has zero signed sum, although the same
sequence attains the sharp 2^k jet bound at every starting site. -/
theorem alpogeNativeAlternatingSignal_even_window (M n : ℕ) :
    (∑ j ∈ Finset.range (2 * M),
      alpogeNativeAlternatingSignal (n + j)) = 0 := by
  induction M with
  | zero => simp
  | succ M ih =>
      have hlen : 2 * (M + 1) = (2 * M + 1) + 1 := by omega
      rw [hlen, Finset.sum_range_succ, Finset.sum_range_succ, ih, zero_add]
      simpa only [Nat.add_assoc] using
        alpogeNativeAlternatingSignal_pair_sum (n + 2 * M)

end RHLean.Analysis

/-! ## Explicit kernel axiom audit: expected only standard Lean axioms. -/
#print axioms RHLean.Analysis.alpogeNativeForwardJet_abs_le_exp
#print axioms RHLean.Analysis.alpogeSquareRootArithmeticJet_sharp
#print axioms RHLean.Analysis.alpogeNativeAlternatingSignal_even_window
