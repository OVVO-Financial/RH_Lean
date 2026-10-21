import «research.MERTENS_FINITE_PREFIX_EXTENSION»

/-!
# Signed higher-order finite Mobius inversion

The finite geometric expansion is the Mobius version of the
Heath-Brown/Vaughan identity. All products below are Dirichlet convolutions.
Support precision improves from B to B^k. No summatory norm preservation,
Type II estimate, probabilistic independence, or RH conclusion is asserted.
-/

noncomputable section
namespace RHLean.Analysis.MertensFiniteExtension
open ArithmeticFunction

/-- The defect is the genuine coefficient tail convolved with the ones function. -/
theorem inverseDefect_eq_tail_mul (a : ArithmeticFunction Int) :
    inverseDefect a = (ArithmeticFunction.moebius - a) * zetaInt := by
  have hmu : ArithmeticFunction.moebius * zetaInt = 1 :=
    ArithmeticFunction.moebius_mul_coe_zeta
  rw [sub_mul, hmu]
  rfl

theorem inverseDefect_mul_moebius (a : ArithmeticFunction Int) :
    inverseDefect a * ArithmeticFunction.moebius = ArithmeticFunction.moebius - a := by
  have hmu : zetaInt * ArithmeticFunction.moebius = 1 :=
    ArithmeticFunction.coe_zeta_mul_moebius
  unfold inverseDefect
  rw [sub_mul, one_mul, mul_assoc, hmu, mul_one]

/-- Finite signed geometric expansion, requiring no infinite-series convergence. -/
def heathBrownLift (a : ArithmeticFunction Int) : Nat -> ArithmeticFunction Int
  | 0 => 0
  | k + 1 => a + inverseDefect a * heathBrownLift a k

/-- Every truncation has its exact signed remainder against genuine Mobius. -/
theorem heathBrownLift_error (a : ArithmeticFunction Int) (k : Nat) :
    ArithmeticFunction.moebius - heathBrownLift a k =
      ArithmeticFunction.moebius * inverseDefect a ^ k := by
  induction k with
  | zero => simp [heathBrownLift]
  | succ k ih =>
    calc
      ArithmeticFunction.moebius - heathBrownLift a (k + 1) =
          inverseDefect a * (ArithmeticFunction.moebius - heathBrownLift a k) := by
            rw [heathBrownLift, mul_sub, inverseDefect_mul_moebius]
            ring
      _ = ArithmeticFunction.moebius * inverseDefect a ^ (k + 1) := by
        rw [ih, pow_succ]
        ring

/-- The inverse defect is the kth convolution power of the original defect. -/
theorem inverseDefect_heathBrownLift (a : ArithmeticFunction Int) (k : Nat) :
    inverseDefect (heathBrownLift a k) = inverseDefect a ^ k := by
  have hmu : ArithmeticFunction.moebius * zetaInt = 1 :=
    ArithmeticFunction.moebius_mul_coe_zeta
  rw [inverseDefect_eq_tail_mul, heathBrownLift_error, mul_right_comm, hmu, one_mul]

/-- The recursive form equals the finite geometric sum. -/
theorem heathBrownLift_eq_geometric (a : ArithmeticFunction Int) (k : Nat) :
    heathBrownLift a k =
      a * Finset.sum (Finset.range k) (fun j => inverseDefect a ^ j) := by
  induction k with
  | zero => simp [heathBrownLift]
  | succ k ih =>
    rw [heathBrownLift, ih, Finset.sum_range_succ']
    simp only [pow_zero, pow_succ']
    rw [← Finset.mul_sum]
    ring

/-- The previous Newton map is exactly the second-order signed lift. -/
theorem heathBrownLift_two (a : ArithmeticFunction Int) :
    heathBrownLift a 2 = newtonLift a := by
  simp only [heathBrownLift, mul_zero, add_zero]
  unfold inverseDefect newtonLift
  ring

/-- Cubic binomial form; the alternating terms must remain signed. -/
theorem heathBrownLift_three (a : ArithmeticFunction Int) :
    heathBrownLift a 3 =
      3 * a - 3 * a ^ 2 * zetaInt + a ^ 3 * zetaInt ^ 2 := by
  simp only [heathBrownLift, mul_zero, add_zero]
  unfold inverseDefect
  ring

/-- Fourth-order form, retaining all cross-family cancellation. -/
theorem heathBrownLift_four (a : ArithmeticFunction Int) :
    heathBrownLift a 4 = 4 * a - 6 * a ^ 2 * zetaInt +
      4 * a ^ 3 * zetaInt ^ 2 - a ^ 4 * zetaInt ^ 3 := by
  simp only [heathBrownLift, mul_zero, add_zero]
  unfold inverseDefect
  ring

/-- Every arithmetic function vanishes below the positive-integer origin. -/
private theorem arithmetic_zero_below_one (f : ArithmeticFunction Int) :
    forall n : Nat, n < 1 -> f n = 0 := by
  intro n hn
  have hn0 : n = 0 := by omega
  subst n
  simp

/-- Vanishing support, not a norm contraction, explains the improved cutoff. -/
theorem inverseDefect_zero_below {B : Nat} {a : ArithmeticFunction Int}
    (ha : AgreeBelow B a ArithmeticFunction.moebius) :
    forall n : Nat, n < B -> inverseDefect a n = 0 := by
  intro n hn
  rw [inverseDefect_eq_tail_mul]
  apply mul_zero_below (A := B) (B := 1)
    (g := zetaInt) _ (arithmetic_zero_below_one zetaInt) (by simpa using! hn)
  intro m hm
  change ArithmeticFunction.moebius m - a m = 0
  rw [ha m hm, sub_self]

theorem convolution_pow_zero_below {B : Nat} {f : ArithmeticFunction Int}
    (hf : forall n : Nat, n < B -> f n = 0) (k : Nat) :
    forall n : Nat, n < B ^ k -> (f ^ k) n = 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    intro n hn
    rw [pow_succ]
    exact mul_zero_below ih hf (by simpa only [pow_succ] using! hn)

/-- A genuine finite coefficient prefix extends to arbitrary integral power precision. -/
theorem heathBrownLift_agrees_below_power {B : Nat} {a : ArithmeticFunction Int}
    (ha : AgreeBelow B a ArithmeticFunction.moebius) (k : Nat) :
    AgreeBelow (B ^ k) (heathBrownLift a k) ArithmeticFunction.moebius := by
  intro n hn
  have hz : (ArithmeticFunction.moebius * inverseDefect a ^ k) n = 0 :=
    mul_zero_below (A := 1) (B := B ^ k)
      (arithmetic_zero_below_one ArithmeticFunction.moebius)
      (convolution_pow_zero_below (inverseDefect_zero_below ha) k) (by simpa using! hn)
  have he := congrArg (fun f : ArithmeticFunction Int => f n) (heathBrownLift_error a k)
  change ArithmeticFunction.moebius n - heathBrownLift a k n =
    (ArithmeticFunction.moebius * inverseDefect a ^ k) n at he
  rw [hz] at he
  exact (sub_eq_zero.mp he).symm

theorem heathBrownLift_prefix_exact {N n k : Nat} (hn : n < (N + 1) ^ k) :
    heathBrownLift (mobiusPrefix N) k n = ArithmeticFunction.moebius n :=
  heathBrownLift_agrees_below_power (mobiusPrefix_agrees N) k n hn

/-- The defect of a nonempty prefix has value zero at one, not the unit value
required by a nonzero multiplicative function in Halasz's theorem. -/
theorem inverseDefect_prefix_one {N : Nat} (hN : 1 <= N) :
    inverseDefect (mobiusPrefix N) 1 = 0 := by
  change (1 : ArithmeticFunction Int) 1 - (mobiusPrefix N * zetaInt) 1 = 0
  rw [ArithmeticFunction.mul_apply_one]
  simp [mobiusPrefix, zetaInt, hN]

/-- Two unprocessed prime defects reinforce rather than cancel in each product. -/
theorem fresh_prime_defect_product {N p q : Nat} (hN : 1 <= N)
    (hp : p.Prime) (hq : q.Prime) (hNp : N < p) (hNq : N < q) :
    inverseDefect (mobiusPrefix N) p * inverseDefect (mobiusPrefix N) q = 1 := by
  rw [inverseDefect_prefix_prime hN hp hNp, inverseDefect_prefix_prime hN hq hNq]
  norm_num

end RHLean.Analysis.MertensFiniteExtension
