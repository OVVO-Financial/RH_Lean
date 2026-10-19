import Mathlib
import RHLean.Analysis.SquarePrefixMertensBridge

/-!
# Exact finite-prefix extension for the genuine Mobius function

The Newton map in the Dirichlet convolution ring squares the support cutoff
of its error. This proves exact arithmetic extension from finite data. It
DOES NOT prove preservation of a sublinear Mertens envelope. The separate
window theorem turns a checked anchor budget into an actual interval bound.
-/

noncomputable section
namespace RHLean.Analysis.MertensFiniteExtension

open ArithmeticFunction

def zetaInt : ArithmeticFunction Int := ArithmeticFunction.zeta

def newtonLift (a : ArithmeticFunction Int) : ArithmeticFunction Int :=
  a + a - a * a * zetaInt

def inverseDefect (a : ArithmeticFunction Int) : ArithmeticFunction Int :=
  1 - a * zetaInt

def AgreeBelow (B : Nat) (a b : ArithmeticFunction Int) : Prop :=
  forall n : Nat, n < B -> a n = b n

/-- The inverse defect squares exactly. No norm estimate is asserted. -/
theorem inverseDefect_newtonLift (a : ArithmeticFunction Int) :
    inverseDefect (newtonLift a) = inverseDefect a * inverseDefect a := by
  unfold inverseDefect newtonLift
  ring

/-- Exact signed error against the actual inverse of the zeta coefficients. -/
theorem newtonLift_eq_moebius_sub_tail (a : ArithmeticFunction Int) :
    newtonLift a = ArithmeticFunction.moebius -
      (ArithmeticFunction.moebius - a) * (ArithmeticFunction.moebius - a) * zetaInt := by
  have hmu : ArithmeticFunction.moebius * zetaInt = 1 :=
    ArithmeticFunction.moebius_mul_coe_zeta
  have huu : ArithmeticFunction.moebius * ArithmeticFunction.moebius * zetaInt =
      ArithmeticFunction.moebius := by rw [mul_assoc, hmu, mul_one]
  have hua : ArithmeticFunction.moebius * a * zetaInt = a := by
    rw [mul_right_comm, hmu, one_mul]
  unfold newtonLift
  calc
    a + a - a * a * zetaInt = ArithmeticFunction.moebius -
        (ArithmeticFunction.moebius * ArithmeticFunction.moebius * zetaInt -
        (ArithmeticFunction.moebius * a * zetaInt +
          ArithmeticFunction.moebius * a * zetaInt) + a * a * zetaInt) := by
          rw [huu, hua]
          ring
    _ = _ := by ring

/-- Multiplicative support cutoffs multiply under Dirichlet convolution. -/
theorem mul_zero_below {A B : Nat} {f g : ArithmeticFunction Int}
    (hf : forall n : Nat, n < A -> f n = 0)
    (hg : forall n : Nat, n < B -> g n = 0)
    {n : Nat} (hn : n < A * B) : (f * g) n = 0 := by
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro d hd
  have hp : d.1 * d.2 = n := (Nat.mem_divisorsAntidiagonal.mp hd).1
  by_cases hsmall : d.1 < A
  · rw [hf d.1 hsmall, zero_mul]
  · have hright : d.2 < B := by
      by_contra hnot
      have hprod := Nat.mul_le_mul (Nat.le_of_not_gt hsmall) (Nat.le_of_not_gt hnot)
      omega
    rw [hg d.2 hright, mul_zero]

/-- Correct coefficients below B produce correct coefficients below B squared.
Only the stated finite initial agreement is required. -/
theorem newtonLift_agrees_below_square {B : Nat} {a : ArithmeticFunction Int}
    (ha : AgreeBelow B a ArithmeticFunction.moebius) :
    AgreeBelow (B * B) (newtonLift a) ArithmeticFunction.moebius := by
  intro n hn
  have ht : forall k : Nat, k < B -> (ArithmeticFunction.moebius - a) k = 0 := by
    intro k hk
    change ArithmeticFunction.moebius k - a k = 0
    rw [ha k hk, sub_self]
  have htwo : forall k : Nat, k < B * B ->
      ((ArithmeticFunction.moebius - a) * (ArithmeticFunction.moebius - a)) k = 0 :=
    fun _ hk => mul_zero_below ht ht hk
  have hz : forall k : Nat, k < 1 -> zetaInt k = 0 := by
    intro k hk
    have hk0 : k = 0 := by omega
    subst k
    simp
  have hthree := mul_zero_below htwo hz (by simpa using! hn)
  rw [newtonLift_eq_moebius_sub_tail]
  change ArithmeticFunction.moebius n -
    ((ArithmeticFunction.moebius - a) * (ArithmeticFunction.moebius - a) * zetaInt) n =
      ArithmeticFunction.moebius n
  rw [hthree, sub_zero]

/-- The extended coefficients retain the genuine Mobius coefficient bound. -/
theorem newtonLift_abs_le_one {B n : Nat} {a : ArithmeticFunction Int}
    (ha : AgreeBelow B a ArithmeticFunction.moebius) (hn : n < B * B) :
    abs (newtonLift a n) <= 1 := by
  rw [newtonLift_agrees_below_square ha n hn]
  exact ArithmeticFunction.abs_moebius_le_one

/-- Truncation is used only to package a supplied finite Mobius prefix. -/
def mobiusPrefix (N : Nat) : ArithmeticFunction Int :=
  { toFun := fun n => if n <= N then ArithmeticFunction.moebius n else 0
    map_zero' := by simp }

theorem mobiusPrefix_agrees (N : Nat) :
    AgreeBelow (N + 1) (mobiusPrefix N) ArithmeticFunction.moebius := by
  intro n hn
  simp [mobiusPrefix, Nat.lt_succ_iff.mp hn]

/-- A prefix through N reconstructs every coefficient through (N+1)^2-1. -/
theorem newtonLift_prefix_exact {N n : Nat} (hn : n < (N + 1) * (N + 1)) :
    newtonLift (mobiusPrefix N) n = ArithmeticFunction.moebius n :=
  newtonLift_agrees_below_square (mobiusPrefix_agrees N) n hn

/-- Pure arithmetic iteration starting with the single unit coefficient. -/
def newtonIterates : Nat -> ArithmeticFunction Int
  | 0 => 1
  | j + 1 => newtonLift (newtonIterates j)

def precisionCutoff : Nat -> Nat
  | 0 => 2
  | j + 1 => precisionCutoff j * precisionCutoff j

theorem precisionCutoff_eq_pow (j : Nat) : precisionCutoff j = 2 ^ (2 ^ j) := by
  induction j with
  | zero => norm_num [precisionCutoff]
  | succ j ih =>
    rw [precisionCutoff, ih, <- pow_add]
    congr 1
    rw [pow_succ]
    omega

theorem newtonIterates_agree (j : Nat) :
    AgreeBelow (precisionCutoff j) (newtonIterates j) ArithmeticFunction.moebius := by
  induction j with
  | zero =>
    intro n hn
    have hn2 : n < 2 := hn
    interval_cases n <;> simp [newtonIterates]
  | succ j ih => exact newtonLift_agrees_below_square ih

theorem precisionCutoff_ge (j : Nat) : j + 2 <= precisionCutoff j := by
  induction j with
  | zero => norm_num [precisionCutoff]
  | succ j ih =>
    have hc : 2 <= precisionCutoff j := by omega
    simp only [precisionCutoff]
    nlinarith

/-- Every actual coefficient is obtained after finitely many seed-only lifts.
This is arithmetic reconstruction, not a uniform summatory growth bound. -/
theorem newtonIterates_coefficient (n : Nat) :
    newtonIterates n n = ArithmeticFunction.moebius n :=
  newtonIterates_agree n n (by have h := precisionCutoff_ge n; omega)

def liftSummatory (a : ArithmeticFunction Int) (n : Nat) : Complex :=
  Finset.sum (Finset.range (n + 1)) (fun k => ((newtonLift a k : Int) : Complex))

theorem liftSummatory_eq_mertens {B n : Nat} {a : ArithmeticFunction Int}
    (ha : AgreeBelow B a ArithmeticFunction.moebius) (hn : n < B * B) :
    liftSummatory a n = mertensSummatory n := by
  unfold liftSummatory mertensSummatory
  apply Finset.sum_congr rfl
  intro k hk
  have hklt : k < B * B := by have hk' := Finset.mem_range.mp hk; omega
  rw [newtonLift_agrees_below_square ha k hklt]

/-- A finite anchor budget certifies a whole new interval, including points
past the exact reconstruction cutoff when the available margin permits it.
The budget is evaluated from the supplied prefix; no future Mertens bound is
an input. -/
theorem guarded_interval_extension {B L U : Nat} {a : ArithmeticFunction Int}
    {C sigma : Real} (ha : AgreeBelow B a ArithmeticFunction.moebius)
    (hL : L < B * B) (hC : 0 <= C) (hsigma : 0 <= sigma)
    (hbudget : norm (liftSummatory a L) + ((U - L : Nat) : Real) <=
      C * (L : Real) ^ sigma) :
    forall x : Nat, L <= x -> x <= U ->
      norm (mertensSummatory x) <= C * (x : Real) ^ sigma := by
  intro x hLx hxU
  have hgap : ((x - L : Nat) : Real) <= ((U - L : Nat) : Real) := by
    exact_mod_cast Nat.sub_le_sub_right hxU L
  calc
    norm (mertensSummatory x) = norm (mertensSummatory L +
        (mertensSummatory x - mertensSummatory L)) := by congr 1; ring
    _ <= norm (mertensSummatory L) +
        norm (mertensSummatory x - mertensSummatory L) := norm_add_le _ _
    _ <= norm (mertensSummatory L) + ((x - L : Nat) : Real) :=
      add_le_add_right (norm_mertensSummatory_sub_le L x hLx) _
    _ = norm (liftSummatory a L) + ((x - L : Nat) : Real) := by
      rw [liftSummatory_eq_mertens ha hL]
    _ <= norm (liftSummatory a L) + ((U - L : Nat) : Real) := add_le_add_right hgap _
    _ <= C * (L : Real) ^ sigma := hbudget
    _ <= C * (x : Real) ^ sigma := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg L) (by exact_mod_cast hLx) hsigma) hC

/-- The raw absolute defect has unit coefficients at every unprocessed prime.
This obstructs an absolute weighted-l1 contraction below exponent one. -/
theorem inverseDefect_prefix_prime {N p : Nat}
    (hN : 1 <= N) (hp : p.Prime) (hNp : N < p) :
    inverseDefect (mobiusPrefix N) p = -1 := by
  have hsum : Finset.sum p.divisors (mobiusPrefix N) = (1 : Int) := by
    have h := Nat.sum_divisors_prime_pow (k := 1) (f := mobiusPrefix N) hp
    simpa [Finset.sum_range_succ, mobiusPrefix, hN, hNp.not_ge] using! h
  unfold inverseDefect
  change (1 : ArithmeticFunction Int) p - (mobiusPrefix N * zetaInt) p = -1
  rw [ArithmeticFunction.one_apply_ne hp.ne_one]
  change 0 - (mobiusPrefix N * (ArithmeticFunction.zeta : ArithmeticFunction Int)) p = -1
  rw [ArithmeticFunction.coe_mul_zeta_apply, hsum]
  norm_num

end RHLean.Analysis.MertensFiniteExtension
