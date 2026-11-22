import Mathlib
import RHLean.Arithmetic.PrimeCombFiniteDifferenceFreshPrime
import RHLean.Analysis.NativePNTErdosContraction
import RHLean.Analysis.AlpogeNativeSharpASKBalance

/-!
# A genuine square-root-length arithmetic jet, tested against Alpoge multiplicity

At X_R = R^2 - 1 the R-th forward difference fits into the square
lattice with an actual integer clock. It is an EXACT R-step arithmetic
operator. This module tests the tempting claim that this R automatically
provides Alpoge's geometric multiplicity m ~ sqrt(X).

The result is more discriminating: the jet annihilates linear drift,
and its second derivative on the native Chebyshev error equals the
ACTUAL von Mangoldt prime-power difference. However, the universal
operator norm of the R-th jet is exactly 2^R, witnessed by an explicit
alternating integral signal. Neither R steps nor a Boolean fresh-prime
difference therefore automatically supplies a paid p-adic multiplicity
or a square-root bound. No RH statement or unproved geometric cost is
imported.
-/

noncomputable section
open scoped ArithmeticFunction.vonMangoldt BigOperators

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

/-- The actual prime signal appears in the FIRST forward difference
of the native Chebyshev error, without discarding prime powers. -/
theorem alpogeNativeForwardJet_error_one (n : ℕ) :
    alpogeNativeForwardJet nativePNTError 1 n =
      Λ (n + 1) - 1 := by
  simpa only [alpogeNativeForwardJet_succ, alpogeNativeForwardJet_zero]
    using nativePNTError_succ_eq n

/-- A second derivative is an EXACT prime-power impulse difference,
not an assumed saving or a claim of p-adic divisibility. -/
theorem alpogeNativeForwardJet_error_two (n : ℕ) :
    alpogeNativeForwardJet nativePNTError 2 n =
      Λ (n + 2) - Λ (n + 1) := by
  change
    (nativePNTError (n + 2) - nativePNTError (n + 1)) -
      (nativePNTError (n + 1) - nativePNTError n) =
        Λ (n + 2) - Λ (n + 1)
  have hnext := nativePNTError_succ_eq (n + 1)
  have hprev := nativePNTError_succ_eq n
  have heq : n + 1 + 1 = n + 2 := by omega
  rw [heq] at hnext
  linarith

/-- At every order, the first jet of the true Chebyshev error is
the same genuine arithmetic Λ signal with the unit drift paid. -/
theorem alpogeNativeForwardJet_error_as_prime_difference
    (k n : ℕ) :
    alpogeNativeForwardJet nativePNTError (k + 1) n =
      alpogeNativeForwardJet
        (fun t => Λ (t + 1) - 1) k n := by
  have hpoint :
      (fun t : ℕ => nativePNTError (t + 1) - nativePNTError t) =
      (fun t : ℕ => Λ (t + 1) - 1) := by
    funext t
    exact nativePNTError_succ_eq t
  rw [alpogeNativeForwardJet_succ_as_difference, hpoint]

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

/-- At every order at least two, the high Chebyshev jet consists
ONLY of the actual prime-power impulses. -/
theorem alpogeNativeForwardJet_error_high
    (k n : ℕ) :
    alpogeNativeForwardJet nativePNTError (k + 2) n =
      alpogeNativeForwardJet
        (fun t => Λ (t + 1)) (k + 1) n := by
  calc
    alpogeNativeForwardJet nativePNTError (k + 2) n =
      alpogeNativeForwardJet
        (fun t => Λ (t + 1) - 1) (k + 1) n := by
          simpa only [show k + 2 = (k + 1) + 1 by omega]
            using alpogeNativeForwardJet_error_as_prime_difference (k + 1) n
    _ = alpogeNativeForwardJet
        (fun t => Λ (t + 1)) (k + 1) n :=
          alpogeNativeForwardJet_sub_const_succ
            (fun t => Λ (t + 1)) 1 k n

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

/-- One prime coordinate already shows the Boolean multiplicity trap:
D_{\{7\}} applied to the original linear sequence at 7 gives 6,
which carries ZERO 7-adic divisibility. -/
theorem alpogeNativePrimeSevenDifference_linear :
    RHLean.Arithmetic.finiteDifferenceOperator
      ({7} : Finset ℕ) (fun n : ℕ => (n : ℤ)) 7 = 6 := by
  rw [RHLean.Arithmetic.finiteDifferenceOperator_singleton
      7 (by norm_num : Nat.Prime 7) (fun n : ℕ => (n : ℤ))]
  norm_num [RHLean.Arithmetic.shift, Pi.sub_apply]

theorem alpogeNativePrimeSevenDifference_not_divisible :
    ¬ (7 : ℤ) ∣
      RHLean.Arithmetic.finiteDifferenceOperator
        ({7} : Finset ℕ) (fun n : ℕ => (n : ℤ)) 7 := by
  rw [alpogeNativePrimeSevenDifference_linear]
  norm_num


/-!
## The actual cross-representation correction: fresh-prime difference
does NOT commute with the Frobenius/inertia colour multiplier.

This is the finite algebraic coboundary that any attempted arithmetic
replacement for the theta-lift chain MUST retain. Rather than
postulating spectral cancellation, the term is carried in exactly
the same original prime-power and ASK width coordinates.
-/

/-- Exact integer-floor Leibniz rule, in EVERY commutative coefficient
ring: the defect is the change of c across the ORIGINAL p-quotient.
When c is the physical colour coefficient this is not negligible
for free, because Frobenius/inertia vary with the original integer. -/
theorem alpogeNativeFreshPrime_product_commutator
    {A : Type*} [CommRing A]
    (p n : ℕ) (c f : ℕ → A) :
    RHLean.Arithmetic.freshPrimeDifference p
      (fun k => c k * f k) n =
    c n * RHLean.Arithmetic.freshPrimeDifference p f n +
      (c n - c (n / p)) * f (n / p) := by
  simp only [RHLean.Arithmetic.freshPrimeDifference_apply]
  ring

/-- The precise condition for having NO cost when commuting the
fresh-prime derivative past the physical multiplier. This invariance
is NOT presumed for actual Frobenius/inertia coefficients. -/
theorem alpogeNativeFreshPrime_product_commute_of_invariant
    {A : Type*} [CommRing A]
    (p n : ℕ) (c f : ℕ → A)
    (h : c n = c (n / p)) :
    RHLean.Arithmetic.freshPrimeDifference p
      (fun k => c k * f k) n =
    c n * RHLean.Arithmetic.freshPrimeDifference p f n := by
  rw [alpogeNativeFreshPrime_product_commutator, h, sub_self,
      zero_mul, add_zero]

/-- An actual one-site source atom from the full, untruncated
Alpoge ASK, with every Lambda prime power and site-dependent
physical partner width retained. -/
def alpogeNativeLiteralASKSitePrimeAtom
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (a : ℝ) (t : H) (w : AlpogeNativeE0 × H → ℝ)
    (g : AlpogeNativeE0 × H) (n : ℕ) : ℂ :=
  ((Λ n : ℝ) : ℂ) * alpogeNativeSiteCut a w t n g

/-- Complete SOURCE-IDENTICAL Frobenius/inertia Leibniz defect.
Neither the character multiplier nor the quotient-terminal
prime-power source is replaced by its absolute value. In particular,
all ramified conductor zeros and their FULL return survive.

A true arithmetic m-lift mechanism would have to pay the cumulative
signed defect in this equation, plus the geometric lattice height.
The equation itself is unconditional. -/
theorem alpogeNativeLiteralASK_freshPrime_characterDefect
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (a : ℝ) (t : H) (w : AlpogeNativeE0 × H → ℝ)
    (g : AlpogeNativeE0 × H) (p n : ℕ) :
    RHLean.Arithmetic.freshPrimeDifference p
      (fun k => alpogeNativeColourKernel inertia frob k g *
        alpogeNativeLiteralASKSitePrimeAtom a t w g k) n =
    alpogeNativeColourKernel inertia frob n g *
      RHLean.Arithmetic.freshPrimeDifference p
        (alpogeNativeLiteralASKSitePrimeAtom a t w g) n +
      (alpogeNativeColourKernel inertia frob n g -
        alpogeNativeColourKernel inertia frob (n / p) g) *
        alpogeNativeLiteralASKSitePrimeAtom a t w g (n / p) := by
  exact alpogeNativeFreshPrime_product_commutator p n
    (fun k => alpogeNativeColourKernel inertia frob k g)
    (alpogeNativeLiteralASKSitePrimeAtom a t w g)


/-!
## Exact quotient-column multiplicity: a p-shift has p physical parents.

The TRUE floor shift n |-> floor(n/p) is p-to-one over a complete
positive quotient fibre, whereas Alpoge's geometric multiplicity
is a paid vanishing order. Their dimensions are not interchangeable.
-/

/-- Every full literal p-quotient fibre has exactly p integer sites.
This identifies a column-multiplicity tax that cannot be hidden in
an absolute-value estimate of the signed character defect. -/
theorem alpogeNativeFloorPrimeFiber_card (p m : ℕ) :
    (Finset.Ico (p * m) (p * (m + 1))).card = p := by
  rw [Nat.card_Ico]
  have h : p * (m + 1) = p * m + p := by ring
  rw [h]
  omega

/-- Every site in that complete p-fibre maps back to the SAME
original quotient: no free independence arises from p new sites. -/
theorem alpogeNativeFloorPrimeFiber_div
    (p m r : ℕ) (hp : 0 < p) (hr : r < p) :
    (p * m + r) / p = m := by
  rw [Nat.mul_add_div hp, Nat.div_eq_of_lt hr]
  omega


/-!
## New exact square-jet / prime-wheel mixed commutator

An additive step at the R^2 lattice and the Euler floor shift are
NOT interchangeable. The full signed compensation lives at the exact
floor-boundary of the multiplicative prime fibre, before passing to
any automorphic character or absolute-value majorant.
-/

/-- An actual one-site additive derivative on the original integer
axis. Its iterates were defined as `alpogeNativeForwardJet` above. -/
def alpogeNativeAdditiveStep (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  f (n + 1) - f n

/-- EXACT additive-clock versus multiplicative-wheel commutator.
No smooth-model or fibration assumption is imposed. -/
theorem alpogeNativeAdditiveWheel_commutator
    (p n : ℕ) (f : ℕ → ℝ) :
    alpogeNativeAdditiveStep
        (RHLean.Arithmetic.freshPrimeDifference p f) n -
      RHLean.Arithmetic.freshPrimeDifference p
        (alpogeNativeAdditiveStep f) n =
      f (n / p + 1) - f ((n + 1) / p) := by
  simp only [alpogeNativeAdditiveStep,
    RHLean.Arithmetic.freshPrimeDifference_apply]
  ring

/-- At all NON-boundary residues 0 <= r < p-1, the exact
commutator equals the first difference of the original quotient
source. A p-step fibre therefore has p-1 unpaid residues,
not just the exceptional crossing residue. -/
theorem alpogeNativeAdditiveWheel_noncrossing
    (p m r : ℕ) (hp : 0 < p) (hr : r + 1 < p)
    (f : ℕ → ℝ) :
    alpogeNativeAdditiveStep
        (RHLean.Arithmetic.freshPrimeDifference p f) (p * m + r) -
      RHLean.Arithmetic.freshPrimeDifference p
        (alpogeNativeAdditiveStep f) (p * m + r) =
      f (m + 1) - f m := by
  rw [alpogeNativeAdditiveWheel_commutator]
  have h0 : (p * m + r) / p = m :=
    alpogeNativeFloorPrimeFiber_div p m r hp (by omega)
  have h1 : (p * m + r + 1) / p = m := by
    have hh : p * m + r + 1 = p * m + (r + 1) := by omega
    rw [hh]
    exact alpogeNativeFloorPrimeFiber_div p m (r + 1) hp hr
  rw [h0, h1]

/-- **GENUINE SOURCE:** the mixed additive-square / multiplicative-prime
commutator on Chebyshev E=psi-x is exactly Lambda(m+1)-1 on every
noncrossing integer residue. No prime-power term or sign is lost.
This is an original-source boundary debt, not a geometric cost proof. -/
theorem alpogeNativeChebyshevAdditiveWheel_noncrossing
    (p m r : ℕ) (hp : 0 < p) (hr : r + 1 < p) :
    alpogeNativeAdditiveStep
        (RHLean.Arithmetic.freshPrimeDifference p nativePNTError)
          (p * m + r) -
      RHLean.Arithmetic.freshPrimeDifference p
        (alpogeNativeAdditiveStep nativePNTError)
          (p * m + r) =
      Λ (m + 1) - 1 := by
  rw [alpogeNativeAdditiveWheel_noncrossing p m r hp hr]
  exact nativePNTError_succ_eq m

end RHLean.Analysis
