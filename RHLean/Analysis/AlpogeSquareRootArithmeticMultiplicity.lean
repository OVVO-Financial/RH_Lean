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


/-!
## A signed square-root descent that the separate unsigned estimates miss

On each complete multiplicative p-quotient fibre, the additive/prime
commutator has p-1 copies of the *same signed* quotient increment and
one zero crossing. Summing over all quotient rows telescopes exactly.
When p=M=R, the physical R-by-R rectangle has R^2 sites, but its
FULL signed commutator collapses to the single original source value
at R, multiplied by R-1. The multiplier is a genuine unpaid cost:
it must NOT be silently divided away to claim a geometric lift.
-/

/-- The final residue r=p-1 crosses the quotient wall and pays ZERO
in the mixed commutator. All r<p-1 are handled by the earlier lemma. -/
theorem alpogeNativeAdditiveWheel_crossing
    (p m : ℕ) (hp : 0 < p) (f : ℕ → ℝ) :
    alpogeNativeAdditiveStep
        (RHLean.Arithmetic.freshPrimeDifference p f)
          (p * m + (p - 1)) -
      RHLean.Arithmetic.freshPrimeDifference p
        (alpogeNativeAdditiveStep f)
          (p * m + (p - 1)) = 0 := by
  rw [alpogeNativeAdditiveWheel_commutator]
  have h0 : (p * m + (p - 1)) / p = m :=
    alpogeNativeFloorPrimeFiber_div p m (p - 1) hp (by omega)
  have hmul : p * m + (p - 1) + 1 = p * (m + 1) := by
    calc
      p * m + (p - 1) + 1 = p * m + p := by omega
      _ = p * (m + 1) := by ring
  have h1 : (p * m + (p - 1) + 1) / p = m + 1 := by
    rw [hmul]
    exact Nat.mul_div_cancel_left (m + 1) hp
  rw [h0, h1, sub_self]

/-- Every complete p-quotient row has EXACTLY p-1 copies of the
original signed quotient difference, including its prime powers.
This is a same-source equality, not a triangle bound. -/
theorem alpogeNativeAdditiveWheel_fiber_sum
    (p m : ℕ) (hp : 0 < p) (f : ℕ → ℝ) :
    (∑ r ∈ Finset.range p,
      (alpogeNativeAdditiveStep
          (RHLean.Arithmetic.freshPrimeDifference p f)
            (p * m + r) -
        RHLean.Arithmetic.freshPrimeDifference p
          (alpogeNativeAdditiveStep f)
            (p * m + r))) =
      ((p - 1 : ℕ) : ℝ) * (f (m + 1) - f m) := by
  have hrange : Finset.range p = Finset.range ((p - 1) + 1) := by
    congr 1
    omega
  rw [hrange, Finset.sum_range_succ]
  have hprefix :
      (∑ r ∈ Finset.range (p - 1),
        (alpogeNativeAdditiveStep
            (RHLean.Arithmetic.freshPrimeDifference p f)
              (p * m + r) -
          RHLean.Arithmetic.freshPrimeDifference p
            (alpogeNativeAdditiveStep f)
              (p * m + r))) =
        ((p - 1 : ℕ) : ℝ) * (f (m + 1) - f m) := by
    calc
      _ = ∑ _r ∈ Finset.range (p - 1), (f (m + 1) - f m) := by
        apply Finset.sum_congr rfl
        intro r hr
        exact alpogeNativeAdditiveWheel_noncrossing
          p m r hp (by have h := Finset.mem_range.mp hr; omega) f
      _ = ((p - 1 : ℕ) : ℝ) * (f (m + 1) - f m) := by
        simp [nsmul_eq_mul]
        ring
  rw [hprefix, alpogeNativeAdditiveWheel_crossing p m hp f]
  ring

/-- The ENTIRE physical p-by-M lattice of additive/Euler commutators
telescopes in SIGNED form to the two original-source endpoints.
The p-1 multiple persists, so no covolume/multiplicity saving is
asserted. This statement is valid for any positive integer p as a
floor-shift; it is a PRIME-WHEEL step only when p is prime. -/
theorem alpogeNativeAdditiveWheel_rectangular_telescope
    (p M : ℕ) (hp : 0 < p) (f : ℕ → ℝ) :
    (∑ m ∈ Finset.range M, ∑ r ∈ Finset.range p,
      (alpogeNativeAdditiveStep
          (RHLean.Arithmetic.freshPrimeDifference p f)
            (p * m + r) -
        RHLean.Arithmetic.freshPrimeDifference p
          (alpogeNativeAdditiveStep f)
            (p * m + r))) =
      ((p - 1 : ℕ) : ℝ) * (f M - f 0) := by
  have htel :
      (∑ m ∈ Finset.range M, (f (m + 1) - f m)) =
        f M - f 0 := by
    induction M with
    | zero => simp
    | succ m ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  calc
    _ = ∑ m ∈ Finset.range M,
        ((p - 1 : ℕ) : ℝ) * (f (m + 1) - f m) := by
          apply Finset.sum_congr rfl
          intro m _hm
          exact alpogeNativeAdditiveWheel_fiber_sum p m hp f
    _ = ((p - 1 : ℕ) : ℝ) * (f M - f 0) := by
          rw [← Finset.mul_sum, htel]

/-- The complete R-by-R square lattice: the original Chebyshev
error at the ENTIRE R²-source collapses to the one root endpoint.
This is a valid FLOOR-shift for every R>0; for composite R it is
NOT the prime-wheel adjunction of a new prime. -/
theorem alpogeNativeSquareClock_mixedWheel_signedTelescope
    (R : ℕ) (hR : 1 ≤ R) :
    (∑ m ∈ Finset.range R, ∑ r ∈ Finset.range R,
      (alpogeNativeAdditiveStep
          (RHLean.Arithmetic.freshPrimeDifference R nativePNTError)
            (R * m + r) -
        RHLean.Arithmetic.freshPrimeDifference R
          (alpogeNativeAdditiveStep nativePNTError)
            (R * m + r))) =
      ((R - 1 : ℕ) : ℝ) * nativePNTError R := by
  have h := alpogeNativeAdditiveWheel_rectangular_telescope
    R R (by omega) nativePNTError
  have hz : nativePNTError 0 = 0 := by
    simp [nativePNTError, nativePsi]
  simpa only [hz, sub_zero] using h


end RHLean.Analysis

/-! ## Explicit kernel axiom audit: expected only standard Lean axioms. -/
#print axioms RHLean.Analysis.alpogeNativeForwardJet_error_two
#print axioms RHLean.Analysis.alpogeNativeForwardJet_error_high
#print axioms RHLean.Analysis.alpogeNativeForwardJet_abs_le_exp
#print axioms RHLean.Analysis.alpogeSquareRootArithmeticJet_sharp
#print axioms RHLean.Analysis.alpogeNativePrimeSevenDifference_not_divisible
#print axioms RHLean.Analysis.alpogeNativeFreshPrime_product_commutator
#print axioms RHLean.Analysis.alpogeNativeLiteralASK_freshPrime_characterDefect
#print axioms RHLean.Analysis.alpogeNativeFloorPrimeFiber_card
#print axioms RHLean.Analysis.alpogeNativeAdditiveWheel_noncrossing
#print axioms RHLean.Analysis.alpogeNativeChebyshevAdditiveWheel_noncrossing
#print axioms RHLean.Analysis.alpogeNativeAdditiveWheel_crossing
#print axioms RHLean.Analysis.alpogeNativeAdditiveWheel_fiber_sum
#print axioms RHLean.Analysis.alpogeNativeAdditiveWheel_rectangular_telescope
#print axioms RHLean.Analysis.alpogeNativeSquareClock_mixedWheel_signedTelescope
