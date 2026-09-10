import Mathlib
import RHLean.Arithmetic.PrimeCombFiniteDifferenceFreshPrime

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Arithmetic

/-!
# Finite-difference / multiplicative-scale intertwining

The square-dilated Go descent and the Euler prime-wheel difference act on the
same floor-shift algebra.  This module records the exact commuting square before
any norm is taken.

The key point is elementary but structural: floor shifts compose by multiplying
their dilation parameters, hence commute.  Therefore both the full finite
Möbius difference operator and one fresh-prime difference commute with an
arbitrary multiplicative scale shift.  In particular the prime-`11` difference
may be applied before the `q^2` owner split without changing the daughter field.

No primality, ordering, CRT-period, asymptotic, or RH assumption is used in the
commutation identities.
-/

/-- The canonical finite Möbius difference operator commutes with every floor
scale shift.  This is the operator-level Fubini identity needed to transport an
already-formed Euler field through a later `q^2` daughter descent. -/
theorem finiteDifferenceOperator_shift_comm
    {R : Type*} [CommRing R]
    (S : Finset ℕ) (e : ℕ) (f : ℕ → R) :
    finiteDifferenceOperator S (shift e f) =
      shift e (finiteDifferenceOperator S f) := by
  funext x
  unfold finiteDifferenceOperator shift
  apply Finset.sum_congr rfl
  intro d hd
  congr 1
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm d e]

/-- A fresh-prime finite difference commutes with every floor scale shift. -/
theorem freshPrimeDifference_shift_comm
    {R : Type*} [CommRing R]
    (p e : ℕ) (f : ℕ → R) :
    freshPrimeDifference p (shift e f) =
      shift e (freshPrimeDifference p f) := by
  funext x
  simp only [freshPrimeDifference_apply, shift]
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm e p]

/-- The same commuting square with the square-dilated owner scale written
literally as `q*q`. -/
theorem freshPrimeDifference_squareShift_comm
    {R : Type*} [CommRing R]
    (p q : ℕ) (f : ℕ → R) :
    freshPrimeDifference p (shift (q * q) f) =
      shift (q * q) (freshPrimeDifference p f) :=
  freshPrimeDifference_shift_comm p (q * q) f

/-- **Prime-11 / q^2 intertwining.**  The first generic Euler difference and the
Go square-dilated daughter operation commute exactly on every arithmetic field.
This is deliberately stated before taking absolute values or energies. -/
theorem elevenDifference_squareShift_comm
    {R : Type*} [CommRing R]
    (q : ℕ) (f : ℕ → R) :
    freshPrimeDifference 11 (shift (q * q) f) =
      shift (q * q) (freshPrimeDifference 11 f) :=
  freshPrimeDifference_squareShift_comm 11 q f

/-- Applying an existing finite prime fibre after the prime-11 difference still
commutes with the `q^2` daughter scale.  Thus all old Euler coordinates remain
inside the same signed fibre while the owner scale is pushed down. -/
theorem finiteDifferenceOperator_eleven_squareShift_intertwining
    {R : Type*} [CommRing R]
    (S : Finset ℕ) (q : ℕ) (f : ℕ → R) :
    finiteDifferenceOperator S
        (freshPrimeDifference 11 (shift (q * q) f)) =
      shift (q * q)
        (finiteDifferenceOperator S (freshPrimeDifference 11 f)) := by
  rw [elevenDifference_squareShift_comm]
  exact finiteDifferenceOperator_shift_comm S (q * q)
    (freshPrimeDifference 11 f)

/-- If `11` is fresh to `S`, the preceding theorem is exactly the unordered
Euler insertion operator on both sides.  This is the chronological-order-free
form needed by the canonical ancestry/Go pushforward. -/
theorem finiteDifferenceOperator_insert_eleven_squareShift_intertwining
    {R : Type*} [CommRing R]
    (S : Finset ℕ) (q : ℕ) (f : ℕ → R)
    (h11 : Nat.Prime 11) (h11S : 11 ∉ S)
    (hprime : ∀ r ∈ S, Nat.Prime r) :
    finiteDifferenceOperator (insert 11 S) (shift (q * q) f) =
      shift (q * q) (finiteDifferenceOperator (insert 11 S) f) := by
  rw [finiteDifferenceOperator_insert_eq_freshPrimeDifference
      S 11 h11 h11S hprime (shift (q * q) f),
    finiteDifferenceOperator_insert_eq_freshPrimeDifference
      S 11 h11 h11S hprime f]
  exact finiteDifferenceOperator_eleven_squareShift_intertwining S q f

end RHLean.Arithmetic
