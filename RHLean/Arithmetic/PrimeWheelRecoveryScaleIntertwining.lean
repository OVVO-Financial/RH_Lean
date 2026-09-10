import Mathlib
import RHLean.Arithmetic.PrimeCombFiniteDifferenceFreshPrime
import RHLean.Arithmetic.PrimeCombFiniteDifferenceRecovery

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Arithmetic

/-!
# Recovered prime-wheel field under Euler / q-square scale transport

`PrimeCombFiniteDifferenceRecovery` identifies the joint prime-wheel field
`raw - 2*smooth` with the actual Möbius prefix at every floor-shifted cutoff.
The operator used there need not be tied to the prime set used to recover the
field.  Once that harmless generalization is made, the scale-commutation lemmas
from `PrimeCombFiniteDifferenceFreshPrime` transport the *actual recovered
Möbius field* through the prime-11 difference and an arbitrary `q^2` daughter
shift.

These are exact finite identities before any norm, energy, CRT averaging, or
asymptotic estimate.
-/

/-- Square-root prime-wheel recovery is respected by an arbitrary independent
finite Möbius difference operator `D_T`.  The recovery prime set `P` and the
operator prime set `T` are deliberately separate. -/
theorem finiteDifferenceOperator_primeWheelRecovery_general
    (P T : Finset ℕ) (upper x : ℕ)
    (hprime : ∀ p ∈ P, Nat.Prime p)
    (hcover : PrimeWheelSqrtCoverage P upper)
    (hx : x ≤ upper) :
    finiteDifferenceOperator T
        (fun y =>
          primeWheelRawPositivePrefix P y -
            2 * primeWheelSmoothPositivePrefix P upper y) x =
      finiteDifferenceOperator T moebiusPositivePrefix x := by
  classical
  unfold finiteDifferenceOperator
  apply Finset.sum_congr rfl
  intro d hd
  have hdx : x / d ≤ upper :=
    (Nat.div_le_self x d).trans hx
  have hprefix :=
    primeWheelRaw_sub_two_smooth_eq_moebiusPositivePrefix
      P upper (x / d) hprime hcover hdx
  rw [show
    shift d
        (fun y =>
          primeWheelRawPositivePrefix P y -
            2 * primeWheelSmoothPositivePrefix P upper y) x =
      shift d moebiusPositivePrefix x by
        simpa [shift] using hprefix]

/-- The same all-prime recovery after a multiplicative daughter shift. -/
theorem finiteDifferenceOperator_primeWheelRecovery_squareShift
    (P T : Finset ℕ) (upper x q : ℕ)
    (hprime : ∀ p ∈ P, Nat.Prime p)
    (hcover : PrimeWheelSqrtCoverage P upper)
    (hx : x ≤ upper) :
    finiteDifferenceOperator T
        (shift (q * q) (fun y =>
          primeWheelRawPositivePrefix P y -
            2 * primeWheelSmoothPositivePrefix P upper y)) x =
      finiteDifferenceOperator T
        (shift (q * q) moebiusPositivePrefix) x := by
  rw [finiteDifferenceOperator_shift_comm,
    finiteDifferenceOperator_shift_comm]
  have hchild : x / (q * q) ≤ upper :=
    (Nat.div_le_self x (q * q)).trans hx
  simpa [shift] using
    finiteDifferenceOperator_primeWheelRecovery_general
      P T upper (x / (q * q)) hprime hcover hchild

/-- Recovery is also preserved after one arbitrary fresh-prime difference. -/
theorem finiteDifferenceOperator_primeWheelRecovery_freshDifference
    (P T : Finset ℕ) (upper x p : ℕ)
    (hprime : ∀ r ∈ P, Nat.Prime r)
    (hcover : PrimeWheelSqrtCoverage P upper)
    (hx : x ≤ upper) :
    finiteDifferenceOperator T
        (freshPrimeDifference p (fun y =>
          primeWheelRawPositivePrefix P y -
            2 * primeWheelSmoothPositivePrefix P upper y)) x =
      finiteDifferenceOperator T
        (freshPrimeDifference p moebiusPositivePrefix) x := by
  unfold freshPrimeDifference
  rw [finiteDifferenceOperator_sub, finiteDifferenceOperator_sub,
    finiteDifferenceOperator_shift_comm,
    finiteDifferenceOperator_shift_comm]
  have hbase :=
    finiteDifferenceOperator_primeWheelRecovery_general
      P T upper x hprime hcover hx
  have hpchild : x / p ≤ upper :=
    (Nat.div_le_self x p).trans hx
  have hchild :=
    finiteDifferenceOperator_primeWheelRecovery_general
      P T upper (x / p) hprime hcover hpchild
  simp only [shift]
  rw [hbase, hchild]

/-- **Actual Möbius prime-11 / q² intertwining.**  Form the prime-11 Euler
finite difference before owner separation and then descend by the square owner
scale.  On the exact square-root recovered field `raw - 2*smooth`, every old
Euler fibre `D_T` gives exactly the same result as on the true Möbius prefix.
No selected-prime surrogate occurs in this theorem. -/
theorem finiteDifferenceOperator_recoveredMobius_eleven_q2_intertwining
    (P T : Finset ℕ) (upper x q : ℕ)
    (hprime : ∀ p ∈ P, Nat.Prime p)
    (hcover : PrimeWheelSqrtCoverage P upper)
    (hx : x ≤ upper) :
    finiteDifferenceOperator T
        (freshPrimeDifference 11
          (shift (q * q) (fun y =>
            primeWheelRawPositivePrefix P y -
              2 * primeWheelSmoothPositivePrefix P upper y))) x =
      finiteDifferenceOperator T
        (freshPrimeDifference 11
          (shift (q * q) moebiusPositivePrefix)) x := by
  rw [finiteDifferenceOperator_eleven_squareShift_intertwining,
    finiteDifferenceOperator_eleven_squareShift_intertwining]
  have hchild : x / (q * q) ≤ upper :=
    (Nat.div_le_self x (q * q)).trans hx
  simpa [shift] using
    finiteDifferenceOperator_primeWheelRecovery_freshDifference
      P T upper (x / (q * q)) 11 hprime hcover hchild

end RHLean.Arithmetic
