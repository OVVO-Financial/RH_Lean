import RHLean.Analysis.EulerCRTRoughnessRecursion
import RHLean.Arithmetic.PrimeCombFiniteDifferenceFreshPrime

/-!
# Exact full-prime-wheel transport on the Mertens carrier

The dyadic cancellation is not a one-prime accident.  The repository already
contains both sides of the general mechanism:

* `roughMertens_wheel_recursion`: removing a wheel prime is a multiplicative
  finite difference of the rough Mertens state;
* `finiteDifferenceOperator_insert_eq_freshPrimeDifference`: adjoining a fresh
  prime is exactly one more Boolean finite-difference coordinate.

This file identifies them.  For every finite set `S` of genuine primes, applying
all selected prime differences to the `primorial S`-rough Mertens state recovers
ordinary Mertens exactly.  Hence enlarging the wheel by a fresh prime leaves the
recovered physical prefix invariant while redistributing it into finer signed
ratio bands.  No estimate, ordering of the primes, or complete CRT period is
used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

private theorem primorial_squarefree_of_primes
    (S : Finset ℕ) (hprime : ∀ p ∈ S, Nat.Prime p) :
    Squarefree (primorial S) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp [primorial]
  | @insert p S hpS ih =>
      have hp : Nat.Prime p := hprime p (by simp)
      have hprimeS : ∀ q ∈ S, Nat.Prime q := by
        intro q hq
        exact hprime q (by simp [hq])
      have hsqS : Squarefree (primorial S) := ih hprimeS
      have hcop : Nat.Coprime p (primorial S) :=
        prime_coprime_primorial S p hp hpS hprimeS
      have hsq : Squarefree (p * primorial S) :=
        (Nat.squarefree_mul hcop).2 ⟨hp.squarefree, hsqS⟩
      rw [primorial_insert S p hpS]
      exact hsq

/-- **Full finite prime-wheel recovery of ordinary Mertens.**  Every selected
prime contributes exactly one multiplicative difference, and after all of them
are taken the rough wheel state is transported back to wheel `1`:

`D_S (T_{prod S}) = T_1`.

This is the unordered finite-set form of the iterative cancellation visible in
the full prime wheel. -/
theorem finiteDifferenceOperator_roughMertens_primorial
    (S : Finset ℕ) (hprime : ∀ p ∈ S, Nat.Prime p) :
    finiteDifferenceOperator S (roughMertens (primorial S)) = roughMertens 1 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp [primorial]
  | @insert p S hpS ih =>
      have hp : Nat.Prime p := hprime p (by simp)
      have hprimeS : ∀ q ∈ S, Nat.Prime q := by
        intro q hq
        exact hprime q (by simp [hq])
      have hsqS : Squarefree (primorial S) :=
        primorial_squarefree_of_primes S hprimeS
      have hcop : Nat.Coprime p (primorial S) :=
        prime_coprime_primorial S p hp hpS hprimeS
      have hsq : Squarefree (p * primorial S) :=
        (Nat.squarefree_mul hcop).2 ⟨hp.squarefree, hsqS⟩
      have hrec :
          freshPrimeDifference p (roughMertens (p * primorial S)) =
            roughMertens (primorial S) := by
        funext x
        have h := roughMertens_wheel_recursion
          (W := p * primorial S) (p := p) hp
          (by exact ⟨primorial S, rfl⟩) hsq x
        have hdiv : (p * primorial S) / p = primorial S :=
          Nat.mul_div_cancel_left (primorial S) hp.pos
        rw [hdiv] at h
        simpa [freshPrimeDifference, multDiff] using h
      rw [primorial_insert S p hpS]
      rw [finiteDifferenceOperator_insert_eq_freshPrimeDifference
        S p hp hpS hprimeS]
      rw [hrec]
      exact ih hprimeS

/-- Pointwise divisor-ratio form of the full-wheel identity.  This is the exact
signed staircase on which successive prime additions act:

`T_1(B) = sum_{d | prod S} mu(d) T_{prod S}(floor(B/d))`.

The zero bands seen for `{2,3}` are therefore instances of a general finite
Boolean difference, not a special dyadic phenomenon. -/
theorem roughMertens_one_eq_primeWheel_divisorDifference
    (S : Finset ℕ) (hprime : ∀ p ∈ S, Nat.Prime p) (B : ℕ) :
    roughMertens 1 B =
      ∑ d ∈ (primorial S).divisors,
        (μ d : ℤ) * roughMertens (primorial S) (B / d) := by
  have h := congrFun (finiteDifferenceOperator_roughMertens_primorial S hprime) B
  rw [finiteDifferenceOperator_apply] at h
  simpa using h.symm

/-- **Prime adjoining is an exact refinement, not a new estimate.**  If `p` is
fresh, the recovered physical Mertens prefix is unchanged when the wheel grows
from `S` to `insert p S`; only its signed ratio-band representation is refined.
This is the formal iterative statement behind the full prime wheel. -/
theorem primeWheelMertensTransport_invariant_insert
    (S : Finset ℕ) (p : ℕ)
    (hp : Nat.Prime p) (hpS : p ∉ S)
    (hprime : ∀ q ∈ S, Nat.Prime q) :
    finiteDifferenceOperator (insert p S)
        (roughMertens (primorial (insert p S))) =
      finiteDifferenceOperator S (roughMertens (primorial S)) := by
  have hprimeInsert : ∀ q ∈ insert p S, Nat.Prime q := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hqS
    · exact hp
    · exact hprime q hqS
  rw [finiteDifferenceOperator_roughMertens_primorial (insert p S) hprimeInsert]
  rw [finiteDifferenceOperator_roughMertens_primorial S hprime]

end RHLean.Proof
