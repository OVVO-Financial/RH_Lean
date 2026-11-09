import Mathlib
import RHLean.Arithmetic.PrimeCombFiniteDifferenceRecovery

/-!
# Square-root prime reconstruction of squarefree integers

Only primes through `Nat.sqrt X` appear in the primorial.  The residual
coprime to that primorial, if greater than one and at most `X`, is prime.

The divisor reconstruction must restrict the outer divisor to `d <= X`.
The unfiltered displayed Eq. (15) is false already at X=49.
-/

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic
open scoped ArithmeticFunction.Moebius BigOperators

def y (X : ℕ) : ℕ := Nat.sqrt X

def P_y (X : ℕ) : ℕ :=
  ∏ p ∈ primesUpTo (y X), p

private theorem P_y_ne_zero (X : ℕ) : P_y X ≠ 0 := by
  unfold P_y
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact (prime_of_mem_primesUpTo hp).ne_zero

/-- Every prime not exceeding the square root divides the primorial. -/
theorem prime_dvd_P_y {X p : ℕ}
    (hp : Nat.Prime p) (hple : p ≤ y X) :
    p ∣ P_y X := by
  unfold P_y
  exact Finset.dvd_prod_of_mem id
    (mem_primesUpTo.mpr ⟨hp, hple⟩)

/-- A prime divisor of an integer coprime to the square-root primorial
must lie strictly above the square root. -/
private theorem prime_gt_root_of_coprime
    (X r p : ℕ) (hp : Nat.Prime p) (hpr : p ∣ r)
    (hc : Nat.Coprime r (P_y X)) :
    y X < p := by
  by_contra hnot
  have hple : p ≤ y X := Nat.le_of_not_gt hnot
  have hprod : p ∣ P_y X := prime_dvd_P_y hp hple
  have hpone : p ∣ 1 := by
    have h := Nat.dvd_gcd hpr hprod
    rw [show Nat.gcd r (P_y X) = 1 from hc] at h
    exact h
  exact hp.ne_one (Nat.dvd_one.mp hpone)

/-- A survivor beyond 1 is necessarily prime below X: if it were composite,
its least prime divisor would be no greater than sqrt X. -/
theorem coprime_root_survivor_is_prime
    (X r : ℕ) (hr : 1 < r) (hrX : r ≤ X)
    (hc : Nat.Coprime r (P_y X)) :
    Nat.Prime r ∧ y X < r := by
  by_cases hprime : Nat.Prime r
  · exact ⟨hprime,
      prime_gt_root_of_coprime X r r hprime (dvd_refl r) hc⟩
  · let p := r.minFac
    have hp : Nat.Prime p := by
      simpa [p] using
        (Nat.minFac_prime (by omega : r ≠ 1))
    have hpd : p ∣ r := by
      simpa [p] using Nat.minFac_dvd r
    have hpy : y X < p :=
      prime_gt_root_of_coprime X r p hp hpd hc
    have hpsq : p ^ 2 ≤ r := by
      simpa [p] using
        (Nat.minFac_sq_le_self (by omega : 0 < r) hprime)
    have hX : X < (y X + 1) ^ 2 := by
      simpa [y] using Nat.lt_succ_sqrt' X
    have hyy : (y X + 1) ^ 2 ≤ p ^ 2 :=
      Nat.pow_le_pow_left (by omega : y X + 1 ≤ p) 2
    omega

/-- Every squarefree integer at or below X splits into a divisor of the
square-root primorial and either 1 or a prime above sqrt X. -/
theorem squarefree_decomposition (X : ℕ) (n : ℕ)
    (hn : n ≤ X) (hsf : Squarefree n) :
    ∃ d r, d ∣ P_y X ∧ n = d * r ∧
      (r = 1 ∨ (Nat.Prime r ∧ y X < r)) := by
  have hn0 : n ≠ 0 := hsf.ne_zero
  let d := Nat.gcd n (P_y X)
  let r := n / d
  have hdn : d ∣ n := by
    dsimp [d]
    exact Nat.gcd_dvd_left n (P_y X)
  have hdp : d ∣ P_y X := by
    dsimp [d]
    exact Nat.gcd_dvd_right n (P_y X)
  have hprod : d * r = n := by
    dsimp [r]
    exact Nat.mul_div_cancel' hdn
  have hcop : Nat.Coprime r (P_y X) := by
    dsimp [r, d]
    exact Nat.coprime_div_gcd_of_squarefree hsf (P_y_ne_zero X)
  have hrpos : 0 < r := by
    rcases Nat.eq_zero_or_pos r with hrzero | hrpositive
    · rw [hrzero, mul_zero] at hprod
      exact False.elim (hn0 hprod.symm)
    · exact hrpositive
  have hrle : r ≤ X := by
    dsimp [r]
    exact (Nat.div_le_self n d).trans hn
  refine ⟨d, r, hdp, hprod.symm, ?_⟩
  by_cases hr1 : r = 1
  · exact Or.inl hr1
  · exact Or.inr
      (coprime_root_survivor_is_prime X r (by omega) hrle hcop)

-- Certifies the unique-small-prime-support mechanism underlying Eq. (15).
-- The signed finite C_X rewriting is stated separately once multiplicities
-- and the necessary d <= X truncation are checked.

end RHLean.Analysis
