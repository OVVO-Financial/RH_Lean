import Mathlib
import RHLean.Proof.DeathShellCardinalityAndCentering

/-!
# Fermat sieve constraints for death-shell coordinates

This module records the exact parity and terminal-digit sieve used by the
Fermat difference-of-squares parametrization.  The finite mod-10 tables are
proved by computation; no asymptotic cardinality claim is made here.

For odd `N = a^2 - b^2`:

* `N ≡ 1 (mod 4)` forces `a` odd and `b` even;
* `N ≡ 3 (mod 4)` forces `a` even and `b` odd.

When `N` is also coprime to `10`, the terminal digits of `a-b` and `a+b`
lie in `{1,3,7,9}` and their product is `N mod 10`.  The resulting tables
contain four admissible `(a mod 10, b mod 10)` pairs in every residue case.
-/

noncomputable section

namespace RHLean.Proof

/-- Decimal unit digits available to an odd integer coprime to `10`. -/
def isOddDecimalUnitDigit (d : ℕ) : Bool :=
  d % 10 == 1 || d % 10 == 3 || d % 10 == 7 || d % 10 == 9

/-- Fermat parity condition determined by `N mod 4`. -/
def fermatParityAdmissible (n4 a b : ℕ) : Bool :=
  if n4 % 4 == 1 then
    a % 2 == 1 && b % 2 == 0
  else if n4 % 4 == 3 then
    a % 2 == 0 && b % 2 == 1
  else
    false

/-- Exact terminal-digit condition for `N = (a-b)(a+b)`, in the case where
both factors are coprime to `10`. -/
def fermatDigitAdmissible (n4 n10 a b : ℕ) : Bool :=
  fermatParityAdmissible n4 a b &&
    isOddDecimalUnitDigit ((a + 10 - b) % 10) &&
    isOddDecimalUnitDigit ((a + b) % 10) &&
    ((((a + 10 - b) % 10) * ((a + b) % 10)) % 10 == n10 % 10)

/-- Finite set of admissible terminal digit pairs. -/
def fermatDigitPairs (n4 n10 : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range 10).product (Finset.range 10)).filter fun p =>
    fermatDigitAdmissible n4 n10 p.1 p.2

/-- Death-shell Fermat `a` coordinate for a prime-cofactor pair. -/
def deathFermatA (q c : ℕ) : ℕ :=
  (q + c) / 2

/-- Death-shell Fermat `b` coordinate for a prime-cofactor pair. -/
def deathFermatB (q c : ℕ) : ℕ :=
  q.absDiff c / 2

/-- The terminal-digit sieve applied directly to a death-shell pair. -/
def deathFermatDigitAdmissible (N q c : ℕ) : Bool :=
  fermatDigitAdmissible (N % 4) (N % 10)
    (deathFermatA q c) (deathFermatB q c)

/-- `N ≡ 1 (mod 4)`, `N ≡ 1 (mod 10)`. -/
theorem fermatDigitPairs_1_1 :
    fermatDigitPairs 1 1 =
      ([(1, 0), (5, 2), (5, 8), (9, 0)] : List (ℕ × ℕ)).toFinset := by
  native_decide

/-- `N ≡ 1 (mod 4)`, `N ≡ 3 (mod 10)`. -/
theorem fermatDigitPairs_1_3 :
    fermatDigitPairs 1 3 =
      ([(3, 4), (3, 6), (7, 4), (7, 6)] : List (ℕ × ℕ)).toFinset := by
  native_decide

/-- `N ≡ 1 (mod 4)`, `N ≡ 7 (mod 10)`. -/
theorem fermatDigitPairs_1_7 :
    fermatDigitPairs 1 7 =
      ([(1, 2), (1, 8), (9, 2), (9, 8)] : List (ℕ × ℕ)).toFinset := by
  native_decide

/-- `N ≡ 1 (mod 4)`, `N ≡ 9 (mod 10)`. -/
theorem fermatDigitPairs_1_9 :
    fermatDigitPairs 1 9 =
      ([(3, 0), (5, 4), (5, 6), (7, 0)] : List (ℕ × ℕ)).toFinset := by
  native_decide

/-- `N ≡ 3 (mod 4)`, `N ≡ 1 (mod 10)`. -/
theorem fermatDigitPairs_3_1 :
    fermatDigitPairs 3 1 =
      ([(0, 3), (0, 7), (4, 5), (6, 5)] : List (ℕ × ℕ)).toFinset := by
  native_decide

/-- `N ≡ 3 (mod 4)`, `N ≡ 3 (mod 10)`. -/
theorem fermatDigitPairs_3_3 :
    fermatDigitPairs 3 3 =
      ([(2, 1), (2, 9), (8, 1), (8, 9)] : List (ℕ × ℕ)).toFinset := by
  native_decide

/-- `N ≡ 3 (mod 4)`, `N ≡ 7 (mod 10)`. -/
theorem fermatDigitPairs_3_7 :
    fermatDigitPairs 3 7 =
      ([(4, 3), (4, 7), (6, 3), (6, 7)] : List (ℕ × ℕ)).toFinset := by
  native_decide

/-- `N ≡ 3 (mod 4)`, `N ≡ 9 (mod 10)`. -/
theorem fermatDigitPairs_3_9 :
    fermatDigitPairs 3 9 =
      ([(0, 1), (0, 9), (2, 5), (8, 5)] : List (ℕ × ℕ)).toFinset := by
  native_decide

/-- Every coprime odd residue case has exactly four admissible terminal pairs. -/
theorem fermatDigitPairs_card_four
    (n4 n10 : ℕ)
    (h4 : n4 % 4 = 1 ∨ n4 % 4 = 3)
    (h10 : n10 % 10 = 1 ∨ n10 % 10 = 3 ∨
      n10 % 10 = 7 ∨ n10 % 10 = 9) :
    (fermatDigitPairs n4 n10).card = 4 := by
  rcases h4 with h4 | h4 <;>
    rcases h10 with h10 | h10 | h10 | h10 <;>
    subst_vars <;> native_decide

end RHLean.Proof
