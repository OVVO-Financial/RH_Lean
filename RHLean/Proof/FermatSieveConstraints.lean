import Mathlib
import RHLean.Proof.DeathShellCardinalityAndCentering

/-!
# Fermat sieve constraints for death-shell coordinates

The correct terminal-digit classification is indexed by `N mod 20`, not by
`N mod 10` alone.  The modulus twenty simultaneously records

* the Fermat parity lane through `N mod 4`; and
* the terminal residue through `N mod 10`.

For the odd classes coprime to ten, each of the eight residues
`1,3,7,9,11,13,17,19 (mod 20)` has exactly four admissible terminal pairs.
The corresponding mod-ten table is the union of its two compatible mod-four
lanes and therefore has eight pairs.

The finite tables below are proved by computation.  No asymptotic shell
cardinality claim is made here.
-/

noncomputable section

namespace RHLean.Proof

/-- Decimal unit digits available to an odd integer coprime to ten. -/
def isOddDecimalUnitDigit (d : ℕ) : Bool :=
  d % 10 == 1 || d % 10 == 3 || d % 10 == 7 || d % 10 == 9

/-- Fermat parity condition determined by the full residue modulo twenty. -/
def fermatParityAdmissibleMod20 (n20 a b : ℕ) : Bool :=
  if n20 % 4 == 1 then
    a % 2 == 1 && b % 2 == 0
  else if n20 % 4 == 3 then
    a % 2 == 0 && b % 2 == 1
  else
    false

/-- Exact coprime-to-ten terminal-digit condition for
`N = a^2 - b^2 = (a-b)(a+b)`, indexed by `N mod 20`. -/
def fermatDigitAdmissibleMod20 (n20 a b : ℕ) : Bool :=
  fermatParityAdmissibleMod20 n20 a b &&
    isOddDecimalUnitDigit ((a + 10 - b) % 10) &&
    isOddDecimalUnitDigit ((a + b) % 10) &&
    ((((a + 10 - b) % 10) * ((a + b) % 10)) % 10 == n20 % 10)

/-- Finite set of admissible terminal pairs `(a mod 10,b mod 10)` for one
residue class modulo twenty. -/
def fermatDigitPairsMod20 (n20 : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range 10).product (Finset.range 10)).filter fun p =>
    fermatDigitAdmissibleMod20 n20 p.1 p.2

/-- The complete mod-ten table is the union of the two compatible mod-twenty
classes. -/
def fermatDigitPairsMod10Union (n10 : ℕ) : Finset (ℕ × ℕ) :=
  fermatDigitPairsMod20 (n10 % 10) ∪
    fermatDigitPairsMod20 (n10 % 10 + 10)

/-- Death-shell Fermat `a` coordinate for a prime-cofactor pair. -/
def deathFermatA (q c : ℕ) : ℕ :=
  (q + c) / 2

/-- Death-shell Fermat `b` coordinate for a prime-cofactor pair. -/
def deathFermatB (q c : ℕ) : ℕ :=
  if q ≤ c then (c - q) / 2 else (q - c) / 2

/-- The mod-twenty terminal sieve applied directly to a death-shell pair. -/
def deathFermatDigitAdmissible (N q c : ℕ) : Bool :=
  fermatDigitAdmissibleMod20 (N % 20)
    (deathFermatA q c) (deathFermatB q c)

/-- `N ≡ 1 (mod 20)`: odd-even Fermat lane. -/
theorem fermatDigitPairsMod20_one :
    fermatDigitPairsMod20 1 =
      ([(1, 0), (5, 2), (5, 8), (9, 0)] : List (ℕ × ℕ)).toFinset := by
  native_decide

/-- `N ≡ 3 (mod 20)`: even-odd Fermat lane. -/
theorem fermatDigitPairsMod20_three :
    fermatDigitPairsMod20 3 =
      ([(2, 1), (2, 9), (8, 1), (8, 9)] : List (ℕ × ℕ)).toFinset := by
  native_decide

/-- `N ≡ 7 (mod 20)`: even-odd Fermat lane. -/
theorem fermatDigitPairsMod20_seven :
    fermatDigitPairsMod20 7 =
      ([(4, 3), (4, 7), (6, 3), (6, 7)] : List (ℕ × ℕ)).toFinset := by
  native_decide

/-- `N ≡ 9 (mod 20)`: odd-even Fermat lane. -/
theorem fermatDigitPairsMod20_nine :
    fermatDigitPairsMod20 9 =
      ([(3, 0), (5, 4), (5, 6), (7, 0)] : List (ℕ × ℕ)).toFinset := by
  native_decide

/-- `N ≡ 11 (mod 20)`: even-odd Fermat lane.  This is the lane containing
`551 = 24^2 - 5^2 = 19 * 29`. -/
theorem fermatDigitPairsMod20_eleven :
    fermatDigitPairsMod20 11 =
      ([(0, 3), (0, 7), (4, 5), (6, 5)] : List (ℕ × ℕ)).toFinset := by
  native_decide

/-- `N ≡ 13 (mod 20)`: odd-even Fermat lane. -/
theorem fermatDigitPairsMod20_thirteen :
    fermatDigitPairsMod20 13 =
      ([(3, 4), (3, 6), (7, 4), (7, 6)] : List (ℕ × ℕ)).toFinset := by
  native_decide

/-- `N ≡ 17 (mod 20)`: odd-even Fermat lane. -/
theorem fermatDigitPairsMod20_seventeen :
    fermatDigitPairsMod20 17 =
      ([(1, 2), (1, 8), (9, 2), (9, 8)] : List (ℕ × ℕ)).toFinset := by
  native_decide

/-- `N ≡ 19 (mod 20)`: even-odd Fermat lane. -/
theorem fermatDigitPairsMod20_nineteen :
    fermatDigitPairsMod20 19 =
      ([(0, 1), (0, 9), (2, 5), (8, 5)] : List (ℕ × ℕ)).toFinset := by
  native_decide

/-- Complete `N ≡ 1 (mod 10)` table: union of the `1` and `11` mod-twenty
lanes. -/
theorem fermatDigitPairsMod10_one :
    fermatDigitPairsMod10Union 1 =
      ([(1, 0), (5, 2), (5, 8), (9, 0),
        (0, 3), (0, 7), (4, 5), (6, 5)] : List (ℕ × ℕ)).toFinset := by
  native_decide

/-- Complete `N ≡ 3 (mod 10)` table: union of the `3` and `13` mod-twenty
lanes. -/
theorem fermatDigitPairsMod10_three :
    fermatDigitPairsMod10Union 3 =
      ([(2, 1), (2, 9), (8, 1), (8, 9),
        (3, 4), (3, 6), (7, 4), (7, 6)] : List (ℕ × ℕ)).toFinset := by
  native_decide

/-- Complete `N ≡ 7 (mod 10)` table: union of the `7` and `17` mod-twenty
lanes. -/
theorem fermatDigitPairsMod10_seven :
    fermatDigitPairsMod10Union 7 =
      ([(4, 3), (4, 7), (6, 3), (6, 7),
        (1, 2), (1, 8), (9, 2), (9, 8)] : List (ℕ × ℕ)).toFinset := by
  native_decide

/-- Complete `N ≡ 9 (mod 10)` table: union of the `9` and `19` mod-twenty
lanes. -/
theorem fermatDigitPairsMod10_nine :
    fermatDigitPairsMod10Union 9 =
      ([(3, 0), (5, 4), (5, 6), (7, 0),
        (0, 1), (0, 9), (2, 5), (8, 5)] : List (ℕ × ℕ)).toFinset := by
  native_decide

/-- Regression witness for the PDF row `a=24`, `b=5`:
`551 = 24^2 - 5^2 = 19 * 29 ≡ 11 (mod 20)`. -/
theorem fermat_551_regression :
    deathFermatA 29 19 = 24 ∧
      deathFermatB 29 19 = 5 ∧
        (4, 5) ∈ fermatDigitPairsMod20 11 := by
  native_decide

/-- In either odd Fermat parity lane, the doubled product `2ab` is divisible by
four. -/
theorem four_dvd_two_mul_of_fermatParity
    {a b : ℕ}
    (h : (Odd a ∧ Even b) ∨ (Even a ∧ Odd b)) :
    4 ∣ 2 * a * b := by
  rcases h with ⟨_, hb⟩ | ⟨ha, _⟩
  · rcases hb with ⟨k, rfl⟩
    refine ⟨a * k, by ring⟩
  · rcases ha with ⟨k, rfl⟩
    refine ⟨k * b, by ring⟩

end RHLean.Proof
