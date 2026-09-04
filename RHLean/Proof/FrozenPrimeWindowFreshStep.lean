import Mathlib
import RHLean.Proof.SquareRootLowPrimeFirstOwnerWallRecurrence

/-!
# Fresh-prime recurrence for signed frozen windows

The pointwise frozen-prime recurrence is

`F_{S ∪ {p}}(X) = F_S(X) - F_S(floor(X/p))`.

For the square-run attack the relevant object is not one cutoff but a signed
window.  Subtracting the recurrence at two endpoints gives the exact law

`W_{S ∪ {p}}(A,B) = W_S(A,B) - W_S(floor(A/p), floor(B/p))`.

Thus admitting a fresh Euler prime does not create another independent copy of
one parent.  Its entire additive effect on the window is the negative of one
compressed predecessor-cube window.  This is the finite algebraic replacement
for the false prime-gap lifetime picture.

No norm, prime-gap estimate, PNT input, or asymptotic statement is used.
-/

noncomputable section

namespace RHLean.Proof

/-- **Fresh-prime frozen-window recurrence.**  Adding `p` to the finite prime
universe subtracts exactly the old signed window seen through the reciprocal
compression `X ↦ floor(X/p)`. -/
theorem frozenPrimeUniverseWindowMass_insert
    {S : Finset ℕ} {p A B : ℕ}
    (hp : p ∉ S) (hpPrime : p.Prime) (hAB : A ≤ B) :
    frozenPrimeUniverseWindowMass (insert p S) A B =
      frozenPrimeUniverseWindowMass S A B -
        frozenPrimeUniverseWindowMass S (A / p) (B / p) := by
  have hdiv : A / p ≤ B / p := Nat.div_le_div_right hAB
  rw [frozenPrimeUniverseWindowMass_eq_sub hAB,
    frozenPrimeUniverseWindowMass_eq_sub hAB,
    frozenPrimeUniverseWindowMass_eq_sub hdiv,
    frozenPrimeUniverseMass_insert hp hpPrime,
    frozenPrimeUniverseMass_insert hp hpPrime]
  ring

/-- **Additive fresh-prime derivative.**  The change from the old window to the
new window is the negative compressed predecessor window. -/
theorem frozenPrimeUniverseWindowMass_insert_sub_old
    {S : Finset ℕ} {p A B : ℕ}
    (hp : p ∉ S) (hpPrime : p.Prime) (hAB : A ≤ B) :
    frozenPrimeUniverseWindowMass (insert p S) A B -
        frozenPrimeUniverseWindowMass S A B =
      -frozenPrimeUniverseWindowMass S (A / p) (B / p) := by
  rw [frozenPrimeUniverseWindowMass_insert hp hpPrime hAB]
  ring

/-- Reverse-sign form: deleting the fresh coordinate recovers exactly the
compressed predecessor window. -/
theorem frozenPrimeUniverseWindowMass_old_sub_insert
    {S : Finset ℕ} {p A B : ℕ}
    (hp : p ∉ S) (hpPrime : p.Prime) (hAB : A ≤ B) :
    frozenPrimeUniverseWindowMass S A B -
        frozenPrimeUniverseWindowMass (insert p S) A B =
      frozenPrimeUniverseWindowMass S (A / p) (B / p) := by
  rw [frozenPrimeUniverseWindowMass_insert hp hpPrime hAB]
  ring

/-- A zero compressed predecessor window means the fresh prime has no net
signed effect on the physical window.  This is the exact cancellation test to
apply before any magnitude estimate. -/
theorem frozenPrimeUniverseWindowMass_insert_eq_old_of_predecessor_zero
    {S : Finset ℕ} {p A B : ℕ}
    (hp : p ∉ S) (hpPrime : p.Prime) (hAB : A ≤ B)
    (hzero : frozenPrimeUniverseWindowMass S (A / p) (B / p) = 0) :
    frozenPrimeUniverseWindowMass (insert p S) A B =
      frozenPrimeUniverseWindowMass S A B := by
  rw [frozenPrimeUniverseWindowMass_insert hp hpPrime hAB, hzero]
  ring

end RHLean.Proof
