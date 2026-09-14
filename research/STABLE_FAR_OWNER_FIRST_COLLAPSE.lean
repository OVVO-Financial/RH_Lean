import «research.STABLE_FAR_RETURNED_FIBER_PRODUCTION»
import RHLean.Proof.SquareRootPredecessorPrimeCells

/-!
# Stable-far owner-first returned-window collapse

The returned-fibre Fubini developed in `STABLE_FAR_RETURNED_FIBER_PRODUCTION`
organizes strict crossings by the returned owner.  Here we reverse that Fubini
order and keep one old crossing owner `q` and one far-prime coordinate `p`
fixed.

For every returned prime `r < q`, the crossing cofactors occupy the frozen
window

`F_{r^-}(X/(q^2*p*r), X/(q*p*r)]`.

Summing these windows over all returned owners is not a new multiplicity
problem.  The existing high-window Euler telescope consumes the complete
`r < q` chronology exactly.  The residue is the empty-prime unit window minus
the single moving parent state `F_q(X/(q*p))`.

No norm, absolute value, asymptotic input, or Mertens estimate is used.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- **Owner-first collapse of every nonunit returned window.**

At fixed old owner `q` and far-prime coordinate `p`, summing all returned-owner
windows `r < q` telescopes exactly to the unit window minus the moving
`q`-boundary.  This is the arithmetic identity behind the occurrence-level
statement that the unit return and all nonunit returns recombine before any
energy is taken. -/
theorem stableFar_ownerFirst_returnedWindows_eq_unitWindow_sub_parent
    (X q p : ℕ) (hq : q.Prime) (hp : p.Prime) :
    (∑ r ∈ frozenPrimeUniverseHighPrimeSet 1 (q - 1),
      frozenPrimeUniverseWindowMass (primesUpTo (r - 1))
        (X / (q * q * p * r)) (X / (q * p * r))) =
      frozenPrimeUniverseWindowMass (primesUpTo 1)
        (X / (q * q * p)) (X / (q * p)) -
      frozenPrimeUniverseMass (primesUpTo q) (X / (q * p)) := by
  have hq2 : 2 ≤ q := hq.two_le
  have h1q : 1 ≤ q - 1 := by omega
  let A : ℕ := X / (q * q * p)
  let B : ℕ := X / (q * p)
  have hden : q * p ≤ q * q * p := by
    have hq1 : 1 ≤ q := hq.one_le
    nlinarith [hp.pos]
  have hdenPos : 0 < q * p := Nat.mul_pos hq.pos hp.pos
  have hAB : A ≤ B := by
    dsimp [A, B]
    exact Nat.div_le_div_left hden hdenPos
  have htel :=
    frozenPrimeUniverse_highWindow_telescope 1 (q - 1) A B h1q hAB
  have hBdiv : B / q = A := by
    dsimp [A, B]
    rw [Nat.div_div_eq_div_mul]
    congr 1
    ring
  have hstep :=
    frozenPrimeUniverseMass_primesUpTo_step_eq_sub_predecessor q B hq
  unfold predecessorPrimeMass at hstep
  rw [hBdiv] at hstep
  have hwindow :
      frozenPrimeUniverseWindowMass (primesUpTo (q - 1)) A B =
        frozenPrimeUniverseMass (primesUpTo q) B := by
    rw [frozenPrimeUniverseWindowMass_eq_sub hAB]
    exact hstep.symm
  rw [hwindow] at htel
  simpa [A, B, Nat.div_div_eq_div_mul, Nat.mul_assoc,
    Nat.mul_comm, Nat.mul_left_comm] using htel

end RHLean.Proof
