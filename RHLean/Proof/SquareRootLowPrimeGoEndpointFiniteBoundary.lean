import Mathlib
import RHLean.Proof.SquareRootLowPrimeGoAncestryClock

/-!
# First finite boundary for exposed Go parent sources

After the `r`-coordinate has been recombined, a surviving two-boundary edge
carries the parent source

`m = q * d`.

The full birth-boundary geometry gives `d < q`, while unfinished Go territory
has `q^3 <= X`.  Hence

`m < q^2`

and therefore, without introducing any analytic estimate,

`m^3 < X^2`.

At the square wall `X = R^2 - 1` this is the integral form of the loose but
genuine boundary `m < R^(4/3)`.  The point is not yet the exponent: the exposed
parent is now a single canonical arithmetic source, with outer owner recoverable
as its largest prime factor, and it lies in a finite power window.  This is the
first boundary to tighten after global endpoint extraction.
-/

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic

/-- A surviving two-boundary edge has a canonical exposed parent source below
`q^2`; its largest prime factor is exactly the outer Go owner `q`. -/
theorem squareRootLowPrimeGoSecondBoundaryDefect_parentSource_coordinates
    {q X r d : ℕ} (hq : q.Prime) (hr : r.Prime) (hrq : r < q)
    (hd : d ∈ squareRootLowPrimeGoSecondBoundaryDefectParents q X r) :
    canonicalLargestPrimeFactor (q * d) = q ∧ q * d < q ^ 2 := by
  have hfull : d ∈ squareRootLowPrimeGoFullBirthBoundaryParents q r :=
    (mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp hd).1
  have hroot :=
    squareRootLowPrimeGoFullBirthBoundary_parent_canonicalRoot hq hr hrq hfull
  have hdPos : 0 < d := by omega
  have hroughQ : canonicalLargestPrimeFactor d < q := by
    rcases mem_squareRootLowPrimeGoFullBirthBoundaryParents.mp hfull with
      ⟨_hd1, _hdq, _hsq, hroughR, _hlower⟩
    exact hroughR.trans hrq
  constructor
  · have howner :=
      canonicalLargestPrimeFactor_mul_prime_eq_of_rough hdPos hq hroughQ
    simpa [Nat.mul_comm] using howner
  · rw [pow_two]
    exact Nat.mul_lt_mul_of_pos_left hroot.2 hq.pos

/-- **First finite Go endpoint cage.**  If the outer owner is genuinely
unfinished, every exposed parent source `m = q*d` from the surviving
second-boundary population satisfies the integral power bound

`m^3 < X^2`.

Equivalently, the parent-source boundary has scale strictly below `X^(2/3)`.
No prime-density estimate, divisor estimate, or cancellation hypothesis enters
this statement. -/
theorem squareRootLowPrimeGoSecondBoundaryDefect_parentSource_cube_lt_cutoffSquare
    {q X r d : ℕ} (hq : q.Prime) (hr : r.Prime) (hrq : r < q)
    (hcube : q ^ 3 ≤ X)
    (hd : d ∈ squareRootLowPrimeGoSecondBoundaryDefectParents q X r) :
    (q * d) ^ 3 < X ^ 2 := by
  have hsource :=
    (squareRootLowPrimeGoSecondBoundaryDefect_parentSource_coordinates
      hq hr hrq hd).2
  have hsourceCube : (q * d) ^ 3 < (q ^ 2) ^ 3 :=
    Nat.pow_lt_pow_left hsource (by omega)
  have hownerSquare : (q ^ 3) ^ 2 ≤ X ^ 2 :=
    Nat.pow_le_pow_left hcube 2
  calc
    (q * d) ^ 3 < (q ^ 2) ^ 3 := hsourceCube
    _ = (q ^ 3) ^ 2 := by ring
    _ ≤ X ^ 2 := hownerSquare

end RHLean.Proof
