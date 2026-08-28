import Mathlib
import RHLean.Proof.SquareRootLowPrimeGoAncestryClock

/-!
# The Go second-boundary defect lives only in the fourth-power owner band

For a full birth-boundary child `n = r*d`, the existing Go geometry proves
`n < q^2`.  A surviving second-boundary defect simultaneously satisfies
`X < q^2*n`.  Therefore every such defect forces

`X < q^4`.

Combined with the unfinished-owner condition `q^3 <= X`, every genuinely live
two-boundary defect lies in the strict band

`q^3 <= X < q^4`.

There is also a first finite cage for the exposed parent source.  After the
`r`-coordinate is recombined, the surviving edge carries the arithmetic source

`m = q*d`.

The birth-boundary geometry gives `d < q`, hence `m < q^2`; together with
`q^3 <= X` this implies the integral power bound

`m^3 < X^2`.

At the square wall `X_R = R^2 - 1`, this is the loose but genuine scale
`m < R^(4/3)`.  It is intentionally only a first finite boundary to tighten:
no asymptotic, prime-density, divisor, or cancellation estimate enters here.
-/

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic

/-- A surviving Go second-boundary defect forces the physical cutoff below the
fourth power of its outer owner. -/
theorem squareRootLowPrimeGoSecondBoundaryDefect_ownerFourth_gt
    {q X r d : ℕ} (hq : q.Prime) (hr : r.Prime) (hrq : r < q)
    (hd : d ∈ squareRootLowPrimeGoSecondBoundaryDefectParents q X r) :
    X < q ^ 4 := by
  have hfull :=
    (mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp hd).1
  have hsecond :=
    squareRootLowPrimeGoSecondBoundaryDefect_secondContact_gt hq hr hd
  have hchild :=
    squareRootLowPrimeGoFullBirthBoundary_child_lt_ownerSquare hq hrq hfull
  have hq2Pos : 0 < q * q := Nat.mul_pos hq.pos hq.pos
  have hupper : q * q * (r * d) < q * q * (q * q) :=
    Nat.mul_lt_mul_of_pos_left hchild hq2Pos
  calc
    X < q * q * (r * d) := hsecond
    _ < q * q * (q * q) := hupper
    _ = q ^ 4 := by ring

/-- Hence every genuinely unfinished owner carrying a surviving two-boundary
defect lies in the narrow power band `q^3 <= X < q^4`. -/
theorem squareRootLowPrimeGoSecondBoundaryDefect_ownerPowerBand
    {q X r d : ℕ} (hq : q.Prime) (hr : r.Prime) (hrq : r < q)
    (hcube : q ^ 3 ≤ X)
    (hd : d ∈ squareRootLowPrimeGoSecondBoundaryDefectParents q X r) :
    q ^ 3 ≤ X ∧ X < q ^ 4 := by
  exact ⟨hcube,
    squareRootLowPrimeGoSecondBoundaryDefect_ownerFourth_gt hq hr hrq hd⟩

/-- A surviving two-boundary edge has one exposed parent arithmetic source
`m = q*d`.  Its largest prime factor is exactly the outer Go owner and the
source lies strictly below the owner square.  Thus the outer coordinate is
recoverable from `m`; there is no additional `q` multiplicity in this source
encoding. -/
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

/-- **First finite Go endpoint cage.**  In genuinely unfinished territory,
every exposed parent source `m = q*d` from a surviving second-boundary edge
satisfies

`m^3 < X^2`.

This is the integral form of the scale `m < X^(2/3)`.  At a square endpoint
`X = R^2 - 1` it is the loose boundary `m < R^(4/3)`, which can be tightened
without changing the canonical source coordinate. -/
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
