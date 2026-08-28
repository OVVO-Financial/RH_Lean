import Mathlib
import RHLean.Proof.SquareRootLowPrimeGoTwoBoundaryShell

/-!
# The Go second-boundary defect lives only in the fourth-power owner band

For a full birth-boundary child `n = r*d`, the existing Go geometry proves
`n < q^2`.  A surviving second-boundary defect simultaneously satisfies
`X < q^2*n`.  Therefore every such defect forces

`X < q^4`.

Combined with the unfinished-owner condition `q^3 <= X`, every genuinely live
two-boundary defect lies in the strict band

`q^3 <= X < q^4`.

At the square wall `X_R = R^2 - 1`, this deletes the entire owner range below
approximately `sqrt R` before any norm or divisor estimate is used.
-/

noncomputable section

namespace RHLean.Proof

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

end RHLean.Proof
