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

After the `r`-coordinate is recombined, the surviving edge carries the exposed
parent arithmetic source

`m = q*d`.

This source is canonical: `P+(m) = q`.  Its active parent clock and inactive
child clock imply the `r`-free second-contact shell

`q*m <= X < q^2*m`,

while the birth-boundary geometry gives `m < q^2`.  Hence every raw defect maps
into one finite arithmetic boundary depending only on `m` and its canonical
largest prime factor.  In particular

`X < m^3 < X^2`.

At the square wall `X_R = R^2 - 1`, this is the deliberately loose but genuine
cubic shell `R^(2/3) < m < R^(4/3)`.  The point is to expose a finite boundary
that can now be tightened; no asymptotic, prime-density, divisor, or cancellation
estimate enters here.
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

/-- The exposed parent source itself lies on an `r`-free second-contact shell.
The parent clock is active at `q*m`; the defect child enters after `X`, and
`r < q` enlarges that inactive clock to the canonical upper wall `q^2*m`. -/
theorem squareRootLowPrimeGoSecondBoundaryDefect_parentSource_contactShell
    {q X r d : ℕ} (hq : q.Prime) (hr : r.Prime) (hrq : r < q)
    (hcube : q ^ 3 ≤ X)
    (hd : d ∈ squareRootLowPrimeGoSecondBoundaryDefectParents q X r) :
    q * (q * d) ≤ X ∧ X < q ^ 2 * (q * d) := by
  have hfull : d ∈ squareRootLowPrimeGoFullBirthBoundaryParents q r :=
    (mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp hd).1
  have hparentClock :=
    squareRootLowPrimeGoFullBirthBoundary_parentClock_le hq hcube hfull
  have hparent : q * (q * d) ≤ X := by
    simpa [squareRootLowPrimeGoAncestryClock, Nat.mul_assoc] using hparentClock
  have hsecond :=
    squareRootLowPrimeGoSecondBoundaryDefect_secondContact_gt hq hr hd
  have hdPos : 0 < d := by
    have hd1 := (mem_squareRootLowPrimeGoFullBirthBoundaryParents.mp hfull).1
    omega
  have hrdLt : r * d < q * d :=
    Nat.mul_lt_mul_of_pos_right hrq hdPos
  have hq2Pos : 0 < q * q := Nat.mul_pos hq.pos hq.pos
  have hupper : q * q * (r * d) < q * q * (q * d) :=
    Nat.mul_lt_mul_of_pos_left hrdLt hq2Pos
  refine ⟨hparent, ?_⟩
  calc
    X < q * q * (r * d) := hsecond
    _ < q * q * (q * d) := hupper
    _ = q ^ 2 * (q * d) := by ring

/-- A finite `r`-free boundary containing every exposed parent source.  The
predicate depends only on the arithmetic source `m` and its canonical largest
prime factor. -/
def squareRootLowPrimeGoExposedParentBoundary (X : ℕ) : Finset ℕ :=
  (Finset.range (X + 1)).filter fun m =>
    let q := canonicalLargestPrimeFactor m
    q ^ 3 ≤ X ∧ X < q ^ 4 ∧
      q * m ≤ X ∧ X < q ^ 2 * m ∧ m < q ^ 2

/-- Every surviving two-boundary defect maps to the finite canonical exposed
parent boundary after forgetting the interior prime `r`. -/
theorem squareRootLowPrimeGoSecondBoundaryDefect_parentSource_mem_boundary
    {q X r d : ℕ} (hq : q.Prime) (hr : r.Prime) (hrq : r < q)
    (hcube : q ^ 3 ≤ X)
    (hd : d ∈ squareRootLowPrimeGoSecondBoundaryDefectParents q X r) :
    q * d ∈ squareRootLowPrimeGoExposedParentBoundary X := by
  have hcoords :=
    squareRootLowPrimeGoSecondBoundaryDefect_parentSource_coordinates
      hq hr hrq hd
  have hcontact :=
    squareRootLowPrimeGoSecondBoundaryDefect_parentSource_contactShell
      hq hr hrq hcube hd
  have hfourth :=
    squareRootLowPrimeGoSecondBoundaryDefect_ownerFourth_gt hq hr hrq hd
  have hmLeQm : q * d ≤ q * (q * d) := by
    calc
      q * d = 1 * (q * d) := by simp
      _ ≤ q * (q * d) := Nat.mul_le_mul_right (q * d) hq.one_le
  have hmLeX : q * d ≤ X := hmLeQm.trans hcontact.1
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
  dsimp
  rw [hcoords.1]
  exact ⟨hcube, hfourth, hcontact.1, hcontact.2, hcoords.2⟩

/-- The same finite boundary is a genuine cubic shell: every exposed parent
source lies strictly above `X^(1/3)` and below `X^(2/3)`, stated integrally as
`X < m^3 < X^2`. -/
theorem squareRootLowPrimeGoSecondBoundaryDefect_parentSource_cubeShell
    {q X r d : ℕ} (hq : q.Prime) (hr : r.Prime) (hrq : r < q)
    (hcube : q ^ 3 ≤ X)
    (hd : d ∈ squareRootLowPrimeGoSecondBoundaryDefectParents q X r) :
    X < (q * d) ^ 3 ∧ (q * d) ^ 3 < X ^ 2 := by
  have hcontact :=
    squareRootLowPrimeGoSecondBoundaryDefect_parentSource_contactShell
      hq hr hrq hcube hd
  have hsource :=
    (squareRootLowPrimeGoSecondBoundaryDefect_parentSource_coordinates
      hq hr hrq hd).2
  have hsourceCube : (q * d) ^ 3 < (q ^ 2) ^ 3 :=
    Nat.pow_lt_pow_left hsource (by omega)
  have hownerSquare : (q ^ 3) ^ 2 ≤ X ^ 2 :=
    Nat.pow_le_pow_left hcube 2
  have hdCube : d ≤ d ^ 3 :=
    Nat.le_self_pow (by norm_num : 3 ≠ 0) d
  have hlower : X < (q * d) ^ 3 := by
    calc
      X < q ^ 2 * (q * d) := hcontact.2
      _ = q ^ 3 * d := by ring
      _ ≤ q ^ 3 * d ^ 3 := Nat.mul_le_mul_left (q ^ 3) hdCube
      _ = (q * d) ^ 3 := by ring
  refine ⟨hlower, ?_⟩
  calc
    (q * d) ^ 3 < (q ^ 2) ^ 3 := hsourceCube
    _ = (q ^ 3) ^ 2 := by ring
    _ ≤ X ^ 2 := hownerSquare

/-- Upper half of the cubic shell, retained as a convenient standalone API. -/
theorem squareRootLowPrimeGoSecondBoundaryDefect_parentSource_cube_lt_cutoffSquare
    {q X r d : ℕ} (hq : q.Prime) (hr : r.Prime) (hrq : r < q)
    (hcube : q ^ 3 ≤ X)
    (hd : d ∈ squareRootLowPrimeGoSecondBoundaryDefectParents q X r) :
    (q * d) ^ 3 < X ^ 2 :=
  (squareRootLowPrimeGoSecondBoundaryDefect_parentSource_cubeShell
    hq hr hrq hcube hd).2

end RHLean.Proof
