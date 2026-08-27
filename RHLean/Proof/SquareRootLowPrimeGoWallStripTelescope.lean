import Mathlib
import RHLean.Proof.LowPrimeParentChildWindowDifference
import RHLean.Proof.SquareRootPredecessorPrimeCells

/-!
# Go-wall strip telescope

The first-owner wall is already a no-liberty boundary.  Its old-prime windows
should therefore be treated as boundary strips rather than as another interior
matching problem.

For consecutive old primes `ell < q`, the strip

`F_{q^-}(X/q) - F_{q^-}(X/ell)`

has one exact fresh-prime decomposition.  The moving boundary term telescopes
across consecutive primes, while the sole non-endpoint residual is evaluated at
one additional division by `q`:

`F_{q^-}((X/q)/q)`.

This is the square-dilated Go residual.  Its literal old-face support maps to the
arithmetic child `m = q*c`.  The fresh prime `q` is exactly `P+(m)`, so children
belonging to distinct Go liberties are disjoint by canonical largest-prime
ownership.  Moreover `q*m <= X`: losing one liberty is recorded by one concrete
multiplicative square certificate.

No estimate is asserted here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- One old-prime Go boundary strip, written in the frozen predecessor universe
immediately before `q`. -/
def squareRootLowPrimeGoWallStripMass (ell q X : ℕ) : ℤ :=
  frozenPrimeUniverseMass (primesUpTo (q - 1)) (X / q) -
    frozenPrimeUniverseMass (primesUpTo (q - 1)) (X / ell)

/-- The moving boundary state after the prime `q` has itself been admitted. -/
def squareRootLowPrimeGoWallBoundaryState (q X : ℕ) : ℤ :=
  frozenPrimeUniverseMass (primesUpTo q) (X / q)

/-- The no-liberty residual after one additional attempted `q` contact. -/
def squareRootLowPrimeGoWallSquareResidual (q X : ℕ) : ℤ :=
  frozenPrimeUniverseMass (primesUpTo (q - 1)) ((X / q) / q)

/-- **Exact one-strip Go descent.**  If `ell` is the previous prime coordinate,
so the predecessor universe before `q` is exactly the universe through `ell`,
then the wall strip is the difference of adjacent moving boundary states plus
one square-dilated residual.

This is the quantitative seam: summing consecutive strips can telescope the
first two terms, while the surviving term has lost an additional factor `q` in
scale. -/
theorem squareRootLowPrimeGoWallStripMass_eq_boundaryDiff_add_squareResidual
    {ell q X : ℕ} (hq : q.Prime)
    (hpred : primesUpTo (q - 1) = primesUpTo ell) :
    squareRootLowPrimeGoWallStripMass ell q X =
      squareRootLowPrimeGoWallBoundaryState q X -
        squareRootLowPrimeGoWallBoundaryState ell X +
          squareRootLowPrimeGoWallSquareResidual q X := by
  have hstep :=
    frozenPrimeUniverseMass_primesUpTo_step_eq_sub_predecessor q (X / q) hq
  unfold predecessorPrimeMass at hstep
  unfold squareRootLowPrimeGoWallStripMass
    squareRootLowPrimeGoWallBoundaryState
    squareRootLowPrimeGoWallSquareResidual
  rw [hpred]
  rw [hpred] at hstep
  omega

/-- The square residual is literally the predecessor-prime mass at the already
reciprocal cutoff `X/q`. -/
theorem squareRootLowPrimeGoWallSquareResidual_eq_predecessorPrimeMass
    (q X : ℕ) :
    squareRootLowPrimeGoWallSquareResidual q X =
      predecessorPrimeMass q (X / q) := by
  rfl

/-- Equivalent `q^2` notation for the square-dilated cutoff. -/
theorem squareRootLowPrimeGoWallSquareResidual_eq_squareCutoff
    (q X : ℕ) :
    squareRootLowPrimeGoWallSquareResidual q X =
      frozenPrimeUniverseMass (primesUpTo (q - 1)) (X / (q * q)) := by
  unfold squareRootLowPrimeGoWallSquareResidual
  rw [Nat.div_div_eq_div_mul]

/-! ## Literal support and global Go ownership -/

/-- Old Boolean faces contributing to the square-dilated residual. -/
def squareRootLowPrimeGoWallSquareResidualFaces
    (q X : ℕ) : Finset (Finset ℕ) :=
  ((primesUpTo (q - 1)).powerset).filter fun u =>
    primeFaceProduct u ≤ X / (q * q)

@[simp] theorem mem_squareRootLowPrimeGoWallSquareResidualFaces
    {q X : ℕ} {u : Finset ℕ} :
    u ∈ squareRootLowPrimeGoWallSquareResidualFaces q X ↔
      u ∈ (primesUpTo (q - 1)).powerset ∧
        primeFaceProduct u ≤ X / (q * q) := by
  simp [squareRootLowPrimeGoWallSquareResidualFaces]

/-- Concrete arithmetic children `m=q*c` represented by one square residual. -/
def squareRootLowPrimeGoWallSquareResidualChildren
    (q X : ℕ) : Finset ℕ :=
  (squareRootLowPrimeGoWallSquareResidualFaces q X).image fun u =>
    q * primeFaceProduct u

@[simp] theorem mem_squareRootLowPrimeGoWallSquareResidualChildren
    {q X m : ℕ} :
    m ∈ squareRootLowPrimeGoWallSquareResidualChildren q X ↔
      ∃ u ∈ squareRootLowPrimeGoWallSquareResidualFaces q X,
        q * primeFaceProduct u = m := by
  simp [squareRootLowPrimeGoWallSquareResidualChildren]

/-- **Canonical Go owner.**  The prime whose second contact generated the
square residual is recoverable from its arithmetic child as the child's
canonical largest prime factor. -/
theorem squareRootLowPrimeGoWallSquareResidualChild_owner
    {q X m : ℕ} (hq : q.Prime)
    (hm : m ∈ squareRootLowPrimeGoWallSquareResidualChildren q X) :
    canonicalLargestPrimeFactor m = q := by
  rcases mem_squareRootLowPrimeGoWallSquareResidualChildren.mp hm with
    ⟨u, hu, rfl⟩
  have huData := mem_squareRootLowPrimeGoWallSquareResidualFaces.mp hu
  have hrough :=
    canonicalLargestPrimeFactor_primeFaceProduct_lt_freshPrime hq huData.1
  have hcPos : 0 < primeFaceProduct u :=
    primeFaceProduct_pos_of_mem_powerset huData.1
  simpa [Nat.mul_comm] using
    (canonicalLargestPrimeFactor_mul_prime_eq_of_rough hcPos hq hrough)

/-- **Square certificate.**  Every owned Go child still fits after one more
multiplication by its canonical owner: `q*m <= X`.  This is the literal loss of
one further liberty. -/
theorem squareRootLowPrimeGoWallSquareResidualChild_owner_mul_le
    {q X m : ℕ} (hq : q.Prime)
    (hm : m ∈ squareRootLowPrimeGoWallSquareResidualChildren q X) :
    q * m ≤ X := by
  rcases mem_squareRootLowPrimeGoWallSquareResidualChildren.mp hm with
    ⟨u, hu, rfl⟩
  have huCut :=
    (mem_squareRootLowPrimeGoWallSquareResidualFaces.mp hu).2
  have hqqPos : 0 < q * q := Nat.mul_pos hq.pos hq.pos
  have hmul : primeFaceProduct u * (q * q) ≤ X :=
    (Nat.le_div_iff_mul_le hqqPos).1 huCut
  simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul

/-- Distinct Go liberties own disjoint square-residual child populations.  The
prime coordinate is not an external multiplicity: it is encoded in `P+(m)`. -/
theorem squareRootLowPrimeGoWallSquareResidualChildren_disjoint
    {q r X : ℕ} (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r) :
    Disjoint (squareRootLowPrimeGoWallSquareResidualChildren q X)
      (squareRootLowPrimeGoWallSquareResidualChildren r X) := by
  rw [Finset.disjoint_left]
  intro m hmq hmr
  have hqOwner := squareRootLowPrimeGoWallSquareResidualChild_owner hq hmq
  have hrOwner := squareRootLowPrimeGoWallSquareResidualChild_owner hr hmr
  exact hqr (hqOwner.symm.trans hrOwner)

/-- Pairwise-disjoint form used when summing the square residuals over an actual
finite prime schedule. -/
theorem squareRootLowPrimeGoWallSquareResidualChildren_pairwiseDisjoint
    (Q : Finset ℕ) (X : ℕ) (hprime : ∀ q ∈ Q, q.Prime) :
    Set.PairwiseDisjoint (↑Q)
      (fun q => squareRootLowPrimeGoWallSquareResidualChildren q X) := by
  intro q hq r hr hqr
  exact squareRootLowPrimeGoWallSquareResidualChildren_disjoint
    (hprime q hq) (hprime r hr) hqr

end RHLean.Proof
