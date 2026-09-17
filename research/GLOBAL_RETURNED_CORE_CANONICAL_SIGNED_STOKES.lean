import Mathlib
import «research.GLOBAL_RETURNED_CORE_SIGNED_CELL_STOKES_BRIDGE»
import «research.CANONICAL_DESCENDING_PRIME_CHRONOLOGY»

/-!
# Canonical global signed Stokes ledger

This file chooses the repository's canonical descending prime chronology and,
inside one first-owner `p` cell, keeps exactly the larger owners `r > p`.
Those are precisely the owner coordinates that preserve the lower-prime
signature of the cell.

The cell-level exact Stokes theorem is then summed over all first owners and all
signatures.  The result is the requested global signed identity

  sum_{p,sigma} T_{R,p,sigma} = B_R + D_R,

where `B_R` is the accumulated signed escape ledger and `D_R` is the terminal
signed mixed-difference residual.  There is still no inequality in this file.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Canonical descending owner schedule remaining above first owner `p`. -/
def lowOwnerFirstOwnerCanonicalStokesSchedule
    (R p : ℕ) : List ℕ :=
  (squareRootCanonicalRoughDescendingPrimeSchedule R).filter (fun r => p < r)

/-- Every coordinate in the canonical cell schedule is prime. -/
theorem lowOwnerFirstOwnerCanonicalStokesSchedule_prime
    (R p : ℕ) :
    ∀ r ∈ lowOwnerFirstOwnerCanonicalStokesSchedule R p, r.Prime := by
  intro r hr
  have hr' : r ∈ squareRootCanonicalRoughDescendingPrimeSchedule R := by
    simpa [lowOwnerFirstOwnerCanonicalStokesSchedule] using hr
  exact (squareRootCanonicalRoughDescendingPrimeSchedule_complete R).1 r hr'

/-- Canonical signed escape ledger for one first-owner/signature cell. -/
def lowOwnerFirstOwnerCanonicalStokesBoundary
    (R p : ℕ) (sig : Finset ℕ) : ℝ :=
  iteratedPairWeightedStokesBoundary
    (lowOwnerFirstOwnerCanonicalStokesSchedule R p)
    (lowOwnerFirstOwnerSignedCellPairCarrier R p sig)
    (lowOwnerFirstOwnerDirichletPolarizationScalar R p)

/-- Canonical terminal signed interior for one first-owner/signature cell. -/
def lowOwnerFirstOwnerCanonicalStokesResidual
    (R p : ℕ) (sig : Finset ℕ) : ℝ :=
  iteratedPairWeightedStokesResidual
    (lowOwnerFirstOwnerCanonicalStokesSchedule R p)
    (lowOwnerFirstOwnerSignedCellPairCarrier R p sig)
    (lowOwnerFirstOwnerDirichletPolarizationScalar R p)

/-- Exact canonical `boundary + residual` form for one cell. -/
theorem lowOwnerFirstOwnerSignedCellTelescope_eq_canonicalStokesBoundary_add_residual
    {R p : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    lowOwnerFirstOwnerSignedCellTelescope R p sig =
      lowOwnerFirstOwnerCanonicalStokesBoundary R p sig +
        lowOwnerFirstOwnerCanonicalStokesResidual R p sig := by
  exact
    lowOwnerFirstOwnerSignedCellTelescope_eq_iteratedStokesBoundary_add_residual
      hp
      (lowOwnerFirstOwnerCanonicalStokesSchedule R p)
      (lowOwnerFirstOwnerCanonicalStokesSchedule_prime R p)

/-- Global accumulated signed Stokes boundary. -/
def lowOwnerCanonicalSignedStokesBoundary (R : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo (squareRootEndpoint R),
    ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
      lowOwnerFirstOwnerCanonicalStokesBoundary R p sig

/-- Global terminal signed Stokes interior. -/
def lowOwnerCanonicalSignedStokesResidual (R : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo (squareRootEndpoint R),
    ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
      lowOwnerFirstOwnerCanonicalStokesResidual R p sig

/-- **Global exact signed Stokes identity.**

This is the concrete repository-level version of

  sum T = B_R + D_R.

Every same-branch contribution has stayed inside exact finite differences or
literal escape faces.  No magnitude has yet been taken. -/
theorem sum_lowOwnerFirstOwnerSignedCellTelescope_eq_canonicalBoundary_add_residual
    (R : ℕ) :
    (∑ p ∈ primesUpTo (squareRootEndpoint R),
      ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
        lowOwnerFirstOwnerSignedCellTelescope R p sig) =
      lowOwnerCanonicalSignedStokesBoundary R +
        lowOwnerCanonicalSignedStokesResidual R := by
  unfold lowOwnerCanonicalSignedStokesBoundary
    lowOwnerCanonicalSignedStokesResidual
  calc
    (∑ p ∈ primesUpTo (squareRootEndpoint R),
      ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
        lowOwnerFirstOwnerSignedCellTelescope R p sig) =
      ∑ p ∈ primesUpTo (squareRootEndpoint R),
        ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
          (lowOwnerFirstOwnerCanonicalStokesBoundary R p sig +
            lowOwnerFirstOwnerCanonicalStokesResidual R p sig) := by
              apply Finset.sum_congr rfl
              intro p hpMem
              have hp : p.Prime := (mem_primesUpTo.mp hpMem).1
              apply Finset.sum_congr rfl
              intro sig _hsig
              exact
                lowOwnerFirstOwnerSignedCellTelescope_eq_canonicalStokesBoundary_add_residual
                  hp
    _ =
      (∑ p ∈ primesUpTo (squareRootEndpoint R),
        ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
          lowOwnerFirstOwnerCanonicalStokesBoundary R p sig) +
      (∑ p ∈ primesUpTo (squareRootEndpoint R),
        ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
          lowOwnerFirstOwnerCanonicalStokesResidual R p sig) := by
            simp_rw [Finset.sum_add_distrib]

end RHLean.Proof
