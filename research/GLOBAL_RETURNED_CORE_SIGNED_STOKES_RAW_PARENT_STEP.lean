import Mathlib
import «research.GLOBAL_RETURNED_CORE_RAW_PARENT_FOUR_CORNER_OCCUPANCY»

/-!
# Exact signed Stokes step on one returned-core owner

This file deliberately stays before every positive-energy gate.

For one first-owner cell `(p,sig)` and one descending owner `r`, the existing
revealed-prime filtration gives

  before r = post-r same-branch survivor + r-crossing owner fibre.

The post-r survivor is already partitioned exactly into

  orbit-covered even corners + inert survivor,

while the current owner fibre supplies the odd corners.  The raw-parent
occupancy theorem gives one common Fubini for those odd/even pieces.  Combining
them yields the exact local Stokes form

  before r = sum_{raw parents} physical four-corner orbit + inert survivor.

The word "four-corner" here means the physical subset of the Boolean orbit:
no completeness assumption is made and no missing corner is silently inserted.
The inert packet is transported as a signed survivor, not estimated.

There is no absolute value, square, contraction, or reciprocal-energy object in
this file.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Signed polarization mass physically present over one orientation-preserving
raw parent at the current owner `r`: odd owner-fibre corners plus even survivor
corners.  A completed block has all four Boolean corners; an incomplete block is
kept literally as the subset that is actually present. -/
def lowOwnerFirstOwnerRawParentPhysicalOrbitMass
    (R p : ℕ) (sig S : Finset ℕ) (r : ℕ)
    (parent : ℕ × ℕ) : ℝ :=
  (∑ mn ∈ lowOwnerFirstOwnerPolarizationFixedRawParentFiber
      R p sig r parent,
    lowOwnerFirstOwnerDirichletPolarizationAtom R p mn) +
  ∑ mn ∈ lowOwnerFirstOwnerRawParentOrbitEvenFixedFiber
      R p sig S r parent,
    lowOwnerFirstOwnerDirichletPolarizationAtom R p mn

/-- Signed polarization mass on the exact inert post-r survivor. -/
def lowOwnerFirstOwnerRawParentInertMass
    (R p : ℕ) (sig S : Finset ℕ) (r : ℕ) : ℝ :=
  ∑ mn ∈ lowOwnerFirstOwnerRawParentOrbitInertCarrier R p sig S r,
    lowOwnerFirstOwnerDirichletPolarizationAtom R p mn

/-- **Exact one-owner signed Stokes identity.**

With all larger primes revealed, the entire signed polarization before `r` is
exactly the sum of the physical raw-parent orbits plus the literal inert
same-branch survivor.  No population is normed or discarded. -/
theorem lowOwnerFirstOwnerRevealedPolarizationEnergy_descending_eq_rawParentOrbits_add_inert
    {R p r : ℕ} {sig : Finset ℕ} (hr : r.Prime) :
    lowOwnerFirstOwnerRevealedPolarizationEnergy R p sig
        (lowOwnerRevealedPrimesAbove R r) =
      (∑ parent ∈ lowOwnerFirstOwnerPolarizationRawParentSet R p sig r,
        lowOwnerFirstOwnerRawParentPhysicalOrbitMass R p sig
          (lowOwnerRevealedPrimesAbove R r) r parent) +
      lowOwnerFirstOwnerRawParentInertMass R p sig
        (lowOwnerRevealedPrimesAbove R r) r := by
  rw [lowOwnerFirstOwnerRevealedPolarizationEnergy_descending_eq_orbitEven_add_inert_add_ownerFiber
      hr]
  rw [sum_lowOwnerFirstOwnerOwnerFiber_add_orbitEven_eq_rawParentOrbits
      R p sig (lowOwnerRevealedPrimesAbove R r) r
      (lowOwnerFirstOwnerDirichletPolarizationAtom R p)]
  unfold lowOwnerFirstOwnerRawParentPhysicalOrbitMass
    lowOwnerFirstOwnerRawParentInertMass
  ring

/-- The same identity with the physical-orbit definition expanded.  This form
is convenient for later completed/incomplete parent partitions and makes it
syntactically explicit that the first inequality has not yet occurred. -/
theorem lowOwnerFirstOwnerRevealedPolarizationEnergy_descending_eq_rawParentOrbitSums_add_inert
    {R p r : ℕ} {sig : Finset ℕ} (hr : r.Prime) :
    lowOwnerFirstOwnerRevealedPolarizationEnergy R p sig
        (lowOwnerRevealedPrimesAbove R r) =
      (∑ parent ∈ lowOwnerFirstOwnerPolarizationRawParentSet R p sig r,
        ((∑ mn ∈ lowOwnerFirstOwnerPolarizationFixedRawParentFiber
              R p sig r parent,
            lowOwnerFirstOwnerDirichletPolarizationAtom R p mn) +
          ∑ mn ∈ lowOwnerFirstOwnerRawParentOrbitEvenFixedFiber
              R p sig (lowOwnerRevealedPrimesAbove R r) r parent,
            lowOwnerFirstOwnerDirichletPolarizationAtom R p mn)) +
      ∑ mn ∈ lowOwnerFirstOwnerRawParentOrbitInertCarrier R p sig
          (lowOwnerRevealedPrimesAbove R r) r,
        lowOwnerFirstOwnerDirichletPolarizationAtom R p mn := by
  simpa [lowOwnerFirstOwnerRawParentPhysicalOrbitMass,
    lowOwnerFirstOwnerRawParentInertMass] using
    (lowOwnerFirstOwnerRevealedPolarizationEnergy_descending_eq_rawParentOrbits_add_inert
      (R := R) (p := p) (r := r) (sig := sig) hr)

end RHLean.Proof
