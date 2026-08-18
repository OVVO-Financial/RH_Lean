import Mathlib
import RHLean.Analysis.PhysicalCenteredDistinguishedPrimeOperator

/-!
# Exact mass reconstruction from physical distinguished-prime transitions

The physical fixed-prime kernel is built from overlapping adjacent three-slot
cells.  This module records the exact signed mass ledger before any norm is
taken.  In particular, it keeps the endpoint cells that are not represented by
a transition when the carrier is empty, and it makes the factor-two overlap of
interior cells explicit.

This is finite arithmetic bookkeeping only.  No estimate, asymptotic cutoff,
stochastic interpretation, or new hypothesis is introduced.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

/-- Total signed mass on all adjacent physical six-site transitions for one
fixed distinguished-prime coordinate. -/
def physicalDistinguishedPrimeTransitionLedger
    (R q : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (physicalDistinguishedPrimeCarrierLength R),
    physicalDistinguishedPrimeLocalTransitionFibreMass R q k

/-- Inactive-to-inactive part of the same physical transition ledger. -/
def physicalDistinguishedPrimeInactiveInactiveLedger
    (R q : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (physicalDistinguishedPrimeCarrierLength R),
    if physicalDistinguishedPrimeState R q k = none ∧
        physicalDistinguishedPrimeState R q (k + 1) = none then
      physicalDistinguishedPrimeLocalTransitionFibreMass R q k
    else
      0

/-- Inactive-to-active part of the physical transition ledger, retaining the
actual destination state without splitting it into an abstract coefficient
family. -/
def physicalDistinguishedPrimeInactiveToActiveLedger
    (R q : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (physicalDistinguishedPrimeCarrierLength R),
    match physicalDistinguishedPrimeState R q k,
        physicalDistinguishedPrimeState R q (k + 1) with
    | none, some _ => physicalDistinguishedPrimeLocalTransitionFibreMass R q k
    | _, _ => 0

/-- Active-to-inactive part of the physical transition ledger. -/
def physicalDistinguishedPrimeActiveToInactiveLedger
    (R q : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (physicalDistinguishedPrimeCarrierLength R),
    match physicalDistinguishedPrimeState R q k,
        physicalDistinguishedPrimeState R q (k + 1) with
    | some _, none => physicalDistinguishedPrimeLocalTransitionFibreMass R q k
    | _, _ => 0

/-- Active-to-active mass discarded by the thirteen-coefficient restricted
projection.  It vanishes automatically in the large-prime support range, but is
kept here so that the arithmetic reconstruction is exact at every scale. -/
def physicalDistinguishedPrimeActiveActiveLedger
    (R q : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (physicalDistinguishedPrimeCarrierLength R),
    match physicalDistinguishedPrimeState R q k,
        physicalDistinguishedPrimeState R q (k + 1) with
    | some _, some _ => physicalDistinguishedPrimeLocalTransitionFibreMass R q k
    | _, _ => 0

/-- The four physical source/destination classes partition the signed adjacent
transition mass exactly, including the small-scale active-to-active defect. -/
theorem physicalDistinguishedPrimeTransitionLedger_partition
    (R q : ℕ) :
    physicalDistinguishedPrimeTransitionLedger R q =
      physicalDistinguishedPrimeInactiveInactiveLedger R q +
        physicalDistinguishedPrimeInactiveToActiveLedger R q +
        physicalDistinguishedPrimeActiveToInactiveLedger R q +
        physicalDistinguishedPrimeActiveActiveLedger R q := by
  classical
  unfold physicalDistinguishedPrimeTransitionLedger
    physicalDistinguishedPrimeInactiveInactiveLedger
    physicalDistinguishedPrimeInactiveToActiveLedger
    physicalDistinguishedPrimeActiveToInactiveLedger
    physicalDistinguishedPrimeActiveActiveLedger
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rcases hs : physicalDistinguishedPrimeState R q k with _ | s <;>
    rcases ht : physicalDistinguishedPrimeState R q (k + 1) with _ | t <;>
    simp [hs, ht]

/-- Signed physical cell mass before adjacent cells are overlapped into
transitions.  There is one more cell than transition. -/
def physicalDistinguishedPrimeCellLedger
    (R q : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (physicalDistinguishedPrimeCarrierLength R + 1),
    physicalDistinguishedPrimeCellFibreMass R q k

/-- The two endpoint-cell masses needed to invert the adjacent-cell overlap.
When the transition carrier is empty these are the same unique physical cell,
which is intentionally counted twice before division by two. -/
def physicalDistinguishedPrimeBoundaryCellLedger
    (R q : ℕ) : ℂ :=
  physicalDistinguishedPrimeCellFibreMass R q 0 +
    physicalDistinguishedPrimeCellFibreMass R q
      (physicalDistinguishedPrimeCarrierLength R)

/-- **Exact de-overlap identity.**  The transition ledger counts every interior
cell twice and each endpoint cell once.  Restoring the two endpoint masses gives
twice the actual physical cell ledger. -/
theorem physicalDistinguishedPrimeTransitionLedger_add_boundary_eq_two_cellLedger
    (R q : ℕ) :
    physicalDistinguishedPrimeTransitionLedger R q +
        physicalDistinguishedPrimeBoundaryCellLedger R q =
      2 * physicalDistinguishedPrimeCellLedger R q := by
  let K := physicalDistinguishedPrimeCarrierLength R
  let f : ℕ → ℂ := fun k => physicalDistinguishedPrimeCellFibreMass R q k
  have htail :
      (∑ k ∈ Finset.range (K + 1), f k) =
        (∑ k ∈ Finset.range K, f k) + f K := by
    simpa using (Finset.sum_range_succ f K)
  have hhead :
      (∑ k ∈ Finset.range (K + 1), f k) =
        f 0 + ∑ k ∈ Finset.range K, f (k + 1) := by
    simpa using (Finset.sum_range_succ' f K)
  change
    (∑ k ∈ Finset.range K, (f k + f (k + 1))) + (f 0 + f K) =
      2 * ∑ k ∈ Finset.range (K + 1), f k
  rw [Finset.sum_add_distrib]
  calc
    (∑ k ∈ Finset.range K, f k) +
          (∑ k ∈ Finset.range K, f (k + 1)) + (f 0 + f K) =
        ((∑ k ∈ Finset.range K, f k) + f K) +
          (f 0 + ∑ k ∈ Finset.range K, f (k + 1)) := by ring
    _ = (∑ k ∈ Finset.range (K + 1), f k) +
          ∑ k ∈ Finset.range (K + 1), f k := by
      rw [← htail, ← hhead]
    _ = 2 * ∑ k ∈ Finset.range (K + 1), f k := by ring

/-- Boundary-complete signed mass recovered from the adjacent transition ledger. -/
def physicalDistinguishedPrimeBoundaryCompleteMass
    (R q : ℕ) : ℂ :=
  (physicalDistinguishedPrimeTransitionLedger R q +
      physicalDistinguishedPrimeBoundaryCellLedger R q) / 2

/-- The boundary-complete transition ledger is exactly the actual physical cell
mass; no approximation or normalization remains. -/
theorem physicalDistinguishedPrimeBoundaryCompleteMass_eq_cellLedger
    (R q : ℕ) :
    physicalDistinguishedPrimeBoundaryCompleteMass R q =
      physicalDistinguishedPrimeCellLedger R q := by
  rw [physicalDistinguishedPrimeBoundaryCompleteMass,
    physicalDistinguishedPrimeTransitionLedger_add_boundary_eq_two_cellLedger]
  ring

/-- At `R = 2` there are no adjacent transitions at all.  This is the exact
small-scale obstruction to identifying the bare transition operator with the
physical signed state. -/
@[simp] theorem physicalDistinguishedPrimeTransitionLedger_two
    (q : ℕ) :
    physicalDistinguishedPrimeTransitionLedger 2 q = 0 := by
  norm_num [physicalDistinguishedPrimeTransitionLedger,
    physicalDistinguishedPrimeCarrierLength, RHLean.Proof.squareRootEndpoint]

/-- Nevertheless the boundary-complete ledger retains the unique physical cell
at `R = 2`, so the exact signal is not lost. -/
@[simp] theorem physicalDistinguishedPrimeCellLedger_two
    (q : ℕ) :
    physicalDistinguishedPrimeCellLedger 2 q =
      physicalDistinguishedPrimeCellFibreMass 2 q 0 := by
  norm_num [physicalDistinguishedPrimeCellLedger,
    physicalDistinguishedPrimeCarrierLength, RHLean.Proof.squareRootEndpoint]

end RHLean.Analysis
