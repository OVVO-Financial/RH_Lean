import Mathlib
import RHLean.Analysis.FrozenSquareRunDowncrossBridge
import RHLean.Proof.LowWheelCanonicalOrientedFrozenFibres

/-!
# Common frozen-owner carrier for the oriented square-run difference

`LowWheelCanonicalOrientedFrozenFibres` identifies the signed Boolean faces
charging one fixed oriented state with one frozen predecessor window through
its canonical pivot.  This file performs the remaining finite Fubini step.

At one root `R`, the oriented ledger is regrouped by physical states `(c,k)`.
The signed face mass of each state is then replaced by its exact frozen
predecessor-window mass.  For two endpoints `a` and `b+1`, both endpoint sums
are extended to the union of their state carriers.  Hence

`O_{b+1} - O_a`

is one signed sum on a common carrier, and each state keeps the *same* canonical
owner `p = minFac(c*k)` at both endpoints.  Only its two frozen window endpoints
move with `R`.

This is the representation needed by the recursive Go laws: predecessor-cube
cancellation is preserved state-by-state before any norm is taken.

No triangle inequality, PNT input, prime-gap estimate, or asymptotic hypothesis
appears.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis
open LowWheelCanonicalDowncrossOwnership
open SignedOwnershipInterval

attribute [local instance] Classical.propDecidable

/-- Fixed rectangular state ambient large enough for every oriented downcross
state at root `R`. -/
def lowWheelCanonicalDowncrossOrientedStateAmbient
    (R : ℕ) : Finset LowWheelCofactorQuotientState :=
  (Finset.Ico 1 R) ×ˢ (Finset.Icc 1 (squareRootEndpoint R))

/-- The physical states actually charged by at least one oriented Boolean face. -/
def lowWheelCanonicalDowncrossOrientedStateCarrier
    (R : ℕ) : Finset LowWheelCofactorQuotientState :=
  (lowWheelCanonicalDowncrossOrientedStateAmbient R).filter fun x =>
    (lowWheelCanonicalDowncrossOrientedChargingFaces R x).Nonempty

@[simp] theorem mem_lowWheelCanonicalDowncrossOrientedStateCarrier
    {R : ℕ} {x : LowWheelCofactorQuotientState} :
    x ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R ↔
      x ∈ lowWheelCanonicalDowncrossOrientedStateAmbient R ∧
        (lowWheelCanonicalDowncrossOrientedChargingFaces R x).Nonempty := by
  simp [lowWheelCanonicalDowncrossOrientedStateCarrier]

/-- Every oriented downcross state lies in the fixed rectangular ambient. -/
theorem lowWheelCanonicalDowncrossOrientedPart_subset_stateAmbient
    {R : ℕ} {t : Finset ℕ} :
    lowWheelCanonicalDowncrossOrientedPart R t ⊆
      lowWheelCanonicalDowncrossOrientedStateAmbient R := by
  intro x hx
  have hdown := (mem_lowWheelCanonicalDowncrossOrientedPart.mp hx).1
  have hphys :=
    mem_lowWheelCanonicalPhysicalStateSet.mp
      (mem_lowWheelCanonicalDowncrossPart.mp hdown).1
  exact Finset.mem_product.mpr ⟨hphys.1, hphys.2.1⟩

/-- Filtering the rectangular ambient by one face recovers exactly that face's
oriented state part. -/
theorem filter_stateAmbient_mem_orientedPart
    (R : ℕ) (t : Finset ℕ) :
    (lowWheelCanonicalDowncrossOrientedStateAmbient R).filter
        (fun x => x ∈ lowWheelCanonicalDowncrossOrientedPart R t) =
      lowWheelCanonicalDowncrossOrientedPart R t := by
  ext x
  constructor
  · intro hx
    exact (Finset.mem_filter.mp hx).2
  · intro hx
    exact Finset.mem_filter.mpr
      ⟨lowWheelCanonicalDowncrossOrientedPart_subset_stateAmbient hx, hx⟩

/-- Nonempty oriented charging automatically puts a state in the canonical
state carrier. -/
theorem mem_orientedStateCarrier_of_chargingFaces_nonempty
    {R : ℕ} {x : LowWheelCofactorQuotientState}
    (hne : (lowWheelCanonicalDowncrossOrientedChargingFaces R x).Nonempty) :
    x ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R := by
  rcases hne with ⟨t, ht⟩
  rcases mem_lowWheelCanonicalDowncrossOrientedChargingFaces.mp ht with
    ⟨_htPow, hx⟩
  apply mem_lowWheelCanonicalDowncrossOrientedStateCarrier.mpr
  exact ⟨lowWheelCanonicalDowncrossOrientedPart_subset_stateAmbient hx,
    ⟨t, ht⟩⟩

/-- Complex signed Boolean-face mass attached to one physical oriented state. -/
def lowWheelCanonicalDowncrossOrientedStateFaceMass
    (R : ℕ) (x : LowWheelCofactorQuotientState) : ℂ :=
  ∑ t ∈ lowWheelCanonicalDowncrossOrientedChargingFaces R x,
    (booleanCubeSign t : ℂ)

/-- State contribution before replacing its Boolean cube by the frozen
predecessor window. -/
def lowWheelCanonicalDowncrossOrientedStateFibre
    (R : ℕ) (x : LowWheelCofactorQuotientState) : ℂ :=
  canonicalMoebiusWeight x.1 *
    lowWheelCanonicalDowncrossOrientedStateFaceMass R x

/-- The exact frozen predecessor-window contribution of one state.  It is zero
when the state is not actually present at root `R`. -/
def lowWheelCanonicalDowncrossOrientedFrozenStateFibre
    (R : ℕ) (x : LowWheelCofactorQuotientState) : ℂ :=
  if (lowWheelCanonicalDowncrossOrientedChargingFaces R x).Nonempty then
    canonicalMoebiusWeight x.1 *
      ((frozenPrimeUniverseWindowMass
        (primesUpTo (lowWheelCanonicalDowncrossPivot x - 1))
        (R / x.2)
        (lowWheelCanonicalDowncrossOwnershipUpper R x.1 x.2) : ℤ) : ℂ)
  else 0

/-- Complex form of the one-state frozen predecessor-window theorem. -/
theorem lowWheelCanonicalDowncrossOrientedStateFaceMass_eq_frozenWindowMass
    {R c k : ℕ}
    (hne : (lowWheelCanonicalDowncrossOrientedChargingFaces R (c, k)).Nonempty) :
    lowWheelCanonicalDowncrossOrientedStateFaceMass R (c, k) =
      ((frozenPrimeUniverseWindowMass
        (primesUpTo (lowWheelCanonicalDowncrossPivot (c, k) - 1))
        (R / k)
        (lowWheelCanonicalDowncrossOwnershipUpper R c k) : ℤ) : ℂ) := by
  have h :=
    sum_booleanCubeSign_orientedChargingFaces_eq_frozenWindowMass hne
  have hc := congrArg (fun z : ℤ => (z : ℂ)) h
  simpa [lowWheelCanonicalDowncrossOrientedStateFaceMass] using hc

/-- The state-fibre and frozen-window presentations agree for every state,
including absent states. -/
theorem lowWheelCanonicalDowncrossOrientedStateFibre_eq_frozenStateFibre
    (R : ℕ) (x : LowWheelCofactorQuotientState) :
    lowWheelCanonicalDowncrossOrientedStateFibre R x =
      lowWheelCanonicalDowncrossOrientedFrozenStateFibre R x := by
  by_cases hne : (lowWheelCanonicalDowncrossOrientedChargingFaces R x).Nonempty
  · rcases x with ⟨c, k⟩
    simp only [lowWheelCanonicalDowncrossOrientedFrozenStateFibre, hne, if_true]
    unfold lowWheelCanonicalDowncrossOrientedStateFibre
    rw [lowWheelCanonicalDowncrossOrientedStateFaceMass_eq_frozenWindowMass hne]
  · have hempty : lowWheelCanonicalDowncrossOrientedChargingFaces R x = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    simp [lowWheelCanonicalDowncrossOrientedStateFibre,
      lowWheelCanonicalDowncrossOrientedStateFaceMass,
      lowWheelCanonicalDowncrossOrientedFrozenStateFibre, hne, hempty]

/-- A state outside the oriented state carrier has zero state fibre. -/
theorem lowWheelCanonicalDowncrossOrientedStateFibre_eq_zero_of_not_mem
    {R : ℕ} {x : LowWheelCofactorQuotientState}
    (hx : x ∉ lowWheelCanonicalDowncrossOrientedStateCarrier R) :
    lowWheelCanonicalDowncrossOrientedStateFibre R x = 0 := by
  by_cases hne : (lowWheelCanonicalDowncrossOrientedChargingFaces R x).Nonempty
  · exact (hx (mem_orientedStateCarrier_of_chargingFaces_nonempty hne)).elim
  · have hempty : lowWheelCanonicalDowncrossOrientedChargingFaces R x = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    simp [lowWheelCanonicalDowncrossOrientedStateFibre,
      lowWheelCanonicalDowncrossOrientedStateFaceMass, hempty]

/-- The same zero-extension property in the frozen-window presentation. -/
theorem lowWheelCanonicalDowncrossOrientedFrozenStateFibre_eq_zero_of_not_mem
    {R : ℕ} {x : LowWheelCofactorQuotientState}
    (hx : x ∉ lowWheelCanonicalDowncrossOrientedStateCarrier R) :
    lowWheelCanonicalDowncrossOrientedFrozenStateFibre R x = 0 := by
  rw [← lowWheelCanonicalDowncrossOrientedStateFibre_eq_frozenStateFibre]
  exact lowWheelCanonicalDowncrossOrientedStateFibre_eq_zero_of_not_mem hx

/-- Extend one face's oriented-state sum to the fixed rectangular ambient. -/
theorem sum_orientedPart_eq_sum_stateAmbient_indicator
    (R : ℕ) (t : Finset ℕ) :
    (∑ x ∈ lowWheelCanonicalDowncrossOrientedPart R t,
        canonicalMoebiusWeight x.1 * (booleanCubeSign t : ℂ)) =
      ∑ x ∈ lowWheelCanonicalDowncrossOrientedStateAmbient R,
        if x ∈ lowWheelCanonicalDowncrossOrientedPart R t then
          canonicalMoebiusWeight x.1 * (booleanCubeSign t : ℂ)
        else 0 := by
  rw [← Finset.sum_filter,
    filter_stateAmbient_mem_orientedPart]

/-- **Finite Fubini by physical state.**  The oriented Euler ledger is exactly
the sum of its signed state fibres. -/
theorem lowWheelCanonicalDowncrossOrientedLedger_eq_sum_stateFibres
    (R : ℕ) :
    lowWheelCanonicalDowncrossOrientedLedger R =
      ∑ x ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R,
        lowWheelCanonicalDowncrossOrientedStateFibre R x := by
  classical
  unfold lowWheelCanonicalDowncrossOrientedLedger
  calc
    (∑ t ∈ (primesUpTo R).powerset,
        ∑ x ∈ lowWheelCanonicalDowncrossOrientedPart R t,
          canonicalMoebiusWeight x.1 * (booleanCubeSign t : ℂ)) =
      ∑ t ∈ (primesUpTo R).powerset,
        ∑ x ∈ lowWheelCanonicalDowncrossOrientedStateAmbient R,
          if x ∈ lowWheelCanonicalDowncrossOrientedPart R t then
            canonicalMoebiusWeight x.1 * (booleanCubeSign t : ℂ)
          else 0 := by
      apply Finset.sum_congr rfl
      intro t _ht
      exact sum_orientedPart_eq_sum_stateAmbient_indicator R t
    _ = ∑ x ∈ lowWheelCanonicalDowncrossOrientedStateAmbient R,
        ∑ t ∈ (primesUpTo R).powerset,
          if x ∈ lowWheelCanonicalDowncrossOrientedPart R t then
            canonicalMoebiusWeight x.1 * (booleanCubeSign t : ℂ)
          else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ x ∈ lowWheelCanonicalDowncrossOrientedStateAmbient R,
        lowWheelCanonicalDowncrossOrientedStateFibre R x := by
      apply Finset.sum_congr rfl
      intro x _hx
      unfold lowWheelCanonicalDowncrossOrientedStateFibre
        lowWheelCanonicalDowncrossOrientedStateFaceMass
        lowWheelCanonicalDowncrossOrientedChargingFaces
      rw [← Finset.sum_filter, Finset.mul_sum]
    _ = ∑ x ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R,
        lowWheelCanonicalDowncrossOrientedStateFibre R x := by
      symm
      unfold lowWheelCanonicalDowncrossOrientedStateCarrier
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x _hx
      by_cases hne :
          (lowWheelCanonicalDowncrossOrientedChargingFaces R x).Nonempty
      · simp [hne]
      · have hempty : lowWheelCanonicalDowncrossOrientedChargingFaces R x = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp hne
        simp [hne, lowWheelCanonicalDowncrossOrientedStateFibre,
          lowWheelCanonicalDowncrossOrientedStateFaceMass, hempty]

/-- State-fibre Fubini with the predecessor cube made explicit. -/
theorem lowWheelCanonicalDowncrossOrientedLedger_eq_sum_frozenStateFibres
    (R : ℕ) :
    lowWheelCanonicalDowncrossOrientedLedger R =
      ∑ x ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R,
        lowWheelCanonicalDowncrossOrientedFrozenStateFibre R x := by
  rw [lowWheelCanonicalDowncrossOrientedLedger_eq_sum_stateFibres]
  apply Finset.sum_congr rfl
  intro x _hx
  exact lowWheelCanonicalDowncrossOrientedStateFibre_eq_frozenStateFibre R x

/-- Common physical state carrier for the two endpoints of a forward square
run.  A state may be born, persist, or die between the endpoints; absent
endpoint contributions are exactly zero. -/
def canonicalOrientedRunStateCarrier (a b : ℕ) :
    Finset LowWheelCofactorQuotientState :=
  lowWheelCanonicalDowncrossOrientedStateCarrier a ∪
    lowWheelCanonicalDowncrossOrientedStateCarrier (b + 1)

/-- Extend the lower endpoint oriented ledger to the common run carrier. -/
theorem lowWheelCanonicalDowncrossOrientedLedger_eq_sum_runCarrier_left
    (a b : ℕ) :
    lowWheelCanonicalDowncrossOrientedLedger a =
      ∑ x ∈ canonicalOrientedRunStateCarrier a b,
        lowWheelCanonicalDowncrossOrientedFrozenStateFibre a x := by
  rw [lowWheelCanonicalDowncrossOrientedLedger_eq_sum_frozenStateFibres]
  refine (Finset.sum_subset Finset.subset_union_left ?_).symm
  intro x hxUnion hxNot
  exact lowWheelCanonicalDowncrossOrientedFrozenStateFibre_eq_zero_of_not_mem hxNot

/-- Extend the upper endpoint oriented ledger to the common run carrier. -/
theorem lowWheelCanonicalDowncrossOrientedLedger_eq_sum_runCarrier_right
    (a b : ℕ) :
    lowWheelCanonicalDowncrossOrientedLedger (b + 1) =
      ∑ x ∈ canonicalOrientedRunStateCarrier a b,
        lowWheelCanonicalDowncrossOrientedFrozenStateFibre (b + 1) x := by
  rw [lowWheelCanonicalDowncrossOrientedLedger_eq_sum_frozenStateFibres]
  refine (Finset.sum_subset Finset.subset_union_right ?_).symm
  intro x hxUnion hxNot
  exact lowWheelCanonicalDowncrossOrientedFrozenStateFibre_eq_zero_of_not_mem hxNot

/-- **Common-owner frozen-strip representation of the square-run frontier.**

Both endpoint ledgers have been placed on one physical-state carrier.  For each
state `x`, its canonical owner `lowWheelCanonicalDowncrossPivot x` is fixed by
`x` itself, so the two terms are frozen windows in the same predecessor prime
universe `primesUpTo (pivot x - 1)`.

This is the exact representation on which the existing strictly-smaller-owner
Go recursion should now be iterated before taking an energy norm. -/
theorem canonicalOrientedRunDifference_eq_sum_frozenStateFibreDifferences
    (a b : ℕ) :
    canonicalOrientedRunDifference a b =
      ∑ x ∈ canonicalOrientedRunStateCarrier a b,
        (lowWheelCanonicalDowncrossOrientedFrozenStateFibre (b + 1) x -
          lowWheelCanonicalDowncrossOrientedFrozenStateFibre a x) := by
  unfold canonicalOrientedRunDifference
  rw [lowWheelCanonicalDowncrossOrientedLedger_eq_sum_runCarrier_right,
    lowWheelCanonicalDowncrossOrientedLedger_eq_sum_runCarrier_left,
    ← Finset.sum_sub_distrib]

end RHLean.Proof
