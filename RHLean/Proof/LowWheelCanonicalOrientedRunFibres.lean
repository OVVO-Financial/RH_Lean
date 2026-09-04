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
      lowWheelCanonicalDowncrossOrientedFrozenStateFibre, hempty]

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
        simp [lowWheelCanonicalDowncrossOrientedStateFibre,
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
  refine Finset.sum_subset Finset.subset_union_left ?_
  intro x hxUnion hxNot
  exact lowWheelCanonicalDowncrossOrientedFrozenStateFibre_eq_zero_of_not_mem hxNot

/-- Extend the upper endpoint oriented ledger to the common run carrier. -/
theorem lowWheelCanonicalDowncrossOrientedLedger_eq_sum_runCarrier_right
    (a b : ℕ) :
    lowWheelCanonicalDowncrossOrientedLedger (b + 1) =
      ∑ x ∈ canonicalOrientedRunStateCarrier a b,
        lowWheelCanonicalDowncrossOrientedFrozenStateFibre (b + 1) x := by
  rw [lowWheelCanonicalDowncrossOrientedLedger_eq_sum_frozenStateFibres]
  refine Finset.sum_subset Finset.subset_union_right ?_
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

/-! ## Sequential insertion law for predecessor density

This is the exact Euler-prime form of the dense-divisibility idea.  If `p` is
inserted after every coordinate already in `t`, all old predecessor products are
unchanged and the only new condition is

`p^d <= Y * primeFaceProduct t`.

Thus, once the old face is dense, failure after adjoining `p` is *exactly* one
large multiplicative jump relative to the entire predecessor cube. -/

/-- Inserting a later coordinate does not change the predecessor face of an
older coordinate. -/
theorem predecessorPrimeFace_insert_of_lt
    {t : Finset ℕ} {p q : ℕ} (hqp : q < p) :
    predecessorPrimeFace (insert p t) q = predecessorPrimeFace t q := by
  ext r
  constructor
  · intro hr
    rcases mem_predecessorPrimeFace.mp hr with ⟨hrins, hrq⟩
    rcases Finset.mem_insert.mp hrins with hrp | hrt
    · subst r
      omega
    · exact mem_predecessorPrimeFace.mpr ⟨hrt, hrq⟩
  · intro hr
    rcases mem_predecessorPrimeFace.mp hr with ⟨hrt, hrq⟩
    exact mem_predecessorPrimeFace.mpr ⟨Finset.mem_insert_of_mem hrt, hrq⟩

/-- If `p` is larger than the whole old face, its predecessor face after
insertion is literally the whole old face. -/
theorem predecessorPrimeFace_insert_top
    {t : Finset ℕ} {p : ℕ}
    (hpTop : ∀ q ∈ t, q < p) :
    predecessorPrimeFace (insert p t) p = t := by
  ext q
  constructor
  · intro hq
    rcases mem_predecessorPrimeFace.mp hq with ⟨hqins, hqp⟩
    rcases Finset.mem_insert.mp hqins with hEq | hqt
    · subst q
      omega
    · exact hqt
  · intro hqt
    exact mem_predecessorPrimeFace.mpr
      ⟨Finset.mem_insert_of_mem hqt, hpTop q hqt⟩

/-- Product form of `predecessorPrimeFace_insert_of_lt`. -/
theorem predecessorPrimeFaceProduct_insert_of_lt
    {t : Finset ℕ} {p q : ℕ} (hqp : q < p) :
    predecessorPrimeFaceProduct (insert p t) q =
      predecessorPrimeFaceProduct t q := by
  unfold predecessorPrimeFaceProduct
  rw [predecessorPrimeFace_insert_of_lt hqp]

/-- Product form of the top-insertion identity. -/
theorem predecessorPrimeFaceProduct_insert_top
    {t : Finset ℕ} {p : ℕ}
    (hpTop : ∀ q ∈ t, q < p) :
    predecessorPrimeFaceProduct (insert p t) p = primeFaceProduct t := by
  unfold predecessorPrimeFaceProduct
  rw [predecessorPrimeFace_insert_top hpTop]

/-- **Sequential Euler insertion law.**  Once `p` is the new largest
coordinate, predecessor density of the enlarged face is exactly old density
plus the single multiplicative condition at `p`. -/
theorem predecessorDenseFace_insert_top_iff
    {d Y p : ℕ} {t : Finset ℕ}
    (hpTop : ∀ q ∈ t, q < p) :
    PredecessorDenseFace d Y (insert p t) ↔
      PredecessorDenseFace d Y t ∧
        p ^ d ≤ Y * primeFaceProduct t := by
  unfold PredecessorDenseFace
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro q hqt
      have hq := h q (Finset.mem_insert_of_mem hqt)
      rw [predecessorPrimeFaceProduct_insert_of_lt (hpTop q hqt)] at hq
      exact hq
    · have hp := h p (by simp)
      rw [predecessorPrimeFaceProduct_insert_top hpTop] at hp
      exact hp
  · rintro ⟨ht, hp⟩ q hq
    rcases Finset.mem_insert.mp hq with hEq | hqt
    · subst q
      rw [predecessorPrimeFaceProduct_insert_top hpTop]
      exact hp
    · have hqp := hpTop q hqt
      rw [predecessorPrimeFaceProduct_insert_of_lt hqp]
      exact ht q hqt

/-- With the predecessor already dense, adjoining a new largest coordinate
fails density exactly when that coordinate is too large relative to the whole
predecessor product. -/
theorem not_predecessorDenseFace_insert_top_iff
    {d Y p : ℕ} {t : Finset ℕ}
    (hpTop : ∀ q ∈ t, q < p)
    (hdense : PredecessorDenseFace d Y t) :
    ¬ PredecessorDenseFace d Y (insert p t) ↔
      Y * primeFaceProduct t < p ^ d := by
  rw [predecessorDenseFace_insert_top_iff hpTop]
  simp only [hdense, true_and]
  omega

/-- Truncating at `p` and then looking below an earlier `q` gives the same
predecessor face as looking below `q` in the original face. -/
theorem predecessorPrimeFace_predecessor_of_lt
    {t : Finset ℕ} {p q : ℕ} (hqp : q < p) :
    predecessorPrimeFace (predecessorPrimeFace t p) q =
      predecessorPrimeFace t q := by
  ext r
  constructor
  · intro hr
    rcases mem_predecessorPrimeFace.mp hr with ⟨hrp, hrq⟩
    exact mem_predecessorPrimeFace.mpr
      ⟨(mem_predecessorPrimeFace.mp hrp).1, hrq⟩
  · intro hr
    rcases mem_predecessorPrimeFace.mp hr with ⟨hrt, hrq⟩
    exact mem_predecessorPrimeFace.mpr
      ⟨mem_predecessorPrimeFace.mpr ⟨hrt, hrq.trans hqp⟩, hrq⟩

/-- Product form of predecessor truncation stability. -/
theorem predecessorPrimeFaceProduct_predecessor_of_lt
    {t : Finset ℕ} {p q : ℕ} (hqp : q < p) :
    predecessorPrimeFaceProduct (predecessorPrimeFace t p) q =
      predecessorPrimeFaceProduct t q := by
  unfold predecessorPrimeFaceProduct
  rw [predecessorPrimeFace_predecessor_of_lt hqp]

/-- If every coordinate before `p` satisfies the density inequality, then the
entire predecessor face below `p` is itself predecessor-dense. -/
theorem predecessorPrimeFace_dense_of_previous
    {d Y p : ℕ} {t : Finset ℕ}
    (hprev : ∀ q ∈ t, q < p →
      q ^ d ≤ Y * predecessorPrimeFaceProduct t q) :
    PredecessorDenseFace d Y (predecessorPrimeFace t p) := by
  intro q hq
  rcases mem_predecessorPrimeFace.mp hq with ⟨hqt, hqp⟩
  rw [predecessorPrimeFaceProduct_predecessor_of_lt hqp]
  exact hprev q hqt hqp

/-- A non-dense face therefore has a first large multiplicative jump attached
to a predecessor face which is already dense. -/
theorem exists_first_predecessorDenseFailure_with_densePredecessor
    {d Y : ℕ} {t : Finset ℕ}
    (hnot : ¬ PredecessorDenseFace d Y t) :
    ∃ p ∈ t,
      Y * predecessorPrimeFaceProduct t p < p ^ d ∧
        PredecessorDenseFace d Y (predecessorPrimeFace t p) := by
  rcases exists_first_predecessorDenseFailure hnot with
    ⟨p, hpt, hfail, hprev⟩
  exact ⟨p, hpt, hfail, predecessorPrimeFace_dense_of_previous hprev⟩

/-- On an oriented charging face, the exceptional first jump is a strictly
smaller owner than the current fresh pivot *and* is attached to an already
dense predecessor cube. -/
theorem orientedChargingFace_dense_or_firstLowerJump_with_densePredecessor
    {R c k d Y : ℕ} {t : Finset ℕ}
    (ht : t ∈ lowWheelCanonicalDowncrossOrientedChargingFaces R (c, k)) :
    PredecessorDenseFace d Y t ∨
      ∃ p ∈ t,
        p < lowWheelCanonicalDowncrossPivot (c, k) ∧
        Y * predecessorPrimeFaceProduct t p < p ^ d ∧
          PredecessorDenseFace d Y (predecessorPrimeFace t p) := by
  rcases mem_lowWheelCanonicalDowncrossOrientedChargingFaces.mp ht with
    ⟨htPow, hx⟩
  by_cases hdense : PredecessorDenseFace d Y t
  · exact Or.inl hdense
  · right
    rcases exists_first_predecessorDenseFailure_with_densePredecessor hdense with
      ⟨p, hpt, hfail, hpredDense⟩
    have hpLt :=
      lowWheelCanonicalDowncrossOriented_facePrime_lt_pivot htPow hx hpt
    exact ⟨p, hpt, hpLt, hfail, hpredDense⟩

/-! ## Triply dense faces and the existing fourth-power wall

For `d = 3`, the prime-factor criterion has a fourth-power consequence after
one Euler insertion.  On the physical oriented carrier the natural scale is
`Y = c*k`: the complete state already satisfies

`(c * primeFaceProduct t) * k <= squareRootEndpoint R`.

Therefore every prime coordinate of a triply predecessor-dense face satisfies
`p^4 <= squareRootEndpoint R`.  Any face containing a fourth-power-unsafe prime
must lie in the first-jump branch.  This is the exact exponent already exposed
by the repository's Go fourth-power cutoff.
-/

/-- For a face of prime coordinates, adjoining `p` to its strict predecessor
face gives a subproduct of the full face product. -/
theorem prime_mul_predecessorPrimeFaceProduct_le
    {t : Finset ℕ} {p : ℕ}
    (hprime : ∀ q ∈ t, q.Prime) (hpt : p ∈ t) :
    p * predecessorPrimeFaceProduct t p ≤ primeFaceProduct t := by
  have hsub : insert p (predecessorPrimeFace t p) ⊆ t := by
    intro q hq
    rcases Finset.mem_insert.mp hq with hEq | hpred
    · subst q
      exact hpt
    · exact (mem_predecessorPrimeFace.mp hpred).1
  have hdiv :
      primeFaceProduct (insert p (predecessorPrimeFace t p)) ∣
        primeFaceProduct t := by
    unfold primeFaceProduct
    exact Finset.prod_dvd_prod_of_subset _ _ id hsub
  have hprodPos : 0 < primeFaceProduct t := by
    unfold primeFaceProduct
    exact Finset.prod_pos fun q hq => (hprime q hq).pos
  have hle := Nat.le_of_dvd hprodPos hdiv
  have hpNot : p ∉ predecessorPrimeFace t p := by simp
  simpa [primeFaceProduct, predecessorPrimeFaceProduct, hpNot] using hle

/-- Every coordinate of a predecessor-dense prime face obeys the corresponding
`d+1` power bound against the complete face product. -/
theorem predecessorDenseFace_coordinate_power_succ_le
    {d Y p : ℕ} {t : Finset ℕ}
    (hprime : ∀ q ∈ t, q.Prime)
    (hdense : PredecessorDenseFace d Y t) (hpt : p ∈ t) :
    p ^ (d + 1) ≤ Y * primeFaceProduct t := by
  have hd := hdense p hpt
  have hprefix := prime_mul_predecessorPrimeFaceProduct_le hprime hpt
  calc
    p ^ (d + 1) = p ^ d * p := by rw [pow_succ]
    _ ≤ (Y * predecessorPrimeFaceProduct t p) * p :=
      Nat.mul_le_mul_right p hd
    _ = Y * (p * predecessorPrimeFaceProduct t p) := by ring
    _ ≤ Y * primeFaceProduct t := Nat.mul_le_mul_left Y hprefix

/-- **Triply dense oriented faces are fourth-power safe.**  With the physical
state scale `Y=c*k`, every prime coordinate lies below the exact fourth-power
wall of the square endpoint. -/
theorem orientedChargingFace_triplyDense_facePrimeFourth_le_endpoint
    {R c k p : ℕ} {t : Finset ℕ}
    (ht : t ∈ lowWheelCanonicalDowncrossOrientedChargingFaces R (c, k))
    (hdense : PredecessorDenseFace 3 (c * k) t) (hpt : p ∈ t) :
    p ^ 4 ≤ squareRootEndpoint R := by
  rcases mem_lowWheelCanonicalDowncrossOrientedChargingFaces.mp ht with
    ⟨htPow, hx⟩
  have hsub := Finset.mem_powerset.mp htPow
  have hprime : ∀ q ∈ t, q.Prime := by
    intro q hqt
    exact prime_of_mem_primesUpTo (hsub hqt)
  have hpower :=
    predecessorDenseFace_coordinate_power_succ_le hprime hdense hpt
  have hdown := (mem_lowWheelCanonicalDowncrossOrientedPart.mp hx).1
  have hphys := (mem_lowWheelCanonicalDowncrossPart.mp hdown).1
  have hcarrier := (mem_lowWheelCanonicalPhysicalStateSet.mp hphys).2.2.2
  have htop := hcarrier.2.2.2
  calc
    p ^ 4 ≤ (c * k) * primeFaceProduct t := by simpa using hpower
    _ = (c * primeFaceProduct t) * k := by ring
    _ ≤ squareRootEndpoint R := htop

/-- A fourth-power-unsafe prime coordinate is an exact certificate that the
face is not triply predecessor-dense at its physical state scale. -/
theorem orientedChargingFace_fourthUnsafe_not_triplyDense
    {R c k p : ℕ} {t : Finset ℕ}
    (ht : t ∈ lowWheelCanonicalDowncrossOrientedChargingFaces R (c, k))
    (hpt : p ∈ t) (hunsafe : squareRootEndpoint R < p ^ 4) :
    ¬ PredecessorDenseFace 3 (c * k) t := by
  intro hdense
  have hsafe :=
    orientedChargingFace_triplyDense_facePrimeFourth_le_endpoint
      ht hdense hpt
  omega

/-- Consequently a fourth-power-unsafe coordinate forces the canonical
first-jump alternative: a strictly lower owner with an already-dense
predecessor cube. -/
theorem orientedChargingFace_fourthUnsafe_forces_firstLowerJump
    {R c k p : ℕ} {t : Finset ℕ}
    (ht : t ∈ lowWheelCanonicalDowncrossOrientedChargingFaces R (c, k))
    (hpt : p ∈ t) (hunsafe : squareRootEndpoint R < p ^ 4) :
    ∃ q ∈ t,
      q < lowWheelCanonicalDowncrossPivot (c, k) ∧
      (c * k) * predecessorPrimeFaceProduct t q < q ^ 3 ∧
        PredecessorDenseFace 3 (c * k) (predecessorPrimeFace t q) := by
  have hnot :=
    orientedChargingFace_fourthUnsafe_not_triplyDense ht hpt hunsafe
  rcases orientedChargingFace_dense_or_firstLowerJump_with_densePredecessor
      (d := 3) (Y := c * k) ht with hdense | hjump
  · exact (hnot hdense).elim
  · exact hjump

end RHLean.Proof