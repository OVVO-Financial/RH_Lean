import Mathlib
import RHLean.Proof.LowWheelCanonicalOrientedRunFibres

/-!
# Ordered predecessor dense-divisibility on frozen Euler faces

The prime-gap picture only controls when consecutive prime children arrive.  It
does not control how long a newly exposed Euler face survives, because inserting
one fresh prime leaves a lower-cutoff copy of the whole predecessor cube.

This file records the elementary multiplicative alternative suggested by that
predecessor-cube law.  For a finite face `t` and one prime coordinate `p`, let

`P_<(t,p)`

be the product of the coordinates of `t` strictly below `p`.  Given an exponent
`d` and scale parameter `Y`, call the face predecessor-dense when

`p^d <= Y * P_<(t,p)`

at every coordinate of the face.  Otherwise there is a canonical *first*
coordinate where the inequality fails; every smaller coordinate still obeys
the dense inequality.  No prime spacing, PNT input, cardinality bound, or
analytic estimate enters.

The final section performs the split directly on one frozen predecessor window.
The signed Boolean mass is decomposed exactly into predecessor-dense faces and
first-jump faces before any absolute value is taken.  On a canonical oriented
state, every first-jump owner remains strictly below the state's fresh pivot,
so the bad branch still descends in the Euler owner order.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis
open LowWheelCanonicalDowncrossOwnership

attribute [local instance] Classical.propDecidable

/-- Coordinates of `t` that were already present before inserting `p`. -/
def predecessorPrimeFace (t : Finset ℕ) (p : ℕ) : Finset ℕ :=
  t.filter fun q => q < p

@[simp] theorem mem_predecessorPrimeFace
    {t : Finset ℕ} {p q : ℕ} :
    q ∈ predecessorPrimeFace t p ↔ q ∈ t ∧ q < p := by
  simp [predecessorPrimeFace]

/-- Product of all coordinates of `t` strictly preceding `p`. -/
def predecessorPrimeFaceProduct (t : Finset ℕ) (p : ℕ) : ℕ :=
  primeFaceProduct (predecessorPrimeFace t p)

/-- Ordered multiplicative density condition on a Boolean face. -/
def PredecessorDenseFace (d Y : ℕ) (t : Finset ℕ) : Prop :=
  ∀ p ∈ t, p ^ d ≤ Y * predecessorPrimeFaceProduct t p

/-- Coordinates at which predecessor dense-divisibility fails. -/
def predecessorDenseFailureSet
    (d Y : ℕ) (t : Finset ℕ) : Finset ℕ :=
  t.filter fun p =>
    Y * predecessorPrimeFaceProduct t p < p ^ d

@[simp] theorem mem_predecessorDenseFailureSet
    {d Y : ℕ} {t : Finset ℕ} {p : ℕ} :
    p ∈ predecessorDenseFailureSet d Y t ↔
      p ∈ t ∧ Y * predecessorPrimeFaceProduct t p < p ^ d := by
  simp [predecessorDenseFailureSet]

/-- Failure-set nonemptiness is exactly failure of predecessor density. -/
theorem predecessorDenseFailureSet_nonempty_iff_not_dense
    (d Y : ℕ) (t : Finset ℕ) :
    (predecessorDenseFailureSet d Y t).Nonempty ↔
      ¬ PredecessorDenseFace d Y t := by
  constructor
  · rintro ⟨p, hp⟩ hdense
    rcases mem_predecessorDenseFailureSet.mp hp with ⟨hpt, hfail⟩
    have hgood := hdense p hpt
    omega
  · intro hnot
    by_contra hnone
    have hempty : predecessorDenseFailureSet d Y t = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hnone
    apply hnot
    intro p hpt
    by_contra hbad
    have hfail : Y * predecessorPrimeFaceProduct t p < p ^ d := by
      omega
    have hpFail : p ∈ predecessorDenseFailureSet d Y t :=
      mem_predecessorDenseFailureSet.mpr ⟨hpt, hfail⟩
    rw [hempty] at hpFail
    simp at hpFail

/-- If density fails, the least failing coordinate is an exact first
multiplicative jump: it fails the inequality, while every earlier coordinate
still satisfies it. -/
theorem exists_first_predecessorDenseFailure
    {d Y : ℕ} {t : Finset ℕ}
    (hnot : ¬ PredecessorDenseFace d Y t) :
    ∃ p ∈ t,
      Y * predecessorPrimeFaceProduct t p < p ^ d ∧
      ∀ q ∈ t, q < p →
        q ^ d ≤ Y * predecessorPrimeFaceProduct t q := by
  have hne : (predecessorDenseFailureSet d Y t).Nonempty :=
    (predecessorDenseFailureSet_nonempty_iff_not_dense d Y t).2 hnot
  let p := (predecessorDenseFailureSet d Y t).min' hne
  have hpFail : p ∈ predecessorDenseFailureSet d Y t :=
    Finset.min'_mem _ hne
  rcases mem_predecessorDenseFailureSet.mp hpFail with ⟨hpt, hfail⟩
  refine ⟨p, hpt, hfail, ?_⟩
  intro q hqt hqp
  by_contra hqbad
  have hqFail : Y * predecessorPrimeFaceProduct t q < q ^ d := by
    omega
  have hqMem : q ∈ predecessorDenseFailureSet d Y t :=
    mem_predecessorDenseFailureSet.mpr ⟨hqt, hqFail⟩
  have hpLeQ : p ≤ q :=
    Finset.min'_le _ _ hqMem
  omega

/-- Exact ordered dichotomy: every face is predecessor-dense, or it has a
first multiplicative jump. -/
theorem predecessorDenseFace_or_exists_firstFailure
    (d Y : ℕ) (t : Finset ℕ) :
    PredecessorDenseFace d Y t ∨
      ∃ p ∈ t,
        Y * predecessorPrimeFaceProduct t p < p ^ d ∧
        ∀ q ∈ t, q < p →
          q ^ d ≤ Y * predecessorPrimeFaceProduct t q := by
  by_cases h : PredecessorDenseFace d Y t
  · exact Or.inl h
  · exact Or.inr (exists_first_predecessorDenseFailure h)

/-! ## Exact signed split of one frozen predecessor window -/

/-- Predecessor-dense faces in one frozen product window. -/
def predecessorDenseFrozenWindowFaces
    (d Y : ℕ) (S : Finset ℕ) (A B : ℕ) : Finset (Finset ℕ) :=
  (frozenPrimeUniverseWindowFaces S A B).filter
    (PredecessorDenseFace d Y)

/-- Complementary faces, each carrying a canonical first multiplicative jump. -/
def predecessorFirstJumpFrozenWindowFaces
    (d Y : ℕ) (S : Finset ℕ) (A B : ℕ) : Finset (Finset ℕ) :=
  (frozenPrimeUniverseWindowFaces S A B).filter fun t =>
    ¬ PredecessorDenseFace d Y t

@[simp] theorem mem_predecessorDenseFrozenWindowFaces
    {d Y : ℕ} {S : Finset ℕ} {A B : ℕ} {t : Finset ℕ} :
    t ∈ predecessorDenseFrozenWindowFaces d Y S A B ↔
      t ∈ frozenPrimeUniverseWindowFaces S A B ∧
        PredecessorDenseFace d Y t := by
  simp [predecessorDenseFrozenWindowFaces]

@[simp] theorem mem_predecessorFirstJumpFrozenWindowFaces
    {d Y : ℕ} {S : Finset ℕ} {A B : ℕ} {t : Finset ℕ} :
    t ∈ predecessorFirstJumpFrozenWindowFaces d Y S A B ↔
      t ∈ frozenPrimeUniverseWindowFaces S A B ∧
        ¬ PredecessorDenseFace d Y t := by
  simp [predecessorFirstJumpFrozenWindowFaces]

/-- The dense and first-jump populations partition the frozen window exactly. -/
theorem predecessorDense_union_firstJump_frozenWindow
    (d Y : ℕ) (S : Finset ℕ) (A B : ℕ) :
    predecessorDenseFrozenWindowFaces d Y S A B ∪
      predecessorFirstJumpFrozenWindowFaces d Y S A B =
        frozenPrimeUniverseWindowFaces S A B := by
  ext t
  by_cases h : PredecessorDenseFace d Y t
  · simp [predecessorDenseFrozenWindowFaces,
      predecessorFirstJumpFrozenWindowFaces, h]
  · simp [predecessorDenseFrozenWindowFaces,
      predecessorFirstJumpFrozenWindowFaces, h]

/-- The two frozen-window populations are disjoint. -/
theorem predecessorDense_disjoint_firstJump_frozenWindow
    (d Y : ℕ) (S : Finset ℕ) (A B : ℕ) :
    Disjoint
      (predecessorDenseFrozenWindowFaces d Y S A B)
      (predecessorFirstJumpFrozenWindowFaces d Y S A B) := by
  rw [Finset.disjoint_left]
  intro t hdense hjump
  have hd := (mem_predecessorDenseFrozenWindowFaces.mp hdense).2
  have hj := (mem_predecessorFirstJumpFrozenWindowFaces.mp hjump).2
  exact hj hd

/-- Signed mass of the predecessor-dense part of a frozen window. -/
def predecessorDenseFrozenWindowMass
    (d Y : ℕ) (S : Finset ℕ) (A B : ℕ) : ℤ :=
  ∑ t ∈ predecessorDenseFrozenWindowFaces d Y S A B,
    booleanCubeSign t

/-- Signed mass of the first-jump part of a frozen window. -/
def predecessorFirstJumpFrozenWindowMass
    (d Y : ℕ) (S : Finset ℕ) (A B : ℕ) : ℤ :=
  ∑ t ∈ predecessorFirstJumpFrozenWindowFaces d Y S A B,
    booleanCubeSign t

/-- **Signed dense/jump decomposition.**  No triangle inequality is used: the
original frozen predecessor mass is exactly the sum of the two signed pieces. -/
theorem frozenPrimeUniverseWindowMass_eq_dense_add_firstJump
    (d Y : ℕ) (S : Finset ℕ) (A B : ℕ) :
    frozenPrimeUniverseWindowMass S A B =
      predecessorDenseFrozenWindowMass d Y S A B +
        predecessorFirstJumpFrozenWindowMass d Y S A B := by
  unfold frozenPrimeUniverseWindowMass
    predecessorDenseFrozenWindowMass
    predecessorFirstJumpFrozenWindowMass
  rw [← predecessorDense_union_firstJump_frozenWindow d Y S A B]
  rw [Finset.sum_union
    (predecessorDense_disjoint_firstJump_frozenWindow d Y S A B)]

/-- Every first-jump face has a canonical least failing coordinate. -/
theorem firstJumpFrozenWindowFace_exists_firstFailure
    {d Y : ℕ} {S : Finset ℕ} {A B : ℕ} {t : Finset ℕ}
    (ht : t ∈ predecessorFirstJumpFrozenWindowFaces d Y S A B) :
    ∃ p ∈ t,
      Y * predecessorPrimeFaceProduct t p < p ^ d ∧
      ∀ q ∈ t, q < p →
        q ^ d ≤ Y * predecessorPrimeFaceProduct t q := by
  have hnot := (mem_predecessorFirstJumpFrozenWindowFaces.mp ht).2
  exact exists_first_predecessorDenseFailure hnot

/-- In a frozen predecessor cube through `pivot-1`, the first failing coordinate
is still strictly below `pivot`.  Thus even the exceptional branch descends in
owner order rather than escaping back to the current owner. -/
theorem firstJumpFrozenPredecessorWindow_exists_lowerOwner
    {d Y pivot A B : ℕ} {t : Finset ℕ}
    (ht : t ∈ predecessorFirstJumpFrozenWindowFaces d Y
      (primesUpTo (pivot - 1)) A B) :
    ∃ p ∈ t,
      p < pivot ∧
      Y * predecessorPrimeFaceProduct t p < p ^ d ∧
      ∀ q ∈ t, q < p →
        q ^ d ≤ Y * predecessorPrimeFaceProduct t q := by
  rcases firstJumpFrozenWindowFace_exists_firstFailure ht with
    ⟨p, hpt, hfail, hprev⟩
  have hwindow :=
    (mem_predecessorFirstJumpFrozenWindowFaces.mp ht).1
  have htPred := (mem_frozenPrimeUniverseWindowFaces.mp hwindow).1
  have hpPrefix := (Finset.mem_powerset.mp htPred) hpt
  rcases mem_primesUpTo.mp hpPrefix with ⟨hpPrime, hpLe⟩
  have hpTwo : 2 ≤ p := hpPrime.two_le
  have hpLt : p < pivot := by omega
  exact ⟨p, hpt, hpLt, hfail, hprev⟩

/-- Specialization to an actual canonically oriented charging face.  Either the
whole old face is predecessor-dense, or its first multiplicative jump occurs at
a prime strictly below the fresh crossing pivot. -/
theorem orientedChargingFace_dense_or_firstLowerJump
    {R c k d Y : ℕ} {t : Finset ℕ}
    (ht : t ∈ lowWheelCanonicalDowncrossOrientedChargingFaces R (c, k)) :
    PredecessorDenseFace d Y t ∨
      ∃ p ∈ t,
        p < lowWheelCanonicalDowncrossPivot (c, k) ∧
        Y * predecessorPrimeFaceProduct t p < p ^ d ∧
        ∀ q ∈ t, q < p →
          q ^ d ≤ Y * predecessorPrimeFaceProduct t q := by
  rcases mem_lowWheelCanonicalDowncrossOrientedChargingFaces.mp ht with
    ⟨htPow, hx⟩
  rcases predecessorDenseFace_or_exists_firstFailure d Y t with hdense | hjump
  · exact Or.inl hdense
  · right
    rcases hjump with ⟨p, hpt, hfail, hprev⟩
    have hpLt :=
      lowWheelCanonicalDowncrossOriented_facePrime_lt_pivot htPow hx hpt
    exact ⟨p, hpt, hpLt, hfail, hprev⟩

end RHLean.Proof
