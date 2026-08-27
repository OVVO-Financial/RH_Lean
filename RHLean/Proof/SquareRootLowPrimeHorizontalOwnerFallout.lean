import Mathlib
import RHLean.Proof.SquareRootLowPrimeMatchingDisplacement

/-!
# Horizontal owner slices for the processed low-prime frontier

This module separates the two objects that occur at one chronological prime
stage.

* The complete paired population removed at `p` is a zero-mass object: every
  lower endpoint is matched with its `p`-extension and the two Mobius weights
  cancel.
* A fresh parent whose `p`-child is absent from the current row is surviving
  fallout.  Its mass is retained and must be estimated; it is never declared
  zero.

The removed populations are recorded by chronological owner and are pairwise
disjoint because every later row is a subset of the frontier left by every
earlier row.

For fallout, the genuine Euler orientation adds

`P+(cofactor) < p`.

A chosen target population is then assigned to the first chronological owner at
which it lies in this canonical fallout.  Once assigned, it is deleted only
from the still-unassigned target.  Therefore the first-fallout slices are
pairwise disjoint and their signed masses add exactly, with an explicit residual
for states having no such owner.

No estimate, chain parity, PNT input, or Mertens bound is used here.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-! ## Chronological removed-pair slices -/

/-- Owner-tagged populations actually removed by chronological matching. -/
def squareRootLowPrimeProcessedSeatRemovedPairSliceFamily :
    List ℕ → Finset SquareRootLowPrimeProcessedState →
      List (ℕ × Finset SquareRootLowPrimeProcessedState)
  | [], _S => []
  | p :: ps, S =>
      (p, squareRootLowPrimeProcessedSeatPaired S p) ::
        squareRootLowPrimeProcessedSeatRemovedPairSliceFamily ps
          (squareRootLowPrimeProcessedSeatFrontierStep S p)

/-- Every recorded removed population lies in the carrier entering the whole
chronological matching. -/
theorem squareRootLowPrimeProcessedSeatRemovedPairSliceFamily_entry_subset
    (ps : List ℕ) (S : Finset SquareRootLowPrimeProcessedState)
    {a : ℕ × Finset SquareRootLowPrimeProcessedState}
    (ha : a ∈ squareRootLowPrimeProcessedSeatRemovedPairSliceFamily ps S) :
    a.2 ⊆ S := by
  induction ps generalizing S a with
  | nil =>
      simp [squareRootLowPrimeProcessedSeatRemovedPairSliceFamily] at ha
  | cons p ps ih =>
      simp only [squareRootLowPrimeProcessedSeatRemovedPairSliceFamily,
        List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact squareRootLowPrimeProcessedSeatPaired_subset S p
      · exact
          (ih (S := squareRootLowPrimeProcessedSeatFrontierStep S p) ha).trans
            (squareRootLowPrimeProcessedSeatFrontierStep_subset' S p)

/-- The population removed at one owner is disjoint from the row that survives
that owner. -/
theorem squareRootLowPrimeProcessedSeatPaired_disjoint_frontierStep
    (S : Finset SquareRootLowPrimeProcessedState) (p : ℕ) :
    Disjoint (squareRootLowPrimeProcessedSeatPaired S p)
      (squareRootLowPrimeProcessedSeatFrontierStep S p) := by
  rw [Finset.disjoint_left]
  intro x hxPaired hxFrontier
  exact (Finset.mem_sdiff.mp hxFrontier).2 hxPaired

/-- Distinct chronological removed-pair slices have disjoint support. -/
theorem squareRootLowPrimeProcessedSeatRemovedPairSliceFamily_disjoint
    (ps : List ℕ) (S : Finset SquareRootLowPrimeProcessedState)
    {a b : ℕ × Finset SquareRootLowPrimeProcessedState}
    (ha : a ∈ squareRootLowPrimeProcessedSeatRemovedPairSliceFamily ps S)
    (hb : b ∈ squareRootLowPrimeProcessedSeatRemovedPairSliceFamily ps S)
    (hab : a ≠ b) :
    Disjoint a.2 b.2 := by
  induction ps generalizing S a b with
  | nil =>
      simp [squareRootLowPrimeProcessedSeatRemovedPairSliceFamily] at ha
  | cons p ps ih =>
      simp only [squareRootLowPrimeProcessedSeatRemovedPairSliceFamily,
        List.mem_cons] at ha hb
      rcases ha with rfl | ha
      · rcases hb with rfl | hb
        · exact (hab rfl).elim
        · rw [Finset.disjoint_left]
          intro x hxHead hxTail
          have hxFrontier :=
            squareRootLowPrimeProcessedSeatRemovedPairSliceFamily_entry_subset ps
              (squareRootLowPrimeProcessedSeatFrontierStep S p) hb hxTail
          exact (Finset.disjoint_left.mp
            (squareRootLowPrimeProcessedSeatPaired_disjoint_frontierStep S p))
            hxHead hxFrontier
      · rcases hb with rfl | hb
        · rw [Finset.disjoint_left]
          intro x hxTail hxHead
          have hxFrontier :=
            squareRootLowPrimeProcessedSeatRemovedPairSliceFamily_entry_subset ps
              (squareRootLowPrimeProcessedSeatFrontierStep S p) ha hxTail
          exact (Finset.disjoint_left.mp
            (squareRootLowPrimeProcessedSeatPaired_disjoint_frontierStep S p))
            hxHead hxFrontier
        · exact ih
            (S := squareRootLowPrimeProcessedSeatFrontierStep S p)
            ha hb hab

/-- Every removed-pair slice cancels by itself.  This theorem applies only to
the paired population, never to fallout. -/
theorem squareRootLowPrimeProcessedSeatRemovedPairSliceFamily_weight_sum_eq_zero
    (ps : List ℕ) (S : Finset SquareRootLowPrimeProcessedState)
    (hprime : ∀ p ∈ ps, p.Prime)
    {a : ℕ × Finset SquareRootLowPrimeProcessedState}
    (ha : a ∈ squareRootLowPrimeProcessedSeatRemovedPairSliceFamily ps S) :
    (∑ x ∈ a.2, squareRootLowPrimeProcessedSeatWeightReal x) = 0 := by
  induction ps generalizing S a with
  | nil =>
      simp [squareRootLowPrimeProcessedSeatRemovedPairSliceFamily] at ha
  | cons p ps ih =>
      simp only [squareRootLowPrimeProcessedSeatRemovedPairSliceFamily,
        List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact squareRootLowPrimeProcessedSeatPaired_weight_sum_eq_zero S
          (hprime p (by simp))
      · have htail : ∀ q ∈ ps, q.Prime := by
          intro q hq
          exact hprime q (by simp [hq])
        exact ih
          (S := squareRootLowPrimeProcessedSeatFrontierStep S p)
          htail ha

/-! ## Fixed-owner missing-child fallout -/

/-- States eligible to be lower endpoints at owner `p`, before asking whether
their `p`-child is present in the current row. -/
def squareRootLowPrimeProcessedSeatFreshParentCandidates
    (S : Finset SquareRootLowPrimeProcessedState) (p : ℕ) :
    Finset SquareRootLowPrimeProcessedState :=
  S.filter fun x =>
    x ≠ none ∧ ¬ p ∣ squareRootLowPrimeProcessedStateCofactor x

@[simp] theorem mem_squareRootLowPrimeProcessedSeatFreshParentCandidates
    {S : Finset SquareRootLowPrimeProcessedState} {p : ℕ}
    {x : SquareRootLowPrimeProcessedState} :
    x ∈ squareRootLowPrimeProcessedSeatFreshParentCandidates S p ↔
      x ∈ S ∧ x ≠ none ∧
        ¬ p ∣ squareRootLowPrimeProcessedStateCofactor x := by
  simp [squareRootLowPrimeProcessedSeatFreshParentCandidates]

/-- Fresh parents whose `p`-child is absent from the current row. -/
def squareRootLowPrimeProcessedSeatOwnerFalloff
    (S : Finset SquareRootLowPrimeProcessedState) (p : ℕ) :
    Finset SquareRootLowPrimeProcessedState :=
  (squareRootLowPrimeProcessedSeatFreshParentCandidates S p).filter fun x =>
    squareRootLowPrimeProcessedSeatExtend p x ∉ S

@[simp] theorem mem_squareRootLowPrimeProcessedSeatOwnerFalloff
    {S : Finset SquareRootLowPrimeProcessedState} {p : ℕ}
    {x : SquareRootLowPrimeProcessedState} :
    x ∈ squareRootLowPrimeProcessedSeatOwnerFalloff S p ↔
      x ∈ S ∧ x ≠ none ∧
        ¬ p ∣ squareRootLowPrimeProcessedStateCofactor x ∧
        squareRootLowPrimeProcessedSeatExtend p x ∉ S := by
  constructor
  · intro hx
    rcases Finset.mem_filter.mp hx with ⟨hxCandidate, hmissing⟩
    have hdata :=
      mem_squareRootLowPrimeProcessedSeatFreshParentCandidates.mp hxCandidate
    exact ⟨hdata.1, hdata.2.1, hdata.2.2, hmissing⟩
  · rintro ⟨hxS, hxHead, hpFresh, hmissing⟩
    exact Finset.mem_filter.mpr
      ⟨mem_squareRootLowPrimeProcessedSeatFreshParentCandidates.mpr
          ⟨hxS, hxHead, hpFresh⟩,
        hmissing⟩

/-- At one owner, every fresh parent is either matched or its child is missing. -/
theorem squareRootLowPrimeProcessedSeatFreshParentCandidates_eq_pairLower_union_falloff
    (S : Finset SquareRootLowPrimeProcessedState) (p : ℕ) :
    squareRootLowPrimeProcessedSeatFreshParentCandidates S p =
      squareRootLowPrimeProcessedSeatPairLower S p ∪
        squareRootLowPrimeProcessedSeatOwnerFalloff S p := by
  ext x
  by_cases hchild : squareRootLowPrimeProcessedSeatExtend p x ∈ S
  · simp [squareRootLowPrimeProcessedSeatFreshParentCandidates,
      squareRootLowPrimeProcessedSeatPairLower,
      squareRootLowPrimeProcessedSeatOwnerFalloff, hchild]
  · simp [squareRootLowPrimeProcessedSeatFreshParentCandidates,
      squareRootLowPrimeProcessedSeatPairLower,
      squareRootLowPrimeProcessedSeatOwnerFalloff, hchild]

/-- Matched lower endpoints and missing-child parents are disjoint. -/
theorem squareRootLowPrimeProcessedSeatPairLower_disjoint_ownerFalloff
    (S : Finset SquareRootLowPrimeProcessedState) (p : ℕ) :
    Disjoint (squareRootLowPrimeProcessedSeatPairLower S p)
      (squareRootLowPrimeProcessedSeatOwnerFalloff S p) := by
  rw [Finset.disjoint_left]
  intro x hxLower hxFalloff
  exact (mem_squareRootLowPrimeProcessedSeatOwnerFalloff.mp hxFalloff).2.2.2
    (mem_squareRootLowPrimeProcessedSeatPairLower.mp hxLower).2.2.2

/-- Fixed-owner cardinality identity for matched parents versus fallout. -/
theorem squareRootLowPrimeProcessedSeatFreshParentCandidates_card
    (S : Finset SquareRootLowPrimeProcessedState) (p : ℕ) :
    (squareRootLowPrimeProcessedSeatFreshParentCandidates S p).card =
      (squareRootLowPrimeProcessedSeatPairLower S p).card +
        (squareRootLowPrimeProcessedSeatOwnerFalloff S p).card := by
  rw [squareRootLowPrimeProcessedSeatFreshParentCandidates_eq_pairLower_union_falloff,
    Finset.card_union_of_disjoint
      (squareRootLowPrimeProcessedSeatPairLower_disjoint_ownerFalloff S p)]

/-- A fresh parent candidate cannot be a same-owner upper endpoint because every
upper endpoint has cofactor divisible by `p`. -/
theorem squareRootLowPrimeProcessedSeatFreshParentCandidate_not_mem_pairUpper
    {S : Finset SquareRootLowPrimeProcessedState} {p : ℕ}
    {x : SquareRootLowPrimeProcessedState}
    (hx : x ∈ squareRootLowPrimeProcessedSeatFreshParentCandidates S p) :
    x ∉ squareRootLowPrimeProcessedSeatPairUpper S p := by
  intro hxUpper
  rcases Finset.mem_image.mp hxUpper with ⟨y, hyLower, hyx⟩
  have hyData := mem_squareRootLowPrimeProcessedSeatPairLower.mp hyLower
  have hpDiv :
      p ∣ squareRootLowPrimeProcessedStateCofactor
        (squareRootLowPrimeProcessedSeatExtend p y) := by
    rcases y with _ | z
    · exact (hyData.2.1 rfl).elim
    · change p ∣ p * z.1
      exact ⟨z.1, rfl⟩
  have hpFresh :=
    (mem_squareRootLowPrimeProcessedSeatFreshParentCandidates.mp hx).2.2
  apply hpFresh
  rw [← hyx]
  exact hpDiv

/-- Missing-child parents survive their owner step. -/
theorem squareRootLowPrimeProcessedSeatOwnerFalloff_subset_frontierStep
    (S : Finset SquareRootLowPrimeProcessedState) (p : ℕ) :
    squareRootLowPrimeProcessedSeatOwnerFalloff S p ⊆
      squareRootLowPrimeProcessedSeatFrontierStep S p := by
  intro x hx
  have hxData := mem_squareRootLowPrimeProcessedSeatOwnerFalloff.mp hx
  apply Finset.mem_sdiff.mpr
  refine ⟨hxData.1, ?_⟩
  intro hxPaired
  rcases Finset.mem_union.mp hxPaired with hxLower | hxUpper
  · exact hxData.2.2.2
      (mem_squareRootLowPrimeProcessedSeatPairLower.mp hxLower).2.2.2
  · have hxCandidate :
        x ∈ squareRootLowPrimeProcessedSeatFreshParentCandidates S p :=
      mem_squareRootLowPrimeProcessedSeatFreshParentCandidates.mpr
        ⟨hxData.1, hxData.2.1, hxData.2.2.1⟩
    exact
      (squareRootLowPrimeProcessedSeatFreshParentCandidate_not_mem_pairUpper
        hxCandidate) hxUpper

/-- Among fresh parent candidates, the survivors of the `p` step are exactly
the missing-child fallout. -/
theorem squareRootLowPrimeProcessedSeatFreshParent_frontier_eq_ownerFalloff
    (S : Finset SquareRootLowPrimeProcessedState) (p : ℕ) :
    squareRootLowPrimeProcessedSeatFreshParentCandidates S p ∩
        squareRootLowPrimeProcessedSeatFrontierStep S p =
      squareRootLowPrimeProcessedSeatOwnerFalloff S p := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_inter.mp hx with ⟨hxCandidate, hxFrontier⟩
    have hxData :=
      mem_squareRootLowPrimeProcessedSeatFreshParentCandidates.mp hxCandidate
    apply mem_squareRootLowPrimeProcessedSeatOwnerFalloff.mpr
    refine ⟨hxData.1, hxData.2.1, hxData.2.2, ?_⟩
    intro hchild
    have hxLower : x ∈ squareRootLowPrimeProcessedSeatPairLower S p :=
      mem_squareRootLowPrimeProcessedSeatPairLower.mpr
        ⟨hxData.1, hxData.2.1, hxData.2.2, hchild⟩
    exact (Finset.mem_sdiff.mp hxFrontier).2
      (Finset.mem_union.mpr (Or.inl hxLower))
  · intro hxFalloff
    have hxData := mem_squareRootLowPrimeProcessedSeatOwnerFalloff.mp hxFalloff
    exact Finset.mem_inter.mpr
      ⟨mem_squareRootLowPrimeProcessedSeatFreshParentCandidates.mpr
          ⟨hxData.1, hxData.2.1, hxData.2.2.1⟩,
        squareRootLowPrimeProcessedSeatOwnerFalloff_subset_frontierStep
          S p hxFalloff⟩

/-- Genuine Euler-oriented fallout: the parent is rough below the fresh owner. -/
def squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff
    (S : Finset SquareRootLowPrimeProcessedState) (p : ℕ) :
    Finset SquareRootLowPrimeProcessedState :=
  (squareRootLowPrimeProcessedSeatOwnerFalloff S p).filter fun x =>
    canonicalLargestPrimeFactor
      (squareRootLowPrimeProcessedStateCofactor x) < p

@[simp] theorem mem_squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff
    {S : Finset SquareRootLowPrimeProcessedState} {p : ℕ}
    {x : SquareRootLowPrimeProcessedState} :
    x ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff S p ↔
      x ∈ S ∧ x ≠ none ∧
        ¬ p ∣ squareRootLowPrimeProcessedStateCofactor x ∧
        squareRootLowPrimeProcessedSeatExtend p x ∉ S ∧
        canonicalLargestPrimeFactor
          (squareRootLowPrimeProcessedStateCofactor x) < p := by
  constructor
  · intro hx
    rcases Finset.mem_filter.mp hx with ⟨hxFalloff, hlpf⟩
    have hdata := mem_squareRootLowPrimeProcessedSeatOwnerFalloff.mp hxFalloff
    exact ⟨hdata.1, hdata.2.1, hdata.2.2.1, hdata.2.2.2, hlpf⟩
  · rintro ⟨hxS, hxHead, hpFresh, hmissing, hlpf⟩
    exact Finset.mem_filter.mpr
      ⟨mem_squareRootLowPrimeProcessedSeatOwnerFalloff.mpr
          ⟨hxS, hxHead, hpFresh, hmissing⟩,
        hlpf⟩

/-! ## Disjoint first-fallout owner slices -/

/-- The current owner slice inside a still-unassigned target population. -/
def squareRootLowPrimeProcessedSeatFirstFalloffSlice
    (T S : Finset SquareRootLowPrimeProcessedState) (p : ℕ) :
    Finset SquareRootLowPrimeProcessedState :=
  T ∩ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff S p

/-- Chronological first-fallout slices.  Assigned states are removed from the
unassigned target before later owners are visited. -/
def squareRootLowPrimeProcessedSeatFirstFalloffFamily :
    List ℕ → Finset SquareRootLowPrimeProcessedState →
      Finset SquareRootLowPrimeProcessedState →
      List (ℕ × Finset SquareRootLowPrimeProcessedState)
  | [], _S, _T => []
  | p :: ps, S, T =>
      (p, squareRootLowPrimeProcessedSeatFirstFalloffSlice T S p) ::
        squareRootLowPrimeProcessedSeatFirstFalloffFamily ps
          (squareRootLowPrimeProcessedSeatFrontierStep S p)
          (T \ squareRootLowPrimeProcessedSeatFirstFalloffSlice T S p)

/-- Union of all assigned first-fallout slices. -/
def squareRootLowPrimeProcessedSeatFirstFalloffSupport :
    List ℕ → Finset SquareRootLowPrimeProcessedState →
      Finset SquareRootLowPrimeProcessedState →
      Finset SquareRootLowPrimeProcessedState
  | [], _S, _T => ∅
  | p :: ps, S, T =>
      squareRootLowPrimeProcessedSeatFirstFalloffSlice T S p ∪
        squareRootLowPrimeProcessedSeatFirstFalloffSupport ps
          (squareRootLowPrimeProcessedSeatFrontierStep S p)
          (T \ squareRootLowPrimeProcessedSeatFirstFalloffSlice T S p)

/-- Target states still unassigned after all owner coordinates. -/
def squareRootLowPrimeProcessedSeatFirstFalloffResidual :
    List ℕ → Finset SquareRootLowPrimeProcessedState →
      Finset SquareRootLowPrimeProcessedState →
      Finset SquareRootLowPrimeProcessedState
  | [], _S, T => T
  | p :: ps, S, T =>
      squareRootLowPrimeProcessedSeatFirstFalloffResidual ps
        (squareRootLowPrimeProcessedSeatFrontierStep S p)
        (T \ squareRootLowPrimeProcessedSeatFirstFalloffSlice T S p)

/-- Every recorded first-fallout slice lies in the original target. -/
theorem squareRootLowPrimeProcessedSeatFirstFalloffFamily_entry_subset_target
    (ps : List ℕ) (S T : Finset SquareRootLowPrimeProcessedState)
    {a : ℕ × Finset SquareRootLowPrimeProcessedState}
    (ha : a ∈ squareRootLowPrimeProcessedSeatFirstFalloffFamily ps S T) :
    a.2 ⊆ T := by
  induction ps generalizing S T a with
  | nil =>
      simp [squareRootLowPrimeProcessedSeatFirstFalloffFamily] at ha
  | cons p ps ih =>
      simp only [squareRootLowPrimeProcessedSeatFirstFalloffFamily,
        List.mem_cons] at ha
      rcases ha with rfl | ha
      · intro x hx
        exact (Finset.mem_inter.mp hx).1
      · intro x hx
        have hxTail :=
          ih
            (S := squareRootLowPrimeProcessedSeatFrontierStep S p)
            (T := T \ squareRootLowPrimeProcessedSeatFirstFalloffSlice T S p)
            ha hx
        exact (Finset.mem_sdiff.mp hxTail).1

/-- Distinct first-fallout owner slices are disjoint. -/
theorem squareRootLowPrimeProcessedSeatFirstFalloffFamily_disjoint
    (ps : List ℕ) (S T : Finset SquareRootLowPrimeProcessedState)
    {a b : ℕ × Finset SquareRootLowPrimeProcessedState}
    (ha : a ∈ squareRootLowPrimeProcessedSeatFirstFalloffFamily ps S T)
    (hb : b ∈ squareRootLowPrimeProcessedSeatFirstFalloffFamily ps S T)
    (hab : a ≠ b) :
    Disjoint a.2 b.2 := by
  induction ps generalizing S T a b with
  | nil =>
      simp [squareRootLowPrimeProcessedSeatFirstFalloffFamily] at ha
  | cons p ps ih =>
      simp only [squareRootLowPrimeProcessedSeatFirstFalloffFamily,
        List.mem_cons] at ha hb
      rcases ha with rfl | ha
      · rcases hb with rfl | hb
        · exact (hab rfl).elim
        · rw [Finset.disjoint_left]
          intro x hxHead hxTail
          have hxTailTarget :=
            squareRootLowPrimeProcessedSeatFirstFalloffFamily_entry_subset_target
              ps
              (squareRootLowPrimeProcessedSeatFrontierStep S p)
              (T \ squareRootLowPrimeProcessedSeatFirstFalloffSlice T S p)
              hb hxTail
          exact (Finset.mem_sdiff.mp hxTailTarget).2 hxHead
      · rcases hb with rfl | hb
        · rw [Finset.disjoint_left]
          intro x hxTail hxHead
          have hxTailTarget :=
            squareRootLowPrimeProcessedSeatFirstFalloffFamily_entry_subset_target
              ps
              (squareRootLowPrimeProcessedSeatFrontierStep S p)
              (T \ squareRootLowPrimeProcessedSeatFirstFalloffSlice T S p)
              ha hxTail
          exact (Finset.mem_sdiff.mp hxTailTarget).2 hxHead
        · exact ih
            (S := squareRootLowPrimeProcessedSeatFrontierStep S p)
            (T := T \ squareRootLowPrimeProcessedSeatFirstFalloffSlice T S p)
            ha hb hab

/-- The assigned support stays inside the chosen target. -/
theorem squareRootLowPrimeProcessedSeatFirstFalloffSupport_subset_target
    (ps : List ℕ) (S T : Finset SquareRootLowPrimeProcessedState) :
    squareRootLowPrimeProcessedSeatFirstFalloffSupport ps S T ⊆ T := by
  induction ps generalizing S T with
  | nil =>
      simp [squareRootLowPrimeProcessedSeatFirstFalloffSupport]
  | cons p ps ih =>
      intro x hx
      change x ∈ squareRootLowPrimeProcessedSeatFirstFalloffSlice T S p ∪
        squareRootLowPrimeProcessedSeatFirstFalloffSupport ps
          (squareRootLowPrimeProcessedSeatFrontierStep S p)
          (T \ squareRootLowPrimeProcessedSeatFirstFalloffSlice T S p) at hx
      rcases Finset.mem_union.mp hx with hxHead | hxTail
      · exact (Finset.mem_inter.mp hxHead).1
      · have hxTailTarget :=
          ih
            (S := squareRootLowPrimeProcessedSeatFrontierStep S p)
            (T := T \ squareRootLowPrimeProcessedSeatFirstFalloffSlice T S p)
            hxTail
        exact (Finset.mem_sdiff.mp hxTailTarget).1

/-- The unassigned residual stays inside the chosen target. -/
theorem squareRootLowPrimeProcessedSeatFirstFalloffResidual_subset_target
    (ps : List ℕ) (S T : Finset SquareRootLowPrimeProcessedState) :
    squareRootLowPrimeProcessedSeatFirstFalloffResidual ps S T ⊆ T := by
  induction ps generalizing S T with
  | nil =>
      intro x hx
      simpa [squareRootLowPrimeProcessedSeatFirstFalloffResidual] using hx
  | cons p ps ih =>
      intro x hx
      have hxTail :=
        ih
          (S := squareRootLowPrimeProcessedSeatFrontierStep S p)
          (T := T \ squareRootLowPrimeProcessedSeatFirstFalloffSlice T S p)
          hx
      exact (Finset.mem_sdiff.mp hxTail).1

/-- Assigned support and residual are disjoint. -/
theorem squareRootLowPrimeProcessedSeatFirstFalloffSupport_disjoint_residual
    (ps : List ℕ) (S T : Finset SquareRootLowPrimeProcessedState) :
    Disjoint
      (squareRootLowPrimeProcessedSeatFirstFalloffSupport ps S T)
      (squareRootLowPrimeProcessedSeatFirstFalloffResidual ps S T) := by
  induction ps generalizing S T with
  | nil =>
      simp [squareRootLowPrimeProcessedSeatFirstFalloffSupport]
  | cons p ps ih =>
      rw [Finset.disjoint_left]
      intro x hxSupport hxResidual
      change x ∈ squareRootLowPrimeProcessedSeatFirstFalloffSlice T S p ∪
        squareRootLowPrimeProcessedSeatFirstFalloffSupport ps
          (squareRootLowPrimeProcessedSeatFrontierStep S p)
          (T \ squareRootLowPrimeProcessedSeatFirstFalloffSlice T S p) at hxSupport
      rcases Finset.mem_union.mp hxSupport with hxHead | hxTail
      · have hxResidualTarget :=
          squareRootLowPrimeProcessedSeatFirstFalloffResidual_subset_target
            ps
            (squareRootLowPrimeProcessedSeatFrontierStep S p)
            (T \ squareRootLowPrimeProcessedSeatFirstFalloffSlice T S p)
            hxResidual
        exact (Finset.mem_sdiff.mp hxResidualTarget).2 hxHead
      · exact (Finset.disjoint_left.mp
          (ih
            (S := squareRootLowPrimeProcessedSeatFrontierStep S p)
            (T := T \ squareRootLowPrimeProcessedSeatFirstFalloffSlice T S p)))
          hxTail hxResidual

/-- Assigned first-fallout support and residual partition the target exactly. -/
theorem squareRootLowPrimeProcessedSeatFirstFalloffSupport_union_residual
    (ps : List ℕ) (S T : Finset SquareRootLowPrimeProcessedState) :
    squareRootLowPrimeProcessedSeatFirstFalloffSupport ps S T ∪
        squareRootLowPrimeProcessedSeatFirstFalloffResidual ps S T = T := by
  induction ps generalizing S T with
  | nil =>
      simp [squareRootLowPrimeProcessedSeatFirstFalloffSupport,
        squareRootLowPrimeProcessedSeatFirstFalloffResidual]
  | cons p ps ih =>
      simp only [squareRootLowPrimeProcessedSeatFirstFalloffSupport,
        squareRootLowPrimeProcessedSeatFirstFalloffResidual]
      rw [Finset.union_assoc,
        ih
          (S := squareRootLowPrimeProcessedSeatFrontierStep S p)
          (T := T \ squareRootLowPrimeProcessedSeatFirstFalloffSlice T S p)]
      ext x
      simp [squareRootLowPrimeProcessedSeatFirstFalloffSlice]
      omega

/-- Recursive signed mass of the disjoint first-fallout owner slices.  Unlike
removed-pair mass, this quantity is not asserted to vanish. -/
def squareRootLowPrimeProcessedSeatFirstFalloffMass :
    List ℕ → Finset SquareRootLowPrimeProcessedState →
      Finset SquareRootLowPrimeProcessedState → ℝ
  | [], _S, _T => 0
  | p :: ps, S, T =>
      (∑ x ∈ squareRootLowPrimeProcessedSeatFirstFalloffSlice T S p,
        squareRootLowPrimeProcessedSeatWeightReal x) +
      squareRootLowPrimeProcessedSeatFirstFalloffMass ps
        (squareRootLowPrimeProcessedSeatFrontierStep S p)
        (T \ squareRootLowPrimeProcessedSeatFirstFalloffSlice T S p)

/-- The assigned support mass is exactly the chronological sum of owner-slice
masses. -/
theorem squareRootLowPrimeProcessedSeatFirstFalloffSupport_weight_sum_eq_mass
    (ps : List ℕ) (S T : Finset SquareRootLowPrimeProcessedState) :
    (∑ x ∈ squareRootLowPrimeProcessedSeatFirstFalloffSupport ps S T,
      squareRootLowPrimeProcessedSeatWeightReal x) =
      squareRootLowPrimeProcessedSeatFirstFalloffMass ps S T := by
  induction ps generalizing S T with
  | nil =>
      simp [squareRootLowPrimeProcessedSeatFirstFalloffSupport,
        squareRootLowPrimeProcessedSeatFirstFalloffMass]
  | cons p ps ih =>
      have htailSub :
          squareRootLowPrimeProcessedSeatFirstFalloffSupport ps
              (squareRootLowPrimeProcessedSeatFrontierStep S p)
              (T \ squareRootLowPrimeProcessedSeatFirstFalloffSlice T S p) ⊆
            T \ squareRootLowPrimeProcessedSeatFirstFalloffSlice T S p :=
        squareRootLowPrimeProcessedSeatFirstFalloffSupport_subset_target
          ps
          (squareRootLowPrimeProcessedSeatFrontierStep S p)
          (T \ squareRootLowPrimeProcessedSeatFirstFalloffSlice T S p)
      have hdisj :
          Disjoint
            (squareRootLowPrimeProcessedSeatFirstFalloffSlice T S p)
            (squareRootLowPrimeProcessedSeatFirstFalloffSupport ps
              (squareRootLowPrimeProcessedSeatFrontierStep S p)
              (T \ squareRootLowPrimeProcessedSeatFirstFalloffSlice T S p)) := by
        rw [Finset.disjoint_left]
        intro x hxHead hxTail
        exact (Finset.mem_sdiff.mp (htailSub hxTail)).2 hxHead
      simp only [squareRootLowPrimeProcessedSeatFirstFalloffSupport,
        squareRootLowPrimeProcessedSeatFirstFalloffMass]
      rw [Finset.sum_union hdisj,
        ih
          (S := squareRootLowPrimeProcessedSeatFrontierStep S p)
          (T := T \ squareRootLowPrimeProcessedSeatFirstFalloffSlice T S p)]

/-- **Horizontal mass decomposition.**  Target mass equals the sum of the
disjoint first-fallout owner masses plus the unassigned residual mass. -/
theorem squareRootLowPrimeProcessedSeatTarget_weight_sum_eq_firstFalloff_add_residual
    (ps : List ℕ) (S T : Finset SquareRootLowPrimeProcessedState) :
    (∑ x ∈ T, squareRootLowPrimeProcessedSeatWeightReal x) =
      squareRootLowPrimeProcessedSeatFirstFalloffMass ps S T +
        ∑ x ∈ squareRootLowPrimeProcessedSeatFirstFalloffResidual ps S T,
          squareRootLowPrimeProcessedSeatWeightReal x := by
  have hdisj :=
    squareRootLowPrimeProcessedSeatFirstFalloffSupport_disjoint_residual ps S T
  have hunion :=
    squareRootLowPrimeProcessedSeatFirstFalloffSupport_union_residual ps S T
  calc
    (∑ x ∈ T, squareRootLowPrimeProcessedSeatWeightReal x) =
        ∑ x ∈
          (squareRootLowPrimeProcessedSeatFirstFalloffSupport ps S T ∪
            squareRootLowPrimeProcessedSeatFirstFalloffResidual ps S T),
          squareRootLowPrimeProcessedSeatWeightReal x := by
            rw [hunion]
    _ =
        (∑ x ∈ squareRootLowPrimeProcessedSeatFirstFalloffSupport ps S T,
          squareRootLowPrimeProcessedSeatWeightReal x) +
        ∑ x ∈ squareRootLowPrimeProcessedSeatFirstFalloffResidual ps S T,
          squareRootLowPrimeProcessedSeatWeightReal x :=
      Finset.sum_union hdisj
    _ = squareRootLowPrimeProcessedSeatFirstFalloffMass ps S T +
        ∑ x ∈ squareRootLowPrimeProcessedSeatFirstFalloffResidual ps S T,
          squareRootLowPrimeProcessedSeatWeightReal x := by
      rw [squareRootLowPrimeProcessedSeatFirstFalloffSupport_weight_sum_eq_mass]

/-- Coverage of the target by first-fallout owners empties the residual. -/
theorem squareRootLowPrimeProcessedSeatFirstFalloffResidual_eq_empty_of_covered
    (ps : List ℕ) (S T : Finset SquareRootLowPrimeProcessedState)
    (hcover : ∀ x ∈ T,
      x ∈ squareRootLowPrimeProcessedSeatFirstFalloffSupport ps S T) :
    squareRootLowPrimeProcessedSeatFirstFalloffResidual ps S T = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hxResidual
  have hxT :=
    squareRootLowPrimeProcessedSeatFirstFalloffResidual_subset_target
      ps S T hxResidual
  have hxSupport := hcover x hxT
  exact (Finset.disjoint_left.mp
    (squareRootLowPrimeProcessedSeatFirstFalloffSupport_disjoint_residual
      ps S T)) hxSupport hxResidual

/-- Under exact coverage, target mass is literally the sum of the disjoint
first-fallout owner-slice masses. -/
theorem squareRootLowPrimeProcessedSeatTarget_weight_sum_eq_firstFalloffMass_of_covered
    (ps : List ℕ) (S T : Finset SquareRootLowPrimeProcessedState)
    (hcover : ∀ x ∈ T,
      x ∈ squareRootLowPrimeProcessedSeatFirstFalloffSupport ps S T) :
    (∑ x ∈ T, squareRootLowPrimeProcessedSeatWeightReal x) =
      squareRootLowPrimeProcessedSeatFirstFalloffMass ps S T := by
  rw [squareRootLowPrimeProcessedSeatTarget_weight_sum_eq_firstFalloff_add_residual]
  rw [squareRootLowPrimeProcessedSeatFirstFalloffResidual_eq_empty_of_covered
    ps S T hcover]
  simp

end RHLean.Proof