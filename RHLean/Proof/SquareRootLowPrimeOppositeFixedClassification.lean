import Mathlib
import RHLean.Proof.FiniteOthelloMatching
import RHLean.Proof.SquareRootLowPrimeDescendingPivotStability
import RHLean.Proof.SquareRootLowPrimeNoLibertyBoundaryHome

/-!
# Opposite processed-seat Othello matching

The true processed-seat carrier is `Option (ℕ × ℕ)`: `none` is the distinguished
head and `some (c,s)` is the `s`-th response seat over cofactor `c`.

For one prime coordinate `p`, the existing processed matcher already provides a
literal disjoint lower/upper pair population

`some (c,s) <-> some (p*c,s)`.

This file completes each such partial matching by fixed points, then remembers
the first stage at which a state is removed.  The result is one genuine Othello
involution for any ordered list of prime coordinates.  Instantiating the order
with the descending fresh-prime list gives the candidate opposite/no-liberty
matching on the same carrier as the quantitative processed-seat identity.

The arithmetic endpoint theorem is deliberately kept separate: after this
finite legality layer is kernel-checked, its stable frontier still has to be
identified pointwise and weight-preservingly with the four tagged post-rematch
endpoint populations in `SquareRootLowPrimeNoLibertyBoundaryHome`.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Literal state type of the complete processed-seat carrier. -/
abbrev SquareRootLowPrimeProcessedState := Option (ℕ × ℕ)

/-- The unique lower endpoint represented by an admitted upper endpoint. -/
noncomputable def squareRootLowPrimeProcessedSeatOthelloPairPreimage
    (S : Finset SquareRootLowPrimeProcessedState) (p : ℕ)
    (x : SquareRootLowPrimeProcessedState)
    (hx : x ∈ squareRootLowPrimeProcessedSeatPairUpper S p) :
    SquareRootLowPrimeProcessedState :=
  Classical.choose (Finset.mem_image.mp hx)

private theorem squareRootLowPrimeProcessedSeatOthelloPairPreimage_spec
    {S : Finset SquareRootLowPrimeProcessedState} {p : ℕ}
    {x : SquareRootLowPrimeProcessedState}
    (hx : x ∈ squareRootLowPrimeProcessedSeatPairUpper S p) :
    squareRootLowPrimeProcessedSeatOthelloPairPreimage S p x hx ∈
        squareRootLowPrimeProcessedSeatPairLower S p ∧
      squareRootLowPrimeProcessedSeatExtend p
        (squareRootLowPrimeProcessedSeatOthelloPairPreimage S p x hx) = x := by
  exact Classical.choose_spec (Finset.mem_image.mp hx)

/-- One processed-seat prime matching, completed by fixed points. -/
noncomputable def squareRootLowPrimeProcessedSeatStepOthelloMate
    (S : Finset SquareRootLowPrimeProcessedState) (p : ℕ) :
    SquareRootLowPrimeProcessedState → SquareRootLowPrimeProcessedState :=
  fun x =>
    if x ∈ squareRootLowPrimeProcessedSeatPairLower S p then
      squareRootLowPrimeProcessedSeatExtend p x
    else if hxUpper : x ∈ squareRootLowPrimeProcessedSeatPairUpper S p then
      squareRootLowPrimeProcessedSeatOthelloPairPreimage S p x hxUpper
    else x

private theorem squareRootLowPrimeProcessedSeatStepOthelloMate_of_lower
    {S : Finset SquareRootLowPrimeProcessedState} {p : ℕ}
    {x : SquareRootLowPrimeProcessedState}
    (hx : x ∈ squareRootLowPrimeProcessedSeatPairLower S p) :
    squareRootLowPrimeProcessedSeatStepOthelloMate S p x =
      squareRootLowPrimeProcessedSeatExtend p x := by
  simp [squareRootLowPrimeProcessedSeatStepOthelloMate, hx]

private theorem squareRootLowPrimeProcessedSeatStepOthelloMate_of_upper
    {S : Finset SquareRootLowPrimeProcessedState} {p : ℕ}
    {x : SquareRootLowPrimeProcessedState}
    (hxLower : x ∉ squareRootLowPrimeProcessedSeatPairLower S p)
    (hxUpper : x ∈ squareRootLowPrimeProcessedSeatPairUpper S p) :
    squareRootLowPrimeProcessedSeatStepOthelloMate S p x =
      squareRootLowPrimeProcessedSeatOthelloPairPreimage S p x hxUpper := by
  simp [squareRootLowPrimeProcessedSeatStepOthelloMate, hxLower, hxUpper]

private theorem squareRootLowPrimeProcessedSeatStepOthelloMate_of_unpaired
    {S : Finset SquareRootLowPrimeProcessedState} {p : ℕ}
    {x : SquareRootLowPrimeProcessedState}
    (hxLower : x ∉ squareRootLowPrimeProcessedSeatPairLower S p)
    (hxUpper : x ∉ squareRootLowPrimeProcessedSeatPairUpper S p) :
    squareRootLowPrimeProcessedSeatStepOthelloMate S p x = x := by
  simp [squareRootLowPrimeProcessedSeatStepOthelloMate, hxLower, hxUpper]

/-- One processed-seat Othello step preserves its current finite row. -/
theorem squareRootLowPrimeProcessedSeatStepOthelloMate_mem
    (S : Finset SquareRootLowPrimeProcessedState) (p : ℕ)
    {x : SquareRootLowPrimeProcessedState} (hxS : x ∈ S) :
    squareRootLowPrimeProcessedSeatStepOthelloMate S p x ∈ S := by
  classical
  by_cases hxLower : x ∈ squareRootLowPrimeProcessedSeatPairLower S p
  · rw [squareRootLowPrimeProcessedSeatStepOthelloMate_of_lower hxLower]
    exact (mem_squareRootLowPrimeProcessedSeatPairLower.mp hxLower).2.2.2
  · by_cases hxUpper : x ∈ squareRootLowPrimeProcessedSeatPairUpper S p
    · rw [squareRootLowPrimeProcessedSeatStepOthelloMate_of_upper hxLower hxUpper]
      exact squareRootLowPrimeProcessedSeatPairLower_subset S p
        (squareRootLowPrimeProcessedSeatOthelloPairPreimage_spec hxUpper).1
    · rw [squareRootLowPrimeProcessedSeatStepOthelloMate_of_unpaired hxLower hxUpper]
      exact hxS

/-- One processed-seat Othello step is involutive. -/
theorem squareRootLowPrimeProcessedSeatStepOthelloMate_involutive
    (S : Finset SquareRootLowPrimeProcessedState) {p : ℕ} (hp : 0 < p)
    (x : SquareRootLowPrimeProcessedState) :
    squareRootLowPrimeProcessedSeatStepOthelloMate S p
        (squareRootLowPrimeProcessedSeatStepOthelloMate S p x) = x := by
  classical
  by_cases hxLower : x ∈ squareRootLowPrimeProcessedSeatPairLower S p
  · let y := squareRootLowPrimeProcessedSeatExtend p x
    have hyUpper : y ∈ squareRootLowPrimeProcessedSeatPairUpper S p := by
      unfold y squareRootLowPrimeProcessedSeatPairUpper
      exact Finset.mem_image.mpr ⟨x, hxLower, rfl⟩
    have hyNotLower : y ∉ squareRootLowPrimeProcessedSeatPairLower S p := by
      intro hyLower
      exact (Finset.disjoint_left.mp
        (squareRootLowPrimeProcessedSeatPairLower_disjoint_upper S p))
        hyLower hyUpper
    have hspec := squareRootLowPrimeProcessedSeatOthelloPairPreimage_spec hyUpper
    have hback :
        squareRootLowPrimeProcessedSeatOthelloPairPreimage S p y hyUpper = x := by
      apply squareRootLowPrimeProcessedSeatExtend_injOn hp hspec.1 hxLower
      simpa [y] using hspec.2
    rw [squareRootLowPrimeProcessedSeatStepOthelloMate_of_lower hxLower]
    change squareRootLowPrimeProcessedSeatStepOthelloMate S p y = x
    rw [squareRootLowPrimeProcessedSeatStepOthelloMate_of_upper hyNotLower hyUpper]
    exact hback
  · by_cases hxUpper : x ∈ squareRootLowPrimeProcessedSeatPairUpper S p
    · let y := squareRootLowPrimeProcessedSeatOthelloPairPreimage S p x hxUpper
      have hspec := squareRootLowPrimeProcessedSeatOthelloPairPreimage_spec hxUpper
      have hyLower : y ∈ squareRootLowPrimeProcessedSeatPairLower S p := by
        simpa [y] using hspec.1
      have hyExt : squareRootLowPrimeProcessedSeatExtend p y = x := by
        simpa [y] using hspec.2
      rw [squareRootLowPrimeProcessedSeatStepOthelloMate_of_upper hxLower hxUpper]
      change squareRootLowPrimeProcessedSeatStepOthelloMate S p y = x
      rw [squareRootLowPrimeProcessedSeatStepOthelloMate_of_lower hyLower]
      exact hyExt
    · rw [squareRootLowPrimeProcessedSeatStepOthelloMate_of_unpaired hxLower hxUpper]
      exact squareRootLowPrimeProcessedSeatStepOthelloMate_of_unpaired hxLower hxUpper

/-- One-step fixed points are exactly the states outside the paired population. -/
theorem squareRootLowPrimeProcessedSeatStepOthelloMate_eq_self_iff
    (S : Finset SquareRootLowPrimeProcessedState) (p : ℕ)
    {x : SquareRootLowPrimeProcessedState} :
    squareRootLowPrimeProcessedSeatStepOthelloMate S p x = x ↔
      x ∉ squareRootLowPrimeProcessedSeatPaired S p := by
  classical
  constructor
  · intro hfix hxPaired
    rcases Finset.mem_union.mp hxPaired with hxLower | hxUpper
    · have hExt : squareRootLowPrimeProcessedSeatExtend p x = x := by
        simpa [squareRootLowPrimeProcessedSeatStepOthelloMate, hxLower] using hfix
      have hxUpper' : x ∈ squareRootLowPrimeProcessedSeatPairUpper S p := by
        unfold squareRootLowPrimeProcessedSeatPairUpper
        exact Finset.mem_image.mpr ⟨x, hxLower, hExt⟩
      exact (Finset.disjoint_left.mp
        (squareRootLowPrimeProcessedSeatPairLower_disjoint_upper S p))
        hxLower hxUpper'
    · have hxNotLower : x ∉ squareRootLowPrimeProcessedSeatPairLower S p := by
        intro hxLower
        exact (Finset.disjoint_left.mp
          (squareRootLowPrimeProcessedSeatPairLower_disjoint_upper S p))
          hxLower hxUpper
      have hspec := squareRootLowPrimeProcessedSeatOthelloPairPreimage_spec hxUpper
      have hpreEq :
          squareRootLowPrimeProcessedSeatOthelloPairPreimage S p x hxUpper = x := by
        simpa [squareRootLowPrimeProcessedSeatStepOthelloMate,
          hxNotLower, hxUpper] using hfix
      have hxLower' : x ∈ squareRootLowPrimeProcessedSeatPairLower S p := by
        simpa [hpreEq] using hspec.1
      exact (Finset.disjoint_left.mp
        (squareRootLowPrimeProcessedSeatPairLower_disjoint_upper S p))
        hxLower' hxUpper
  · intro hxNotPaired
    have hxNotLower : x ∉ squareRootLowPrimeProcessedSeatPairLower S p := by
      intro hxLower
      exact hxNotPaired (Finset.mem_union.mpr (Or.inl hxLower))
    have hxNotUpper : x ∉ squareRootLowPrimeProcessedSeatPairUpper S p := by
      intro hxUpper
      exact hxNotPaired (Finset.mem_union.mpr (Or.inr hxUpper))
    simp [squareRootLowPrimeProcessedSeatStepOthelloMate,
      hxNotLower, hxNotUpper]

/-- Every moved one-step state has the opposite native processed-seat weight. -/
theorem squareRootLowPrimeProcessedSeatStepOthelloMate_weight_neg
    (S : Finset SquareRootLowPrimeProcessedState) {p : ℕ} (hp : p.Prime)
    (x : SquareRootLowPrimeProcessedState)
    (hne : squareRootLowPrimeProcessedSeatStepOthelloMate S p x ≠ x) :
    squareRootLowPrimeProcessedSeatWeightReal
        (squareRootLowPrimeProcessedSeatStepOthelloMate S p x) =
      -squareRootLowPrimeProcessedSeatWeightReal x := by
  classical
  by_cases hxLower : x ∈ squareRootLowPrimeProcessedSeatPairLower S p
  · rw [squareRootLowPrimeProcessedSeatStepOthelloMate_of_lower hxLower]
    exact squareRootLowPrimeProcessedSeatExtend_weight_eq_neg hp hxLower
  · by_cases hxUpper : x ∈ squareRootLowPrimeProcessedSeatPairUpper S p
    · rw [squareRootLowPrimeProcessedSeatStepOthelloMate_of_upper hxLower hxUpper]
      have hspec := squareRootLowPrimeProcessedSeatOthelloPairPreimage_spec hxUpper
      have hforward := squareRootLowPrimeProcessedSeatExtend_weight_eq_neg hp hspec.1
      rw [hspec.2] at hforward
      linarith
    · exfalso
      apply hne
      simp [squareRootLowPrimeProcessedSeatStepOthelloMate, hxLower, hxUpper]

/-- A one-step mate preserves the paired population setwise. -/
theorem squareRootLowPrimeProcessedSeatStepOthelloMate_mem_paired
    (S : Finset SquareRootLowPrimeProcessedState) (p : ℕ)
    {x : SquareRootLowPrimeProcessedState}
    (hx : x ∈ squareRootLowPrimeProcessedSeatPaired S p) :
    squareRootLowPrimeProcessedSeatStepOthelloMate S p x ∈
      squareRootLowPrimeProcessedSeatPaired S p := by
  classical
  rcases Finset.mem_union.mp hx with hxLower | hxUpper
  · rw [squareRootLowPrimeProcessedSeatStepOthelloMate_of_lower hxLower]
    apply Finset.mem_union.mpr
    right
    unfold squareRootLowPrimeProcessedSeatPairUpper
    exact Finset.mem_image.mpr ⟨x, hxLower, rfl⟩
  · have hxNotLower : x ∉ squareRootLowPrimeProcessedSeatPairLower S p := by
      intro hxLower
      exact (Finset.disjoint_left.mp
        (squareRootLowPrimeProcessedSeatPairLower_disjoint_upper S p))
        hxLower hxUpper
    rw [squareRootLowPrimeProcessedSeatStepOthelloMate_of_upper hxNotLower hxUpper]
    exact Finset.mem_union.mpr <| Or.inl <|
      (squareRootLowPrimeProcessedSeatOthelloPairPreimage_spec hxUpper).1

/-- A matching frontier is always a subset of the row from which it starts. -/
private theorem squareRootLowPrimeProcessedSeatMatchingFrontier_subset_local
    (ps : List ℕ) (S : Finset SquareRootLowPrimeProcessedState) :
    squareRootLowPrimeProcessedSeatMatchingFrontier ps S ⊆ S := by
  induction ps generalizing S with
  | nil =>
      simp [squareRootLowPrimeProcessedSeatMatchingFrontier]
  | cons p ps ih =>
      intro x hx
      have hxStep := ih
        (S := squareRootLowPrimeProcessedSeatFrontierStep S p) hx
      exact (Finset.mem_sdiff.mp hxStep).1

/-- A complete ordered processed-seat chronology as one Othello self-map.
At the first stage that removes a state, its local mate is remembered forever. -/
noncomputable def squareRootLowPrimeProcessedSeatChronologicalOthelloMate :
    List ℕ → Finset SquareRootLowPrimeProcessedState →
      SquareRootLowPrimeProcessedState → SquareRootLowPrimeProcessedState
  | [], _S => id
  | p :: ps, S => fun x =>
      if x ∈ squareRootLowPrimeProcessedSeatPaired S p then
        squareRootLowPrimeProcessedSeatStepOthelloMate S p x
      else
        squareRootLowPrimeProcessedSeatChronologicalOthelloMate ps
          (squareRootLowPrimeProcessedSeatFrontierStep S p) x

private theorem squareRootLowPrimeProcessedSeatChronologicalOthelloMate_cons_of_paired
    {p : ℕ} {ps : List ℕ} {S : Finset SquareRootLowPrimeProcessedState}
    {x : SquareRootLowPrimeProcessedState}
    (hx : x ∈ squareRootLowPrimeProcessedSeatPaired S p) :
    squareRootLowPrimeProcessedSeatChronologicalOthelloMate (p :: ps) S x =
      squareRootLowPrimeProcessedSeatStepOthelloMate S p x := by
  simp [squareRootLowPrimeProcessedSeatChronologicalOthelloMate, hx]

private theorem squareRootLowPrimeProcessedSeatChronologicalOthelloMate_cons_of_unpaired
    {p : ℕ} {ps : List ℕ} {S : Finset SquareRootLowPrimeProcessedState}
    {x : SquareRootLowPrimeProcessedState}
    (hx : x ∉ squareRootLowPrimeProcessedSeatPaired S p) :
    squareRootLowPrimeProcessedSeatChronologicalOthelloMate (p :: ps) S x =
      squareRootLowPrimeProcessedSeatChronologicalOthelloMate ps
        (squareRootLowPrimeProcessedSeatFrontierStep S p) x := by
  simp [squareRootLowPrimeProcessedSeatChronologicalOthelloMate, hx]

/-- The global chronology preserves its original finite carrier. -/
theorem squareRootLowPrimeProcessedSeatChronologicalOthelloMate_mem
    (ps : List ℕ) (S : Finset SquareRootLowPrimeProcessedState)
    {x : SquareRootLowPrimeProcessedState} (hxS : x ∈ S) :
    squareRootLowPrimeProcessedSeatChronologicalOthelloMate ps S x ∈ S := by
  induction ps generalizing S x with
  | nil =>
      simpa [squareRootLowPrimeProcessedSeatChronologicalOthelloMate] using hxS
  | cons p ps ih =>
      by_cases hxPaired : x ∈ squareRootLowPrimeProcessedSeatPaired S p
      · rw [squareRootLowPrimeProcessedSeatChronologicalOthelloMate_cons_of_paired
          hxPaired]
        exact squareRootLowPrimeProcessedSeatStepOthelloMate_mem S p hxS
      · have hxFrontier : x ∈ squareRootLowPrimeProcessedSeatFrontierStep S p :=
          Finset.mem_sdiff.mpr ⟨hxS, hxPaired⟩
        rw [squareRootLowPrimeProcessedSeatChronologicalOthelloMate_cons_of_unpaired
          hxPaired]
        have hrec := ih
          (S := squareRootLowPrimeProcessedSeatFrontierStep S p) hxFrontier
        exact (Finset.mem_sdiff.mp hrec).1

/-- The global chronology is an involution on its original finite carrier. -/
theorem squareRootLowPrimeProcessedSeatChronologicalOthelloMate_involutive
    (ps : List ℕ) (S : Finset SquareRootLowPrimeProcessedState)
    (hpos : ∀ p ∈ ps, 0 < p)
    {x : SquareRootLowPrimeProcessedState} (hxS : x ∈ S) :
    squareRootLowPrimeProcessedSeatChronologicalOthelloMate ps S
        (squareRootLowPrimeProcessedSeatChronologicalOthelloMate ps S x) = x := by
  induction ps generalizing S x with
  | nil => simp [squareRootLowPrimeProcessedSeatChronologicalOthelloMate]
  | cons p ps ih =>
      have hp : 0 < p := hpos p (by simp)
      have hrest : ∀ q ∈ ps, 0 < q := by
        intro q hq
        exact hpos q (by simp [hq])
      by_cases hxPaired : x ∈ squareRootLowPrimeProcessedSeatPaired S p
      · let y := squareRootLowPrimeProcessedSeatStepOthelloMate S p x
        have hyPaired : y ∈ squareRootLowPrimeProcessedSeatPaired S p := by
          exact squareRootLowPrimeProcessedSeatStepOthelloMate_mem_paired
            S p hxPaired
        rw [squareRootLowPrimeProcessedSeatChronologicalOthelloMate_cons_of_paired
          hxPaired]
        change squareRootLowPrimeProcessedSeatChronologicalOthelloMate
          (p :: ps) S y = x
        rw [squareRootLowPrimeProcessedSeatChronologicalOthelloMate_cons_of_paired
          hyPaired]
        exact squareRootLowPrimeProcessedSeatStepOthelloMate_involutive S hp x
      · have hxFrontier : x ∈ squareRootLowPrimeProcessedSeatFrontierStep S p :=
          Finset.mem_sdiff.mpr ⟨hxS, hxPaired⟩
        let y := squareRootLowPrimeProcessedSeatChronologicalOthelloMate ps
          (squareRootLowPrimeProcessedSeatFrontierStep S p) x
        have hyFrontier : y ∈ squareRootLowPrimeProcessedSeatFrontierStep S p := by
          exact squareRootLowPrimeProcessedSeatChronologicalOthelloMate_mem ps
            (squareRootLowPrimeProcessedSeatFrontierStep S p) hxFrontier
        have hyNotPaired : y ∉ squareRootLowPrimeProcessedSeatPaired S p :=
          (Finset.mem_sdiff.mp hyFrontier).2
        rw [squareRootLowPrimeProcessedSeatChronologicalOthelloMate_cons_of_unpaired
          hxPaired]
        change squareRootLowPrimeProcessedSeatChronologicalOthelloMate
          (p :: ps) S y = x
        rw [squareRootLowPrimeProcessedSeatChronologicalOthelloMate_cons_of_unpaired
          hyNotPaired]
        simpa [y] using ih
          (S := squareRootLowPrimeProcessedSeatFrontierStep S p)
          hrest hxFrontier

/-- Every moved state of the global chronology reverses native weight. -/
theorem squareRootLowPrimeProcessedSeatChronologicalOthelloMate_weight_neg
    (ps : List ℕ) (S : Finset SquareRootLowPrimeProcessedState)
    (hprime : ∀ p ∈ ps, p.Prime)
    {x : SquareRootLowPrimeProcessedState} (hxS : x ∈ S)
    (hne : squareRootLowPrimeProcessedSeatChronologicalOthelloMate ps S x ≠ x) :
    squareRootLowPrimeProcessedSeatWeightReal
        (squareRootLowPrimeProcessedSeatChronologicalOthelloMate ps S x) =
      -squareRootLowPrimeProcessedSeatWeightReal x := by
  induction ps generalizing S x with
  | nil =>
      simp [squareRootLowPrimeProcessedSeatChronologicalOthelloMate] at hne
  | cons p ps ih =>
      have hp : p.Prime := hprime p (by simp)
      have hrest : ∀ q ∈ ps, q.Prime := by
        intro q hq
        exact hprime q (by simp [hq])
      by_cases hxPaired : x ∈ squareRootLowPrimeProcessedSeatPaired S p
      · rw [squareRootLowPrimeProcessedSeatChronologicalOthelloMate_cons_of_paired
          hxPaired] at hne ⊢
        have hstepNe : squareRootLowPrimeProcessedSeatStepOthelloMate S p x ≠ x := by
          intro hfix
          exact ((squareRootLowPrimeProcessedSeatStepOthelloMate_eq_self_iff S p).mp
            hfix) hxPaired
        exact squareRootLowPrimeProcessedSeatStepOthelloMate_weight_neg
          S hp x hstepNe
      · have hxFrontier : x ∈ squareRootLowPrimeProcessedSeatFrontierStep S p :=
          Finset.mem_sdiff.mpr ⟨hxS, hxPaired⟩
        rw [squareRootLowPrimeProcessedSeatChronologicalOthelloMate_cons_of_unpaired
          hxPaired] at hne ⊢
        exact ih
          (S := squareRootLowPrimeProcessedSeatFrontierStep S p)
          hrest hxFrontier hne

/-- On a state in the starting row, global fixedness is exactly terminal
survival under that chronology. -/
private theorem squareRootLowPrimeProcessedSeatChronologicalOthelloMate_eq_self_iff
    (ps : List ℕ) (S : Finset SquareRootLowPrimeProcessedState)
    {x : SquareRootLowPrimeProcessedState} (hxS : x ∈ S) :
    squareRootLowPrimeProcessedSeatChronologicalOthelloMate ps S x = x ↔
      x ∈ squareRootLowPrimeProcessedSeatMatchingFrontier ps S := by
  induction ps generalizing S x with
  | nil =>
      simp [squareRootLowPrimeProcessedSeatChronologicalOthelloMate,
        squareRootLowPrimeProcessedSeatMatchingFrontier, hxS]
  | cons p ps ih =>
      by_cases hxPaired : x ∈ squareRootLowPrimeProcessedSeatPaired S p
      · have hstepNe : squareRootLowPrimeProcessedSeatStepOthelloMate S p x ≠ x := by
          intro hfix
          exact ((squareRootLowPrimeProcessedSeatStepOthelloMate_eq_self_iff S p).mp
            hfix) hxPaired
        constructor
        · intro hfix
          rw [squareRootLowPrimeProcessedSeatChronologicalOthelloMate_cons_of_paired
            hxPaired] at hfix
          exact (hstepNe hfix).elim
        · intro hxTerminal
          have hxStep : x ∈ squareRootLowPrimeProcessedSeatFrontierStep S p :=
            squareRootLowPrimeProcessedSeatMatchingFrontier_subset_local ps
              (squareRootLowPrimeProcessedSeatFrontierStep S p) hxTerminal
          exact ((Finset.mem_sdiff.mp hxStep).2 hxPaired).elim
      · have hxFrontier : x ∈ squareRootLowPrimeProcessedSeatFrontierStep S p :=
          Finset.mem_sdiff.mpr ⟨hxS, hxPaired⟩
        constructor
        · intro hfix
          rw [squareRootLowPrimeProcessedSeatChronologicalOthelloMate_cons_of_unpaired
            hxPaired] at hfix
          exact (ih
            (S := squareRootLowPrimeProcessedSeatFrontierStep S p)
            hxFrontier).mp hfix
        · intro hxTerminal
          have htail :
              x ∈ squareRootLowPrimeProcessedSeatMatchingFrontier ps
                (squareRootLowPrimeProcessedSeatFrontierStep S p) := by
            simpa [squareRootLowPrimeProcessedSeatMatchingFrontier] using hxTerminal
          have hfix := (ih
            (S := squareRootLowPrimeProcessedSeatFrontierStep S p)
            hxFrontier).mpr htail
          simpa [squareRootLowPrimeProcessedSeatChronologicalOthelloMate,
            hxPaired] using hfix

/-- Fixed states of a chronological Othello mate are exactly its iterated
matching frontier. -/
theorem finiteOthelloStablePart_processedSeatChronological_eq_frontier
    (ps : List ℕ) (S : Finset SquareRootLowPrimeProcessedState) :
    finiteOthelloStablePart S
        (squareRootLowPrimeProcessedSeatChronologicalOthelloMate ps S) =
      squareRootLowPrimeProcessedSeatMatchingFrontier ps S := by
  classical
  ext x
  constructor
  · intro hxStable
    rcases Finset.mem_filter.mp hxStable with ⟨hxS, hfix⟩
    exact (squareRootLowPrimeProcessedSeatChronologicalOthelloMate_eq_self_iff
      ps S hxS).mp hfix
  · intro hxTerminal
    have hxS := squareRootLowPrimeProcessedSeatMatchingFrontier_subset_local
      ps S hxTerminal
    exact Finset.mem_filter.mpr
      ⟨hxS,
        (squareRootLowPrimeProcessedSeatChronologicalOthelloMate_eq_self_iff
          ps S hxS).mpr hxTerminal⟩

/-- **Candidate second Othello matching on the true processed-seat carrier.**

The same legal fresh-prime edges are played in descending owner order.  The
subsequent endpoint theorem decides whether this is already the final rematch or
only the prime-toggle component of the final alternating construction. -/
noncomputable def squareRootLowPrimeProcessedSeatNoLibertyMate
    (R K j U : ℕ) :
    SquareRootLowPrimeProcessedState → SquareRootLowPrimeProcessedState :=
  squareRootLowPrimeProcessedSeatChronologicalOthelloMate
    (squareRootLowPrimeFreshPrimeListDescending K U)
    (squareRootLowPrimeProcessedSeatCarrier R K j U)

/-- The candidate second matching preserves the true processed-seat carrier. -/
theorem squareRootLowPrimeProcessedSeatNoLibertyMate_mem
    {R K j U : ℕ} {x : SquareRootLowPrimeProcessedState}
    (hx : x ∈ squareRootLowPrimeProcessedSeatCarrier R K j U) :
    squareRootLowPrimeProcessedSeatNoLibertyMate R K j U x ∈
      squareRootLowPrimeProcessedSeatCarrier R K j U := by
  exact squareRootLowPrimeProcessedSeatChronologicalOthelloMate_mem
    (squareRootLowPrimeFreshPrimeListDescending K U)
    (squareRootLowPrimeProcessedSeatCarrier R K j U) hx

/-- The candidate second matching is involutive on the true carrier. -/
theorem squareRootLowPrimeProcessedSeatNoLibertyMate_involutive
    {R K j U : ℕ} {x : SquareRootLowPrimeProcessedState}
    (hx : x ∈ squareRootLowPrimeProcessedSeatCarrier R K j U) :
    squareRootLowPrimeProcessedSeatNoLibertyMate R K j U
        (squareRootLowPrimeProcessedSeatNoLibertyMate R K j U x) = x := by
  apply squareRootLowPrimeProcessedSeatChronologicalOthelloMate_involutive
    (squareRootLowPrimeFreshPrimeListDescending K U)
    (squareRootLowPrimeProcessedSeatCarrier R K j U)
  · intro p hp
    exact (prime_of_mem_squareRootLowPrimeFreshPrimeListDescending hp).pos
  · exact hx

/-- Every moved state of the candidate second matching reverses native weight. -/
theorem squareRootLowPrimeProcessedSeatNoLibertyMate_weight_neg
    {R K j U : ℕ} {x : SquareRootLowPrimeProcessedState}
    (hx : x ∈ squareRootLowPrimeProcessedSeatCarrier R K j U)
    (hne : squareRootLowPrimeProcessedSeatNoLibertyMate R K j U x ≠ x) :
    squareRootLowPrimeProcessedSeatWeightReal
        (squareRootLowPrimeProcessedSeatNoLibertyMate R K j U x) =
      -squareRootLowPrimeProcessedSeatWeightReal x := by
  apply squareRootLowPrimeProcessedSeatChronologicalOthelloMate_weight_neg
    (squareRootLowPrimeFreshPrimeListDescending K U)
    (squareRootLowPrimeProcessedSeatCarrier R K j U)
  · intro p hp
    exact prime_of_mem_squareRootLowPrimeFreshPrimeListDescending hp
  · exact hx
  · exact hne

/-- The candidate stable set is literally the descending processed-seat
frontier. -/
theorem finiteOthelloStablePart_processedSeatNoLibertyMate_eq_descendingFrontier
    (R K j U : ℕ) :
    finiteOthelloStablePart
        (squareRootLowPrimeProcessedSeatCarrier R K j U)
        (squareRootLowPrimeProcessedSeatNoLibertyMate R K j U) =
      squareRootLowPrimeProcessedSeatDescendingTerminalFrontier R K j U := by
  exact finiteOthelloStablePart_processedSeatChronological_eq_frontier
    (squareRootLowPrimeFreshPrimeListDescending K U)
    (squareRootLowPrimeProcessedSeatCarrier R K j U)

/-- Finite cancellation already identifies the stable mass of this legal
candidate with the actual running imbalance. -/
theorem squareRootLowPrimeProcessedSeatNoLibertyMate_stableMass_eq_runningImbalance
    {R K j U : ℕ} (hR : 2 ≤ R) :
    (∑ x ∈ finiteOthelloStablePart
        (squareRootLowPrimeProcessedSeatCarrier R K j U)
        (squareRootLowPrimeProcessedSeatNoLibertyMate R K j U),
      squareRootLowPrimeProcessedSeatWeightReal x) =
      squareRootLowPrimeRunningImbalanceReal R K j U := by
  calc
    (∑ x ∈ finiteOthelloStablePart
        (squareRootLowPrimeProcessedSeatCarrier R K j U)
        (squareRootLowPrimeProcessedSeatNoLibertyMate R K j U),
      squareRootLowPrimeProcessedSeatWeightReal x) =
      ∑ x ∈ squareRootLowPrimeProcessedSeatCarrier R K j U,
        squareRootLowPrimeProcessedSeatWeightReal x :=
        (sum_finiteOthelloRegion_eq_stable
          (squareRootLowPrimeProcessedSeatCarrier R K j U)
          (squareRootLowPrimeProcessedSeatNoLibertyMate R K j U)
          squareRootLowPrimeProcessedSeatWeightReal
          (fun x hx => squareRootLowPrimeProcessedSeatNoLibertyMate_mem hx)
          (fun x hx => squareRootLowPrimeProcessedSeatNoLibertyMate_involutive hx)
          (fun x hx hne =>
            squareRootLowPrimeProcessedSeatNoLibertyMate_weight_neg hx hne)).symm
    _ = squareRootLowPrimeRunningImbalanceReal R K j U :=
      squareRootLowPrimeProcessedSeatCarrier_mass_eq_runningImbalanceReal hR

end RHLean.Proof
