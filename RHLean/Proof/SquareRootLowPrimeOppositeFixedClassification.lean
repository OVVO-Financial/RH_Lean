import Mathlib
import RHLean.Proof.FiniteOthelloMatching
import RHLean.Proof.SquareRootLowPrimeDescendingPivotStability
import RHLean.Proof.SquareRootLowPrimeNoLibertyBoundaryHome

/-!
# Opposite processed-seat Othello matching

The first processed-seat chronology removes the available fresh-prime edges in
increasing prime order.  For the opposite Othello position we use the very same
Euler edges

`some (c,s) <-> some (p*c,s)`

but play them in descending prime order.  At the first stage where a state is
removed, remember its unique opposite endpoint; states never removed are fixed.
This packages the whole descending chronology as one self-map of the original
processed-seat carrier.

Every moved edge is an actual fresh-prime multiplication, so the native
processed-seat weight changes sign.  The map is an involution because the two
endpoints are removed at the same first stage and are sent back to one another.
Its stable part is therefore exactly the already-defined descending terminal
frontier.

The carrier-specific theorem still required below this layer is the exact
classification of that stable frontier by the four post-rematching endpoint
classes in `SquareRootLowPrimeNoLibertyBoundaryHome`.  No estimate or analytic
input occurs in this file.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- The literal state type of the complete processed-seat carrier. -/
abbrev SquareRootLowPrimeProcessedState := Option (ℕ × ℕ)

/-- Unique lower endpoint whose `p`-extension is a given upper endpoint. -/
noncomputable def squareRootLowPrimeProcessedSeatOthelloPairPreimage
    (S : Finset SquareRootLowPrimeProcessedState) (p : ℕ)
    (x : SquareRootLowPrimeProcessedState)
    (h : ∃ y ∈ squareRootLowPrimeProcessedSeatPairLower S p,
      squareRootLowPrimeProcessedSeatExtend p y = x) :
    SquareRootLowPrimeProcessedState :=
  Classical.choose h

private theorem squareRootLowPrimeProcessedSeatOthelloPairPreimage_spec
    {S : Finset SquareRootLowPrimeProcessedState} {p : ℕ}
    {x : SquareRootLowPrimeProcessedState}
    (h : ∃ y ∈ squareRootLowPrimeProcessedSeatPairLower S p,
      squareRootLowPrimeProcessedSeatExtend p y = x) :
    squareRootLowPrimeProcessedSeatOthelloPairPreimage S p x h ∈
        squareRootLowPrimeProcessedSeatPairLower S p ∧
      squareRootLowPrimeProcessedSeatExtend p
        (squareRootLowPrimeProcessedSeatOthelloPairPreimage S p x h) = x := by
  exact Classical.choose_spec h

/-- One processed-seat prime matching completed by fixed points. -/
noncomputable def squareRootLowPrimeProcessedSeatStepOthelloMate
    (S : Finset SquareRootLowPrimeProcessedState) (p : ℕ) :
    SquareRootLowPrimeProcessedState → SquareRootLowPrimeProcessedState :=
  fun x =>
    if hx : x ∈ squareRootLowPrimeProcessedSeatPairLower S p then
      squareRootLowPrimeProcessedSeatExtend p x
    else if hupper :
        ∃ y ∈ squareRootLowPrimeProcessedSeatPairLower S p,
          squareRootLowPrimeProcessedSeatExtend p y = x then
      squareRootLowPrimeProcessedSeatOthelloPairPreimage S p x hupper
    else x

private theorem squareRootLowPrimeProcessedSeatPairUpper_iff_exists_lower_othello
    {S : Finset SquareRootLowPrimeProcessedState} {p : ℕ}
    {x : SquareRootLowPrimeProcessedState} :
    x ∈ squareRootLowPrimeProcessedSeatPairUpper S p ↔
      ∃ y ∈ squareRootLowPrimeProcessedSeatPairLower S p,
        squareRootLowPrimeProcessedSeatExtend p y = x := by
  simp [squareRootLowPrimeProcessedSeatPairUpper]

/-- One processed-seat Othello step preserves its current finite row. -/
theorem squareRootLowPrimeProcessedSeatStepOthelloMate_mem
    (S : Finset SquareRootLowPrimeProcessedState) (p : ℕ)
    {x : SquareRootLowPrimeProcessedState} (hxS : x ∈ S) :
    squareRootLowPrimeProcessedSeatStepOthelloMate S p x ∈ S := by
  classical
  by_cases hxLower : x ∈ squareRootLowPrimeProcessedSeatPairLower S p
  · simp [squareRootLowPrimeProcessedSeatStepOthelloMate, hxLower]
    exact (mem_squareRootLowPrimeProcessedSeatPairLower.mp hxLower).2.2.2
  · by_cases hupper :
      ∃ y ∈ squareRootLowPrimeProcessedSeatPairLower S p,
        squareRootLowPrimeProcessedSeatExtend p y = x
    · have hspec := squareRootLowPrimeProcessedSeatOthelloPairPreimage_spec hupper
      simp [squareRootLowPrimeProcessedSeatStepOthelloMate, hxLower, hupper]
      exact (mem_squareRootLowPrimeProcessedSeatPairLower.mp hspec.1).1
    · simp [squareRootLowPrimeProcessedSeatStepOthelloMate, hxLower, hupper, hxS]

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
    have hpre :
        ∃ z ∈ squareRootLowPrimeProcessedSeatPairLower S p,
          squareRootLowPrimeProcessedSeatExtend p z = y :=
      ⟨x, hxLower, rfl⟩
    have hspec := squareRootLowPrimeProcessedSeatOthelloPairPreimage_spec hpre
    have hback :
        squareRootLowPrimeProcessedSeatOthelloPairPreimage S p y hpre = x := by
      apply squareRootLowPrimeProcessedSeatExtend_injOn hp hspec.1 hxLower
      simpa [y] using hspec.2
    simp [squareRootLowPrimeProcessedSeatStepOthelloMate,
      hxLower, y, hyNotLower, hpre, hback]
  · by_cases hupper :
      ∃ y ∈ squareRootLowPrimeProcessedSeatPairLower S p,
        squareRootLowPrimeProcessedSeatExtend p y = x
    · let y := squareRootLowPrimeProcessedSeatOthelloPairPreimage S p x hupper
      have hyLower : y ∈ squareRootLowPrimeProcessedSeatPairLower S p :=
        (squareRootLowPrimeProcessedSeatOthelloPairPreimage_spec hupper).1
      have hyExt : squareRootLowPrimeProcessedSeatExtend p y = x :=
        (squareRootLowPrimeProcessedSeatOthelloPairPreimage_spec hupper).2
      simp [squareRootLowPrimeProcessedSeatStepOthelloMate,
        hxLower, hupper, y, hyLower, hyExt]
    · simp [squareRootLowPrimeProcessedSeatStepOthelloMate, hxLower, hupper]

/-- One-step fixed points are exactly the states outside the paired population. -/
theorem squareRootLowPrimeProcessedSeatStepOthelloMate_eq_self_iff
    (S : Finset SquareRootLowPrimeProcessedState) (p : ℕ)
    {x : SquareRootLowPrimeProcessedState} :
    squareRootLowPrimeProcessedSeatStepOthelloMate S p x = x ↔
      x ∉ squareRootLowPrimeProcessedSeatPaired S p := by
  classical
  by_cases hxLower : x ∈ squareRootLowPrimeProcessedSeatPairLower S p
  · have hxPaired : x ∈ squareRootLowPrimeProcessedSeatPaired S p :=
      Finset.mem_union.mpr (Or.inl hxLower)
    have hne : squareRootLowPrimeProcessedSeatExtend p x ≠ x := by
      intro heq
      have hxUpper : x ∈ squareRootLowPrimeProcessedSeatPairUpper S p := by
        unfold squareRootLowPrimeProcessedSeatPairUpper
        exact Finset.mem_image.mpr ⟨x, hxLower, heq⟩
      exact (Finset.disjoint_left.mp
        (squareRootLowPrimeProcessedSeatPairLower_disjoint_upper S p))
        hxLower hxUpper
    simp [squareRootLowPrimeProcessedSeatStepOthelloMate,
      hxLower, hxPaired, hne]
  · by_cases hupper :
      ∃ y ∈ squareRootLowPrimeProcessedSeatPairLower S p,
        squareRootLowPrimeProcessedSeatExtend p y = x
    · have hxUpper : x ∈ squareRootLowPrimeProcessedSeatPairUpper S p :=
        squareRootLowPrimeProcessedSeatPairUpper_iff_exists_lower_othello.mpr hupper
      have hxPaired : x ∈ squareRootLowPrimeProcessedSeatPaired S p :=
        Finset.mem_union.mpr (Or.inr hxUpper)
      have hspec := squareRootLowPrimeProcessedSeatOthelloPairPreimage_spec hupper
      have hne :
          squareRootLowPrimeProcessedSeatOthelloPairPreimage S p x hupper ≠ x := by
        intro heq
        have hxLower' : x ∈ squareRootLowPrimeProcessedSeatPairLower S p := by
          simpa [heq] using hspec.1
        exact hxLower hxLower'
      simp [squareRootLowPrimeProcessedSeatStepOthelloMate,
        hxLower, hupper, hxPaired, hne]
    · have hxNotUpper : x ∉ squareRootLowPrimeProcessedSeatPairUpper S p := by
        simpa [squareRootLowPrimeProcessedSeatPairUpper_iff_exists_lower_othello]
          using hupper
      have hxNotPaired : x ∉ squareRootLowPrimeProcessedSeatPaired S p := by
        intro hx
        rcases Finset.mem_union.mp hx with h | h
        · exact hxLower h
        · exact hxNotUpper h
      simp [squareRootLowPrimeProcessedSeatStepOthelloMate,
        hxLower, hupper, hxNotPaired]

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
  · simp [squareRootLowPrimeProcessedSeatStepOthelloMate, hxLower]
    exact squareRootLowPrimeProcessedSeatExtend_weight_eq_neg hp hxLower
  · by_cases hupper :
      ∃ y ∈ squareRootLowPrimeProcessedSeatPairLower S p,
        squareRootLowPrimeProcessedSeatExtend p y = x
    · have hspec := squareRootLowPrimeProcessedSeatOthelloPairPreimage_spec hupper
      have hforward :=
        squareRootLowPrimeProcessedSeatExtend_weight_eq_neg hp hspec.1
      rw [hspec.2] at hforward
      simp [squareRootLowPrimeProcessedSeatStepOthelloMate, hxLower, hupper]
      linarith
    · simp [squareRootLowPrimeProcessedSeatStepOthelloMate, hxLower, hupper]
        at hne

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
      · simp [squareRootLowPrimeProcessedSeatChronologicalOthelloMate, hxPaired]
        exact squareRootLowPrimeProcessedSeatStepOthelloMate_mem S p hxS
      · have hxFrontier : x ∈ squareRootLowPrimeProcessedSeatFrontierStep S p :=
          Finset.mem_sdiff.mpr ⟨hxS, hxPaired⟩
        have hrec := ih
          (S := squareRootLowPrimeProcessedSeatFrontierStep S p) hxFrontier
        simp [squareRootLowPrimeProcessedSeatChronologicalOthelloMate, hxPaired]
        exact squareRootLowPrimeProcessedSeatFrontierStep_subset' S p hrec

/-- The global chronology is an involution on the original finite carrier. -/
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
        have hyS : y ∈ S :=
          squareRootLowPrimeProcessedSeatStepOthelloMate_mem S p
            (squareRootLowPrimeProcessedSeatPaired_subset S p hxPaired)
        have hyPaired : y ∈ squareRootLowPrimeProcessedSeatPaired S p := by
          have hfix := squareRootLowPrimeProcessedSeatStepOthelloMate_eq_self_iff S p
          by_contra hnot
          have hyFixed : squareRootLowPrimeProcessedSeatStepOthelloMate S p y = y :=
            hfix.mpr hnot
          have hback :=
            squareRootLowPrimeProcessedSeatStepOthelloMate_involutive S hp x
          change squareRootLowPrimeProcessedSeatStepOthelloMate S p y = x at hback
          rw [hyFixed] at hback
          subst y
          exact hnot hxPaired
        simp [squareRootLowPrimeProcessedSeatChronologicalOthelloMate,
          hxPaired, y, hyPaired,
          squareRootLowPrimeProcessedSeatStepOthelloMate_involutive S hp x]
      · have hxFrontier : x ∈ squareRootLowPrimeProcessedSeatFrontierStep S p :=
          Finset.mem_sdiff.mpr ⟨hxS, hxPaired⟩
        let y := squareRootLowPrimeProcessedSeatChronologicalOthelloMate ps
          (squareRootLowPrimeProcessedSeatFrontierStep S p) x
        have hyFrontier : y ∈ squareRootLowPrimeProcessedSeatFrontierStep S p :=
          squareRootLowPrimeProcessedSeatChronologicalOthelloMate_mem ps
            (squareRootLowPrimeProcessedSeatFrontierStep S p) hxFrontier
        have hyNotPaired : y ∉ squareRootLowPrimeProcessedSeatPaired S p :=
          (Finset.mem_sdiff.mp hyFrontier).2
        have hrec := ih
          (S := squareRootLowPrimeProcessedSeatFrontierStep S p)
          hrest hxFrontier
        simp [squareRootLowPrimeProcessedSeatChronologicalOthelloMate,
          hxPaired, y, hyNotPaired] at hrec ⊢
        exact hrec

/-- Every moved state of the global chronology still reverses native weight. -/
theorem squareRootLowPrimeProcessedSeatChronologicalOthelloMate_weight_neg
    (ps : List ℕ) (S : Finset SquareRootLowPrimeProcessedState)
    (hprime : ∀ p ∈ ps, p.Prime)
    {x : SquareRootLowPrimeProcessedState} (hxS : x ∈ S)
    (hne : squareRootLowPrimeProcessedSeatChronologicalOthelloMate ps S x ≠ x) :
    squareRootLowPrimeProcessedSeatWeightReal
        (squareRootLowPrimeProcessedSeatChronologicalOthelloMate ps S x) =
      -squareRootLowPrimeProcessedSeatWeightReal x := by
  induction ps generalizing S x with
  | nil => simp [squareRootLowPrimeProcessedSeatChronologicalOthelloMate] at hne
  | cons p ps ih =>
      have hp : p.Prime := hprime p (by simp)
      have hrest : ∀ q ∈ ps, q.Prime := by
        intro q hq
        exact hprime q (by simp [hq])
      by_cases hxPaired : x ∈ squareRootLowPrimeProcessedSeatPaired S p
      · have hstepNe : squareRootLowPrimeProcessedSeatStepOthelloMate S p x ≠ x :=
          fun h =>
            (squareRootLowPrimeProcessedSeatStepOthelloMate_eq_self_iff S p).mp h
              hxPaired
        simp [squareRootLowPrimeProcessedSeatChronologicalOthelloMate, hxPaired]
        exact squareRootLowPrimeProcessedSeatStepOthelloMate_weight_neg
          S hp x hstepNe
      · have hxFrontier : x ∈ squareRootLowPrimeProcessedSeatFrontierStep S p :=
          Finset.mem_sdiff.mpr ⟨hxS, hxPaired⟩
        simp [squareRootLowPrimeProcessedSeatChronologicalOthelloMate, hxPaired]
          at hne ⊢
        exact ih
          (S := squareRootLowPrimeProcessedSeatFrontierStep S p)
          hrest hxFrontier hne

/-- Fixed states of a chronological Othello mate are exactly its iterated
matching frontier. -/
theorem finiteOthelloStablePart_processedSeatChronological_eq_frontier
    (ps : List ℕ) (S : Finset SquareRootLowPrimeProcessedState) :
    finiteOthelloStablePart S
        (squareRootLowPrimeProcessedSeatChronologicalOthelloMate ps S) =
      squareRootLowPrimeProcessedSeatMatchingFrontier ps S := by
  classical
  induction ps generalizing S with
  | nil =>
      ext x
      simp [finiteOthelloStablePart,
        squareRootLowPrimeProcessedSeatChronologicalOthelloMate,
        squareRootLowPrimeProcessedSeatMatchingFrontier]
  | cons p ps ih =>
      ext x
      by_cases hxS : x ∈ S
      · by_cases hxPaired : x ∈ squareRootLowPrimeProcessedSeatPaired S p
        · have hstepNe : squareRootLowPrimeProcessedSeatStepOthelloMate S p x ≠ x :=
            fun h =>
              (squareRootLowPrimeProcessedSeatStepOthelloMate_eq_self_iff S p).mp h
                hxPaired
          have hxNotFrontier :
              x ∉ squareRootLowPrimeProcessedSeatMatchingFrontier (p :: ps) S := by
            intro hx
            have hxStep := squareRootLowPrimeProcessedSeatMatchingFrontier_subset'
              ps (squareRootLowPrimeProcessedSeatFrontierStep S p) hx
            exact (Finset.mem_sdiff.mp hxStep).2 hxPaired
          simp [finiteOthelloStablePart,
            squareRootLowPrimeProcessedSeatChronologicalOthelloMate,
            squareRootLowPrimeProcessedSeatMatchingFrontier,
            hxS, hxPaired, hstepNe, hxNotFrontier]
        · have hxStep : x ∈ squareRootLowPrimeProcessedSeatFrontierStep S p :=
            Finset.mem_sdiff.mpr ⟨hxS, hxPaired⟩
          have hih := Finset.ext_iff.mp
            (ih (S := squareRootLowPrimeProcessedSeatFrontierStep S p)) x
          simp only [finiteOthelloStablePart, Finset.mem_filter] at hih
          simp [finiteOthelloStablePart,
            squareRootLowPrimeProcessedSeatChronologicalOthelloMate,
            squareRootLowPrimeProcessedSeatMatchingFrontier,
            hxS, hxPaired, hxStep, hih]
      · have hxNotPaired : x ∉ squareRootLowPrimeProcessedSeatPaired S p :=
          fun hx => hxS (squareRootLowPrimeProcessedSeatPaired_subset S p hx)
        have hxNotFrontier :
            x ∉ squareRootLowPrimeProcessedSeatMatchingFrontier (p :: ps) S :=
          fun hx => hxS
            (squareRootLowPrimeProcessedSeatMatchingFrontier_subset' (p :: ps) S hx)
        simp [finiteOthelloStablePart,
          squareRootLowPrimeProcessedSeatChronologicalOthelloMate,
          squareRootLowPrimeProcessedSeatMatchingFrontier,
          hxS, hxNotPaired, hxNotFrontier]

/-- **Second Othello matching on the true processed-seat carrier.**

The same legal fresh-prime edges are played in descending owner order. -/
noncomputable def squareRootLowPrimeProcessedSeatNoLibertyMate
    (R K j U : ℕ) :
    SquareRootLowPrimeProcessedState → SquareRootLowPrimeProcessedState :=
  squareRootLowPrimeProcessedSeatChronologicalOthelloMate
    (squareRootLowPrimeFreshPrimeListDescending K U)
    (squareRootLowPrimeProcessedSeatCarrier R K j U)

/-- The second matching preserves the true processed-seat carrier. -/
theorem squareRootLowPrimeProcessedSeatNoLibertyMate_mem
    {R K j U : ℕ} {x : SquareRootLowPrimeProcessedState}
    (hx : x ∈ squareRootLowPrimeProcessedSeatCarrier R K j U) :
    squareRootLowPrimeProcessedSeatNoLibertyMate R K j U x ∈
      squareRootLowPrimeProcessedSeatCarrier R K j U := by
  exact squareRootLowPrimeProcessedSeatChronologicalOthelloMate_mem
    (squareRootLowPrimeFreshPrimeListDescending K U)
    (squareRootLowPrimeProcessedSeatCarrier R K j U) hx

/-- The second matching is involutive on the true processed-seat carrier. -/
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

/-- Every moved state of the second matching reverses the native processed-seat
weight. -/
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

/-- The stable set of `match₂` is literally the descending processed-seat
frontier.  The final arithmetic classifier must identify this frontier with the
four tagged no-liberty endpoint classes. -/
theorem finiteOthelloStablePart_processedSeatNoLibertyMate_eq_descendingFrontier
    (R K j U : ℕ) :
    finiteOthelloStablePart
        (squareRootLowPrimeProcessedSeatCarrier R K j U)
        (squareRootLowPrimeProcessedSeatNoLibertyMate R K j U) =
      squareRootLowPrimeProcessedSeatDescendingTerminalFrontier R K j U := by
  exact finiteOthelloStablePart_processedSeatChronological_eq_frontier
    (squareRootLowPrimeFreshPrimeListDescending K U)
    (squareRootLowPrimeProcessedSeatCarrier R K j U)

/-- The stable mass of the second legal Othello matching already equals the
actual running imbalance.  This uses only finite sign cancellation on the true
processed carrier; no first matching is needed for this equality. -/
theorem squareRootLowPrimeProcessedSeatNoLibertyMate_stableMass_eq_runningImbalance
    {R K j U : ℕ} (hR : 2 ≤ R) :
    (∑ x ∈ finiteOthelloStablePart
        (squareRootLowPrimeProcessedSeatCarrier R K j U)
        (squareRootLowPrimeProcessedSeatNoLibertyMate R K j U),
      squareRootLowPrimeProcessedSeatWeightReal x) =
      squareRootLowPrimeRunningImbalanceReal R K j U := by
  rw [← squareRootLowPrimeProcessedSeatCarrier_mass_eq_runningImbalanceReal hR]
  symm
  exact sum_finiteOthelloRegion_eq_stable
    (squareRootLowPrimeProcessedSeatCarrier R K j U)
    (squareRootLowPrimeProcessedSeatNoLibertyMate R K j U)
    squareRootLowPrimeProcessedSeatWeightReal
    (fun x hx => squareRootLowPrimeProcessedSeatNoLibertyMate_mem hx)
    (fun x hx => squareRootLowPrimeProcessedSeatNoLibertyMate_involutive hx)
    (fun x hx hne => squareRootLowPrimeProcessedSeatNoLibertyMate_weight_neg hx hne)

end RHLean.Proof
