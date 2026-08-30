import Mathlib
import RHLean.Proof.AlternatingSignMatchingParity
import RHLean.Proof.SquareRootLowPrimeMatchingDisplacement

/-!
# The complete processed-prime chronology as one involution

Sequential fresh-prime matching can be viewed as one Othello position rather
than a long sequence of local deletions.  At the first stage where a state is
paired, remember its unique opposite endpoint; states never paired are fixed.

The resulting global map is a genuine sign-reversing involution on the original
finite carrier.  Its fixed set is exactly the existing iterated matching
frontier.  Thus the terminal frontier is literally a fixed-point set, allowing
it to be compared to a second arithmetic involution by the finite parity
principle in `AlternatingSignMatchingParity`.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Unique lower endpoint whose `p`-extension is a given upper endpoint. -/
noncomputable def squareRootLowPrimeProcessedSeatPairPreimage
    (S : Finset SquareRootLowPrimeProcessedState) (p : ℕ)
    (x : SquareRootLowPrimeProcessedState)
    (h : ∃ y ∈ squareRootLowPrimeProcessedSeatPairLower S p,
      squareRootLowPrimeProcessedSeatExtend p y = x) :
    SquareRootLowPrimeProcessedState :=
  Classical.choose h

private theorem squareRootLowPrimeProcessedSeatPairPreimage_spec
    {S : Finset SquareRootLowPrimeProcessedState} {p : ℕ}
    {x : SquareRootLowPrimeProcessedState}
    (h : ∃ y ∈ squareRootLowPrimeProcessedSeatPairLower S p,
      squareRootLowPrimeProcessedSeatExtend p y = x) :
    squareRootLowPrimeProcessedSeatPairPreimage S p x h ∈
        squareRootLowPrimeProcessedSeatPairLower S p ∧
      squareRootLowPrimeProcessedSeatExtend p
        (squareRootLowPrimeProcessedSeatPairPreimage S p x h) = x := by
  exact Classical.choose_spec h

/-- One prime matching, completed by fixed points to a self-map. -/
noncomputable def squareRootLowPrimeProcessedSeatStepInvolution
    (S : Finset SquareRootLowPrimeProcessedState) (p : ℕ) :
    SquareRootLowPrimeProcessedState → SquareRootLowPrimeProcessedState :=
  fun x =>
    if hx : x ∈ squareRootLowPrimeProcessedSeatPairLower S p then
      squareRootLowPrimeProcessedSeatExtend p x
    else if hupper :
        ∃ y ∈ squareRootLowPrimeProcessedSeatPairLower S p,
          squareRootLowPrimeProcessedSeatExtend p y = x then
      squareRootLowPrimeProcessedSeatPairPreimage S p x hupper
    else x

private theorem squareRootLowPrimeProcessedSeatPairUpper_iff_exists_lower
    {S : Finset SquareRootLowPrimeProcessedState} {p : ℕ}
    {x : SquareRootLowPrimeProcessedState} :
    x ∈ squareRootLowPrimeProcessedSeatPairUpper S p ↔
      ∃ y ∈ squareRootLowPrimeProcessedSeatPairLower S p,
        squareRootLowPrimeProcessedSeatExtend p y = x := by
  simp [squareRootLowPrimeProcessedSeatPairUpper]

/-- The one-step involution preserves the ambient carrier. -/
theorem squareRootLowPrimeProcessedSeatStepInvolution_mem
    (S : Finset SquareRootLowPrimeProcessedState) (p : ℕ)
    {x : SquareRootLowPrimeProcessedState} (hxS : x ∈ S) :
    squareRootLowPrimeProcessedSeatStepInvolution S p x ∈ S := by
  classical
  by_cases hxLower : x ∈ squareRootLowPrimeProcessedSeatPairLower S p
  · simp [squareRootLowPrimeProcessedSeatStepInvolution, hxLower]
    exact (mem_squareRootLowPrimeProcessedSeatPairLower.mp hxLower).2.2.2
  · by_cases hupper :
      ∃ y ∈ squareRootLowPrimeProcessedSeatPairLower S p,
        squareRootLowPrimeProcessedSeatExtend p y = x
    · have hspec := squareRootLowPrimeProcessedSeatPairPreimage_spec hupper
      simp [squareRootLowPrimeProcessedSeatStepInvolution, hxLower, hupper]
      exact (mem_squareRootLowPrimeProcessedSeatPairLower.mp hspec.1).1
    · simp [squareRootLowPrimeProcessedSeatStepInvolution, hxLower, hupper, hxS]

/-- Every lower endpoint is sent to the corresponding upper endpoint, and the
upper endpoint is sent back. -/
theorem squareRootLowPrimeProcessedSeatStepInvolution_involutive
    (S : Finset SquareRootLowPrimeProcessedState) {p : ℕ} (hp : 0 < p)
    (x : SquareRootLowPrimeProcessedState) :
    squareRootLowPrimeProcessedSeatStepInvolution S p
        (squareRootLowPrimeProcessedSeatStepInvolution S p x) = x := by
  classical
  by_cases hxLower : x ∈ squareRootLowPrimeProcessedSeatPairLower S p
  · let y := squareRootLowPrimeProcessedSeatExtend p x
    have hyUpper : y ∈ squareRootLowPrimeProcessedSeatPairUpper S p := by
      unfold y squareRootLowPrimeProcessedSeatPairUpper
      exact Finset.mem_image.mpr ⟨x, hxLower, rfl⟩
    have hyNotLower : y ∉ squareRootLowPrimeProcessedSeatPairLower S p := by
      exact (Finset.disjoint_left.mp
        (squareRootLowPrimeProcessedSeatPairLower_disjoint_upper S p))
        (by exact hyUpper) |>.elim
    have hpre :
        ∃ z ∈ squareRootLowPrimeProcessedSeatPairLower S p,
          squareRootLowPrimeProcessedSeatExtend p z = y :=
      ⟨x, hxLower, rfl⟩
    have hspec := squareRootLowPrimeProcessedSeatPairPreimage_spec hpre
    have hback : squareRootLowPrimeProcessedSeatPairPreimage S p y hpre = x :=
      squareRootLowPrimeProcessedSeatExtend_injOn hp hspec.1 hxLower hspec.2
    simp [squareRootLowPrimeProcessedSeatStepInvolution, hxLower, y,
      hyNotLower, hpre, hback]
  · by_cases hupper :
      ∃ y ∈ squareRootLowPrimeProcessedSeatPairLower S p,
        squareRootLowPrimeProcessedSeatExtend p y = x
    · let y := squareRootLowPrimeProcessedSeatPairPreimage S p x hupper
      have hyLower : y ∈ squareRootLowPrimeProcessedSeatPairLower S p :=
        (squareRootLowPrimeProcessedSeatPairPreimage_spec hupper).1
      have hyExt : squareRootLowPrimeProcessedSeatExtend p y = x :=
        (squareRootLowPrimeProcessedSeatPairPreimage_spec hupper).2
      simp [squareRootLowPrimeProcessedSeatStepInvolution, hxLower, hupper,
        y, hyLower, hyExt]
    · simp [squareRootLowPrimeProcessedSeatStepInvolution, hxLower, hupper]

/-- One-step fixed points are exactly states outside the paired population. -/
theorem squareRootLowPrimeProcessedSeatStepInvolution_eq_self_iff
    (S : Finset SquareRootLowPrimeProcessedState) (p : ℕ)
    {x : SquareRootLowPrimeProcessedState} :
    squareRootLowPrimeProcessedSeatStepInvolution S p x = x ↔
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
    simp [squareRootLowPrimeProcessedSeatStepInvolution, hxLower,
      hxPaired, hne]
  · by_cases hupper :
      ∃ y ∈ squareRootLowPrimeProcessedSeatPairLower S p,
        squareRootLowPrimeProcessedSeatExtend p y = x
    · have hxUpper : x ∈ squareRootLowPrimeProcessedSeatPairUpper S p :=
        squareRootLowPrimeProcessedSeatPairUpper_iff_exists_lower.mpr hupper
      have hxPaired : x ∈ squareRootLowPrimeProcessedSeatPaired S p :=
        Finset.mem_union.mpr (Or.inr hxUpper)
      have hspec := squareRootLowPrimeProcessedSeatPairPreimage_spec hupper
      have hne : squareRootLowPrimeProcessedSeatPairPreimage S p x hupper ≠ x := by
        intro heq
        have hxLower' : x ∈ squareRootLowPrimeProcessedSeatPairLower S p := by
          simpa [heq] using hspec.1
        exact hxLower hxLower'
      simp [squareRootLowPrimeProcessedSeatStepInvolution, hxLower, hupper,
        hxPaired, hne]
    · have hxNotUpper : x ∉ squareRootLowPrimeProcessedSeatPairUpper S p := by
        simpa [squareRootLowPrimeProcessedSeatPairUpper_iff_exists_lower]
          using hupper
      have hxNotPaired : x ∉ squareRootLowPrimeProcessedSeatPaired S p := by
        intro hx
        rcases Finset.mem_union.mp hx with h | h
        · exact hxLower h
        · exact hxNotUpper h
      simp [squareRootLowPrimeProcessedSeatStepInvolution, hxLower, hupper,
        hxNotPaired]

/-- Every moved one-step state has opposite processed-seat weight. -/
theorem squareRootLowPrimeProcessedSeatStepInvolution_weight_neg
    (S : Finset SquareRootLowPrimeProcessedState) {p : ℕ} (hp : p.Prime)
    (x : SquareRootLowPrimeProcessedState)
    (hne : squareRootLowPrimeProcessedSeatStepInvolution S p x ≠ x) :
    squareRootLowPrimeProcessedSeatWeightReal
        (squareRootLowPrimeProcessedSeatStepInvolution S p x) =
      -squareRootLowPrimeProcessedSeatWeightReal x := by
  classical
  by_cases hxLower : x ∈ squareRootLowPrimeProcessedSeatPairLower S p
  · simp [squareRootLowPrimeProcessedSeatStepInvolution, hxLower]
    exact squareRootLowPrimeProcessedSeatExtend_weight_eq_neg hp hxLower
  · by_cases hupper :
      ∃ y ∈ squareRootLowPrimeProcessedSeatPairLower S p,
        squareRootLowPrimeProcessedSeatExtend p y = x
    · have hspec := squareRootLowPrimeProcessedSeatPairPreimage_spec hupper
      have hforward :=
        squareRootLowPrimeProcessedSeatExtend_weight_eq_neg hp hspec.1
      rw [hspec.2] at hforward
      simp [squareRootLowPrimeProcessedSeatStepInvolution, hxLower, hupper]
      linarith
    · simp [squareRootLowPrimeProcessedSeatStepInvolution, hxLower, hupper]
      at hne

/-- Complete chronological matching, with every state paired at the first stage
that removes it and never-paired states left fixed. -/
noncomputable def squareRootLowPrimeProcessedSeatMatchingInvolution :
    List ℕ → Finset SquareRootLowPrimeProcessedState →
      SquareRootLowPrimeProcessedState → SquareRootLowPrimeProcessedState
  | [], _S => id
  | p :: ps, S => fun x =>
      if x ∈ squareRootLowPrimeProcessedSeatPaired S p then
        squareRootLowPrimeProcessedSeatStepInvolution S p x
      else
        squareRootLowPrimeProcessedSeatMatchingInvolution ps
          (squareRootLowPrimeProcessedSeatFrontierStep S p) x

/-- The global chronology involution preserves the original finite carrier. -/
theorem squareRootLowPrimeProcessedSeatMatchingInvolution_mem
    (ps : List ℕ) (S : Finset SquareRootLowPrimeProcessedState)
    {x : SquareRootLowPrimeProcessedState} (hxS : x ∈ S) :
    squareRootLowPrimeProcessedSeatMatchingInvolution ps S x ∈ S := by
  induction ps generalizing S x with
  | nil => simpa [squareRootLowPrimeProcessedSeatMatchingInvolution] using hxS
  | cons p ps ih =>
      by_cases hxPaired : x ∈ squareRootLowPrimeProcessedSeatPaired S p
      · simp [squareRootLowPrimeProcessedSeatMatchingInvolution, hxPaired]
        exact squareRootLowPrimeProcessedSeatStepInvolution_mem S p hxS
      · have hxFrontier : x ∈ squareRootLowPrimeProcessedSeatFrontierStep S p :=
          Finset.mem_sdiff.mpr ⟨hxS, hxPaired⟩
        have hrec := ih
          (S := squareRootLowPrimeProcessedSeatFrontierStep S p) hxFrontier
        simp [squareRootLowPrimeProcessedSeatMatchingInvolution, hxPaired]
        exact squareRootLowPrimeProcessedSeatFrontierStep_subset' S p hrec

/-- The global chronology map is an involution. -/
theorem squareRootLowPrimeProcessedSeatMatchingInvolution_involutive
    (ps : List ℕ) (S : Finset SquareRootLowPrimeProcessedState)
    (hpos : ∀ p ∈ ps, 0 < p)
    {x : SquareRootLowPrimeProcessedState} (hxS : x ∈ S) :
    squareRootLowPrimeProcessedSeatMatchingInvolution ps S
        (squareRootLowPrimeProcessedSeatMatchingInvolution ps S x) = x := by
  induction ps generalizing S x with
  | nil => simp [squareRootLowPrimeProcessedSeatMatchingInvolution]
  | cons p ps ih =>
      have hp : 0 < p := hpos p (by simp)
      have hrest : ∀ q ∈ ps, 0 < q := by
        intro q hq
        exact hpos q (by simp [hq])
      by_cases hxPaired : x ∈ squareRootLowPrimeProcessedSeatPaired S p
      · let y := squareRootLowPrimeProcessedSeatStepInvolution S p x
        have hyS : y ∈ S :=
          squareRootLowPrimeProcessedSeatStepInvolution_mem S p
            (squareRootLowPrimeProcessedSeatPaired_subset S p hxPaired)
        have hyPaired : y ∈ squareRootLowPrimeProcessedSeatPaired S p := by
          have hfix := squareRootLowPrimeProcessedSeatStepInvolution_eq_self_iff S p
          by_contra hnot
          have hyFixed : squareRootLowPrimeProcessedSeatStepInvolution S p y = y :=
            hfix.mpr hnot
          have hback := squareRootLowPrimeProcessedSeatStepInvolution_involutive
            S hp x
          change squareRootLowPrimeProcessedSeatStepInvolution S p y = x at hback
          rw [hyFixed] at hback
          subst y
          exact hnot hxPaired
        simp [squareRootLowPrimeProcessedSeatMatchingInvolution, hxPaired,
          y, hyPaired,
          squareRootLowPrimeProcessedSeatStepInvolution_involutive S hp x]
      · have hxFrontier : x ∈ squareRootLowPrimeProcessedSeatFrontierStep S p :=
          Finset.mem_sdiff.mpr ⟨hxS, hxPaired⟩
        let y := squareRootLowPrimeProcessedSeatMatchingInvolution ps
          (squareRootLowPrimeProcessedSeatFrontierStep S p) x
        have hyFrontier : y ∈ squareRootLowPrimeProcessedSeatFrontierStep S p :=
          squareRootLowPrimeProcessedSeatMatchingInvolution_mem ps
            (squareRootLowPrimeProcessedSeatFrontierStep S p) hxFrontier
        have hyNotPaired : y ∉ squareRootLowPrimeProcessedSeatPaired S p :=
          (Finset.mem_sdiff.mp hyFrontier).2
        have hrec := ih
          (S := squareRootLowPrimeProcessedSeatFrontierStep S p)
          hrest hxFrontier
        simp [squareRootLowPrimeProcessedSeatMatchingInvolution, hxPaired,
          y, hyNotPaired] at hrec ⊢
        exact hrec

/-- Moved states of the global chronology still reverse signed weight. -/
theorem squareRootLowPrimeProcessedSeatMatchingInvolution_weight_neg
    (ps : List ℕ) (S : Finset SquareRootLowPrimeProcessedState)
    (hprime : ∀ p ∈ ps, p.Prime)
    {x : SquareRootLowPrimeProcessedState} (hxS : x ∈ S)
    (hne : squareRootLowPrimeProcessedSeatMatchingInvolution ps S x ≠ x) :
    squareRootLowPrimeProcessedSeatWeightReal
        (squareRootLowPrimeProcessedSeatMatchingInvolution ps S x) =
      -squareRootLowPrimeProcessedSeatWeightReal x := by
  induction ps generalizing S x with
  | nil => simp [squareRootLowPrimeProcessedSeatMatchingInvolution] at hne
  | cons p ps ih =>
      have hp : p.Prime := hprime p (by simp)
      have hrest : ∀ q ∈ ps, q.Prime := by
        intro q hq
        exact hprime q (by simp [hq])
      by_cases hxPaired : x ∈ squareRootLowPrimeProcessedSeatPaired S p
      · have hstepNe : squareRootLowPrimeProcessedSeatStepInvolution S p x ≠ x :=
          fun h =>
            (squareRootLowPrimeProcessedSeatStepInvolution_eq_self_iff S p).mp h
              hxPaired
        simp [squareRootLowPrimeProcessedSeatMatchingInvolution, hxPaired]
        exact squareRootLowPrimeProcessedSeatStepInvolution_weight_neg
          S hp x hstepNe
      · have hxFrontier : x ∈ squareRootLowPrimeProcessedSeatFrontierStep S p :=
          Finset.mem_sdiff.mpr ⟨hxS, hxPaired⟩
        simp [squareRootLowPrimeProcessedSeatMatchingInvolution, hxPaired] at hne ⊢
        exact ih
          (S := squareRootLowPrimeProcessedSeatFrontierStep S p)
          hrest hxFrontier hne

/-- **Othello stable-disc theorem for the prime chronology.**  The fixed states
of the global sign-reversing involution are exactly the terminal matching
frontier. -/
theorem signMatchingFixedPart_processedSeatMatching_eq_frontier
    (ps : List ℕ) (S : Finset SquareRootLowPrimeProcessedState)
    (hpos : ∀ p ∈ ps, 0 < p) :
    signMatchingFixedPart S
        (squareRootLowPrimeProcessedSeatMatchingInvolution ps S) =
      squareRootLowPrimeProcessedSeatMatchingFrontier ps S := by
  classical
  induction ps generalizing S with
  | nil =>
      ext x
      simp [signMatchingFixedPart,
        squareRootLowPrimeProcessedSeatMatchingInvolution,
        squareRootLowPrimeProcessedSeatMatchingFrontier]
  | cons p ps ih =>
      have hp : 0 < p := hpos p (by simp)
      have hrest : ∀ q ∈ ps, 0 < q := by
        intro q hq
        exact hpos q (by simp [hq])
      ext x
      simp only [mem_signMatchingFixedPart]
      by_cases hxS : x ∈ S
      · by_cases hxPaired : x ∈ squareRootLowPrimeProcessedSeatPaired S p
        · have hstepNe : squareRootLowPrimeProcessedSeatStepInvolution S p x ≠ x :=
            fun h =>
              (squareRootLowPrimeProcessedSeatStepInvolution_eq_self_iff S p).mp h
                hxPaired
          have hxNotFrontier :
              x ∉ squareRootLowPrimeProcessedSeatMatchingFrontier (p :: ps) S := by
            intro hx
            have hxStep := squareRootLowPrimeProcessedSeatMatchingFrontier_subset'
              ps (squareRootLowPrimeProcessedSeatFrontierStep S p) hx
            exact (Finset.mem_sdiff.mp hxStep).2 hxPaired
          simp [squareRootLowPrimeProcessedSeatMatchingInvolution, hxPaired,
            hstepNe, hxNotFrontier]
        · have hxStep : x ∈ squareRootLowPrimeProcessedSeatFrontierStep S p :=
            Finset.mem_sdiff.mpr ⟨hxS, hxPaired⟩
          have hih := Finset.ext_iff.mp
            (ih (S := squareRootLowPrimeProcessedSeatFrontierStep S p) hrest) x
          simp only [mem_signMatchingFixedPart] at hih
          simp [squareRootLowPrimeProcessedSeatMatchingInvolution, hxPaired,
            squareRootLowPrimeProcessedSeatMatchingFrontier, hxS, hih]
      · have hxNotFrontier :
          x ∉ squareRootLowPrimeProcessedSeatMatchingFrontier (p :: ps) S :=
          fun hx => hxS
            (squareRootLowPrimeProcessedSeatMatchingFrontier_subset'
              (p :: ps) S hx)
        have hxNotPaired : x ∉ squareRootLowPrimeProcessedSeatPaired S p :=
          fun hx => hxS (squareRootLowPrimeProcessedSeatPaired_subset S p hx)
        simp [squareRootLowPrimeProcessedSeatMatchingInvolution, hxNotPaired,
          hxS, hxNotFrontier]

end RHLean.Proof
