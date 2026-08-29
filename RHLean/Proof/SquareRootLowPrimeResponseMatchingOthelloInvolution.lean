import Mathlib
import RHLean.Proof.FiniteOthelloMatching
import RHLean.Proof.SquareRootLowPrimeMatchingFrontierSaturation

/-!
# Response-child chronology as one finite Othello involution

The existing sequential matching removes every available arithmetic edge
`n <-> p*n` at the first fresh-prime stage where the edge is present.  Remember
that first removal stage and complete the partial matching by fixed points.
The resulting self-map acts directly on the arithmetic child carrier `Finset ℕ`,
is involutive, reverses the Mobius sign on every moved state, and has fixed set
exactly the existing complete matching frontier.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Unique lower endpoint whose `p`-multiple is a known upper endpoint. -/
noncomputable def squareRootLowPrimeResponsePairPreimage
    (S : Finset ℕ) (p x : ℕ)
    (h : ∃ y ∈ squareRootLowPrimeResponsePairLower S p, p * y = x) : ℕ :=
  Classical.choose h

private theorem squareRootLowPrimeResponsePairPreimage_spec
    {S : Finset ℕ} {p x : ℕ}
    (h : ∃ y ∈ squareRootLowPrimeResponsePairLower S p, p * y = x) :
    squareRootLowPrimeResponsePairPreimage S p x h ∈
        squareRootLowPrimeResponsePairLower S p ∧
      p * squareRootLowPrimeResponsePairPreimage S p x h = x := by
  exact Classical.choose_spec h

/-- One prime-coordinate matching completed by fixed points. -/
noncomputable def squareRootLowPrimeResponseStepOthelloMate
    (S : Finset ℕ) (p : ℕ) : ℕ → ℕ := fun x =>
  if hx : x ∈ squareRootLowPrimeResponsePairLower S p then
    p * x
  else if hupper : ∃ y ∈ squareRootLowPrimeResponsePairLower S p, p * y = x then
    squareRootLowPrimeResponsePairPreimage S p x hupper
  else x

private theorem squareRootLowPrimeResponsePairUpper_iff_exists_lower
    {S : Finset ℕ} {p x : ℕ} :
    x ∈ squareRootLowPrimeResponsePairUpper S p ↔
      ∃ y ∈ squareRootLowPrimeResponsePairLower S p, p * y = x := by
  simp [squareRootLowPrimeResponsePairUpper]

/-- One-step mate preserves the ambient carrier. -/
theorem squareRootLowPrimeResponseStepOthelloMate_mem
    (S : Finset ℕ) (p : ℕ) {x : ℕ} (hxS : x ∈ S) :
    squareRootLowPrimeResponseStepOthelloMate S p x ∈ S := by
  classical
  by_cases hxLower : x ∈ squareRootLowPrimeResponsePairLower S p
  · simp [squareRootLowPrimeResponseStepOthelloMate, hxLower]
    exact (mem_squareRootLowPrimeResponsePairLower.mp hxLower).2.2
  · by_cases hupper : ∃ y ∈ squareRootLowPrimeResponsePairLower S p, p * y = x
    · have hspec := squareRootLowPrimeResponsePairPreimage_spec hupper
      simp [squareRootLowPrimeResponseStepOthelloMate, hxLower, hupper]
      exact (mem_squareRootLowPrimeResponsePairLower.mp hspec.1).1
    · simp [squareRootLowPrimeResponseStepOthelloMate, hxLower, hupper, hxS]

/-- One-step mate is involutive for a positive coordinate. -/
theorem squareRootLowPrimeResponseStepOthelloMate_involutive
    (S : Finset ℕ) {p : ℕ} (hp : 0 < p) (x : ℕ) :
    squareRootLowPrimeResponseStepOthelloMate S p
        (squareRootLowPrimeResponseStepOthelloMate S p x) = x := by
  classical
  by_cases hxLower : x ∈ squareRootLowPrimeResponsePairLower S p
  · let y := p * x
    have hyUpper : y ∈ squareRootLowPrimeResponsePairUpper S p := by
      unfold y squareRootLowPrimeResponsePairUpper
      exact Finset.mem_image.mpr ⟨x, hxLower, rfl⟩
    have hyNotLower : y ∉ squareRootLowPrimeResponsePairLower S p := by
      exact (Finset.disjoint_left.mp
        (squareRootLowPrimeResponsePairLower_disjoint_upper S p)) |>.2 hyUpper
    have hpre : ∃ z ∈ squareRootLowPrimeResponsePairLower S p, p * z = y :=
      ⟨x, hxLower, rfl⟩
    have hspec := squareRootLowPrimeResponsePairPreimage_spec hpre
    have hback : squareRootLowPrimeResponsePairPreimage S p y hpre = x :=
      Nat.mul_left_cancel hp hspec.2
    simp [squareRootLowPrimeResponseStepOthelloMate, hxLower, y,
      hyNotLower, hpre, hback]
  · by_cases hupper : ∃ y ∈ squareRootLowPrimeResponsePairLower S p, p * y = x
    · let y := squareRootLowPrimeResponsePairPreimage S p x hupper
      have hyLower : y ∈ squareRootLowPrimeResponsePairLower S p :=
        (squareRootLowPrimeResponsePairPreimage_spec hupper).1
      have hyExt : p * y = x :=
        (squareRootLowPrimeResponsePairPreimage_spec hupper).2
      simp [squareRootLowPrimeResponseStepOthelloMate, hxLower, hupper,
        y, hyLower, hyExt]
    · simp [squareRootLowPrimeResponseStepOthelloMate, hxLower, hupper]

/-- One-step fixed points are exactly states outside the paired population. -/
theorem squareRootLowPrimeResponseStepOthelloMate_eq_self_iff
    (S : Finset ℕ) {p : ℕ} (hp : 0 < p) {x : ℕ} :
    squareRootLowPrimeResponseStepOthelloMate S p x = x ↔
      x ∉ squareRootLowPrimeResponsePaired S p := by
  classical
  by_cases hxLower : x ∈ squareRootLowPrimeResponsePairLower S p
  · have hxPaired : x ∈ squareRootLowPrimeResponsePaired S p :=
      Finset.mem_union.mpr (Or.inl hxLower)
    have hxPos : 0 < x := by
      have hxS := (mem_squareRootLowPrimeResponsePairLower.mp hxLower).1
      by_contra hx0
      have hxZero : x = 0 := Nat.eq_zero_of_not_pos hx0
      subst x
      have hdiv : p ∣ 0 := dvd_zero p
      exact (mem_squareRootLowPrimeResponsePairLower.mp hxLower).2.1 hdiv
    have hne : p * x ≠ x := by
      intro heq
      have hpOne : p = 1 := Nat.eq_of_mul_eq_right hxPos heq
      omega
    simp [squareRootLowPrimeResponseStepOthelloMate, hxLower, hxPaired, hne]
  · by_cases hupper : ∃ y ∈ squareRootLowPrimeResponsePairLower S p, p * y = x
    · have hxUpper : x ∈ squareRootLowPrimeResponsePairUpper S p :=
        squareRootLowPrimeResponsePairUpper_iff_exists_lower.mpr hupper
      have hxPaired : x ∈ squareRootLowPrimeResponsePaired S p :=
        Finset.mem_union.mpr (Or.inr hxUpper)
      have hspec := squareRootLowPrimeResponsePairPreimage_spec hupper
      have hne : squareRootLowPrimeResponsePairPreimage S p x hupper ≠ x := by
        intro heq
        have hxLower' : x ∈ squareRootLowPrimeResponsePairLower S p := by
          simpa [heq] using hspec.1
        exact hxLower hxLower'
      simp [squareRootLowPrimeResponseStepOthelloMate, hxLower, hupper,
        hxPaired, hne]
    · have hxNotUpper : x ∉ squareRootLowPrimeResponsePairUpper S p := by
        simpa [squareRootLowPrimeResponsePairUpper_iff_exists_lower] using hupper
      have hxNotPaired : x ∉ squareRootLowPrimeResponsePaired S p := by
        intro hx
        rcases Finset.mem_union.mp hx with h | h
        · exact hxLower h
        · exact hxNotUpper h
      simp [squareRootLowPrimeResponseStepOthelloMate, hxLower, hupper,
        hxNotPaired]

/-- Every moved one-step state has opposite Mobius weight. -/
theorem squareRootLowPrimeResponseStepOthelloMate_weight_neg
    (S : Finset ℕ) {p : ℕ} (hp : p.Prime) (x : ℕ)
    (hne : squareRootLowPrimeResponseStepOthelloMate S p x ≠ x) :
    μ (squareRootLowPrimeResponseStepOthelloMate S p x) = -μ x := by
  classical
  by_cases hxLower : x ∈ squareRootLowPrimeResponsePairLower S p
  · simp [squareRootLowPrimeResponseStepOthelloMate, hxLower]
    exact moebius_prime_mul_eq_neg_of_not_dvd hp
      (mem_squareRootLowPrimeResponsePairLower.mp hxLower).2.1
  · by_cases hupper : ∃ y ∈ squareRootLowPrimeResponsePairLower S p, p * y = x
    · have hspec := squareRootLowPrimeResponsePairPreimage_spec hupper
      have hforward := moebius_prime_mul_eq_neg_of_not_dvd hp
        (mem_squareRootLowPrimeResponsePairLower.mp hspec.1).2.1
      rw [hspec.2] at hforward
      simp [squareRootLowPrimeResponseStepOthelloMate, hxLower, hupper]
      omega
    · simp [squareRootLowPrimeResponseStepOthelloMate, hxLower, hupper] at hne

/-- Complete chronological response matching as one self-map. -/
noncomputable def squareRootLowPrimeResponseMatchingOthelloMate :
    List ℕ → Finset ℕ → ℕ → ℕ
  | [], _S => id
  | p :: ps, S => fun x =>
      if x ∈ squareRootLowPrimeResponsePaired S p then
        squareRootLowPrimeResponseStepOthelloMate S p x
      else
        squareRootLowPrimeResponseMatchingOthelloMate ps
          (squareRootLowPrimeResponseFrontierStep S p) x

/-- The global chronology mate preserves the original finite carrier. -/
theorem squareRootLowPrimeResponseMatchingOthelloMate_mem
    (ps : List ℕ) (S : Finset ℕ) {x : ℕ} (hxS : x ∈ S) :
    squareRootLowPrimeResponseMatchingOthelloMate ps S x ∈ S := by
  induction ps generalizing S x with
  | nil => simpa [squareRootLowPrimeResponseMatchingOthelloMate] using hxS
  | cons p ps ih =>
      by_cases hxPaired : x ∈ squareRootLowPrimeResponsePaired S p
      · simp [squareRootLowPrimeResponseMatchingOthelloMate, hxPaired]
        exact squareRootLowPrimeResponseStepOthelloMate_mem S p hxS
      · have hxFrontier : x ∈ squareRootLowPrimeResponseFrontierStep S p :=
          Finset.mem_sdiff.mpr ⟨hxS, hxPaired⟩
        have hrec := ih (S := squareRootLowPrimeResponseFrontierStep S p) hxFrontier
        simp [squareRootLowPrimeResponseMatchingOthelloMate, hxPaired]
        exact squareRootLowPrimeResponseFrontierStep_subset S p hrec

/-- The global chronology mate is involutive. -/
theorem squareRootLowPrimeResponseMatchingOthelloMate_involutive
    (ps : List ℕ) (S : Finset ℕ)
    (hpos : ∀ p ∈ ps, 0 < p) {x : ℕ} (hxS : x ∈ S) :
    squareRootLowPrimeResponseMatchingOthelloMate ps S
        (squareRootLowPrimeResponseMatchingOthelloMate ps S x) = x := by
  induction ps generalizing S x with
  | nil => simp [squareRootLowPrimeResponseMatchingOthelloMate]
  | cons p ps ih =>
      have hp : 0 < p := hpos p (by simp)
      have hrest : ∀ q ∈ ps, 0 < q := by
        intro q hq
        exact hpos q (by simp [hq])
      by_cases hxPaired : x ∈ squareRootLowPrimeResponsePaired S p
      · let y := squareRootLowPrimeResponseStepOthelloMate S p x
        have hyS : y ∈ S :=
          squareRootLowPrimeResponseStepOthelloMate_mem S p
            (squareRootLowPrimeResponsePaired_subset S p hxPaired)
        have hyPaired : y ∈ squareRootLowPrimeResponsePaired S p := by
          have hfix := squareRootLowPrimeResponseStepOthelloMate_eq_self_iff S hp
          by_contra hnot
          have hyFixed : squareRootLowPrimeResponseStepOthelloMate S p y = y :=
            hfix.mpr hnot
          have hback := squareRootLowPrimeResponseStepOthelloMate_involutive S hp x
          change squareRootLowPrimeResponseStepOthelloMate S p y = x at hback
          rw [hyFixed] at hback
          subst y
          exact hnot hxPaired
        simp [squareRootLowPrimeResponseMatchingOthelloMate, hxPaired,
          y, hyPaired, squareRootLowPrimeResponseStepOthelloMate_involutive S hp x]
      · have hxFrontier : x ∈ squareRootLowPrimeResponseFrontierStep S p :=
          Finset.mem_sdiff.mpr ⟨hxS, hxPaired⟩
        let y := squareRootLowPrimeResponseMatchingOthelloMate ps
          (squareRootLowPrimeResponseFrontierStep S p) x
        have hyFrontier : y ∈ squareRootLowPrimeResponseFrontierStep S p :=
          squareRootLowPrimeResponseMatchingOthelloMate_mem ps
            (squareRootLowPrimeResponseFrontierStep S p) hxFrontier
        have hyNotPaired : y ∉ squareRootLowPrimeResponsePaired S p :=
          (Finset.mem_sdiff.mp hyFrontier).2
        have hrec := ih
          (S := squareRootLowPrimeResponseFrontierStep S p) hrest hxFrontier
        simp [squareRootLowPrimeResponseMatchingOthelloMate, hxPaired,
          y, hyNotPaired] at hrec ⊢
        exact hrec

/-- Moved states of the global chronology reverse Mobius weight. -/
theorem squareRootLowPrimeResponseMatchingOthelloMate_weight_neg
    (ps : List ℕ) (S : Finset ℕ)
    (hprime : ∀ p ∈ ps, p.Prime) {x : ℕ} (hxS : x ∈ S)
    (hne : squareRootLowPrimeResponseMatchingOthelloMate ps S x ≠ x) :
    μ (squareRootLowPrimeResponseMatchingOthelloMate ps S x) = -μ x := by
  induction ps generalizing S x with
  | nil => simp [squareRootLowPrimeResponseMatchingOthelloMate] at hne
  | cons p ps ih =>
      have hp : p.Prime := hprime p (by simp)
      have hrest : ∀ q ∈ ps, q.Prime := by
        intro q hq
        exact hprime q (by simp [hq])
      by_cases hxPaired : x ∈ squareRootLowPrimeResponsePaired S p
      · have hstepNe : squareRootLowPrimeResponseStepOthelloMate S p x ≠ x :=
          fun h =>
            (squareRootLowPrimeResponseStepOthelloMate_eq_self_iff S hp.pos).mp h
              hxPaired
        simp [squareRootLowPrimeResponseMatchingOthelloMate, hxPaired]
        exact squareRootLowPrimeResponseStepOthelloMate_weight_neg S hp x hstepNe
      · have hxFrontier : x ∈ squareRootLowPrimeResponseFrontierStep S p :=
          Finset.mem_sdiff.mpr ⟨hxS, hxPaired⟩
        simp [squareRootLowPrimeResponseMatchingOthelloMate, hxPaired] at hne ⊢
        exact ih (S := squareRootLowPrimeResponseFrontierStep S p)
          hrest hxFrontier hne

/-- The fixed states of the global chronology are exactly the iterated frontier. -/
theorem finiteOthelloStablePart_responseMatching_eq_frontier
    (ps : List ℕ) (S : Finset ℕ) (hpos : ∀ p ∈ ps, 0 < p) :
    finiteOthelloStablePart S
        (squareRootLowPrimeResponseMatchingOthelloMate ps S) =
      squareRootLowPrimeResponseMatchingFrontier ps S := by
  classical
  induction ps generalizing S with
  | nil =>
      ext x
      simp [finiteOthelloStablePart,
        squareRootLowPrimeResponseMatchingOthelloMate,
        squareRootLowPrimeResponseMatchingFrontier]
  | cons p ps ih =>
      have hp : 0 < p := hpos p (by simp)
      have hrest : ∀ q ∈ ps, 0 < q := by
        intro q hq
        exact hpos q (by simp [hq])
      ext x
      simp only [finiteOthelloStablePart, Finset.mem_filter]
      by_cases hxS : x ∈ S
      · by_cases hxPaired : x ∈ squareRootLowPrimeResponsePaired S p
        · have hstepNe : squareRootLowPrimeResponseStepOthelloMate S p x ≠ x :=
            fun h =>
              (squareRootLowPrimeResponseStepOthelloMate_eq_self_iff S hp).mp h
                hxPaired
          have hxNotFrontier :
              x ∉ squareRootLowPrimeResponseMatchingFrontier (p :: ps) S := by
            intro hx
            have hxStep := squareRootLowPrimeResponseMatchingFrontier_subset ps
              (squareRootLowPrimeResponseFrontierStep S p) hx
            exact (Finset.mem_sdiff.mp hxStep).2 hxPaired
          simp [squareRootLowPrimeResponseMatchingOthelloMate, hxPaired,
            hstepNe, hxNotFrontier]
        · have hxStep : x ∈ squareRootLowPrimeResponseFrontierStep S p :=
            Finset.mem_sdiff.mpr ⟨hxS, hxPaired⟩
          have hih := Finset.ext_iff.mp
            (ih (S := squareRootLowPrimeResponseFrontierStep S p) hrest) x
          simp only [finiteOthelloStablePart, Finset.mem_filter] at hih
          simp [squareRootLowPrimeResponseMatchingOthelloMate, hxPaired,
            squareRootLowPrimeResponseMatchingFrontier, hxS, hih]
      · have hxNotFrontier :
          x ∉ squareRootLowPrimeResponseMatchingFrontier (p :: ps) S :=
          fun hx => hxS
            (squareRootLowPrimeResponseMatchingFrontier_subset (p :: ps) S hx)
        have hxNotPaired : x ∉ squareRootLowPrimeResponsePaired S p :=
          fun hx => hxS (squareRootLowPrimeResponsePaired_subset S p hx)
        simp [squareRootLowPrimeResponseMatchingOthelloMate, hxNotPaired,
          hxS, hxNotFrontier]

end RHLean.Proof
