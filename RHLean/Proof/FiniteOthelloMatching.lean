import Mathlib

/-!
# Finite Othello parity for sign-reversing matchings

The useful Othello principle is not a heuristic about local flips.  It is a
finite parity statement about a region after all forced moves have been played.

A matching involution on a finite signed region pairs every moving state with a
state of opposite weight.  If at most one stable state remains, then the entire
region has signed mass of absolute value at most one.  This is the exact
combinatorial statement used after an alternating-path / gradient-path reversal:
the long path itself contributes zero in pairs and only its last stable endpoint
can survive.

No arithmetic, asymptotic estimate, or RH input appears here.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- States moved by a candidate matching involution. -/
def finiteOthelloMovingPart {α : Type*} [DecidableEq α]
    (S : Finset α) (mate : α → α) : Finset α :=
  S.filter fun x => mate x ≠ x

/-- Stable states of a candidate matching involution. -/
def finiteOthelloStablePart {α : Type*} [DecidableEq α]
    (S : Finset α) (mate : α → α) : Finset α :=
  S.filter fun x => mate x = x

/-- Moving and stable states are disjoint. -/
theorem finiteOthelloMovingPart_disjoint_stable
    {α : Type*} [DecidableEq α]
    (S : Finset α) (mate : α → α) :
    Disjoint (finiteOthelloMovingPart S mate)
      (finiteOthelloStablePart S mate) := by
  classical
  rw [Finset.disjoint_left]
  intro x hxMove hxStable
  exact (Finset.mem_filter.mp hxMove).2
    (Finset.mem_filter.mp hxStable).2

/-- Every state is either moved or stable. -/
theorem finiteOthelloMovingPart_union_stable
    {α : Type*} [DecidableEq α]
    (S : Finset α) (mate : α → α) :
    finiteOthelloMovingPart S mate ∪ finiteOthelloStablePart S mate = S := by
  classical
  ext x
  constructor
  · intro hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (Finset.mem_filter.mp hx).1
    · exact (Finset.mem_filter.mp hx).1
  · intro hx
    by_cases hfix : mate x = x
    · exact Finset.mem_union.mpr <| Or.inr <|
        Finset.mem_filter.mpr ⟨hx, hfix⟩
    · exact Finset.mem_union.mpr <| Or.inl <|
        Finset.mem_filter.mpr ⟨hx, hfix⟩

/-- Exact cancellation of the moving part of an involutive sign-reversing
matching. -/
theorem sum_finiteOthelloMovingPart_eq_zero
    {α A : Type*} [DecidableEq α] [AddCommGroup A]
    (S : Finset α) (mate : α → α) (w : α → A)
    (hmem : ∀ x ∈ S, mate x ∈ S)
    (hinv : ∀ x ∈ S, mate (mate x) = x)
    (hneg : ∀ x ∈ S, mate x ≠ x → w (mate x) = -w x) :
    (∑ x ∈ finiteOthelloMovingPart S mate, w x) = 0 := by
  classical
  exact Finset.sum_involution
    (s := finiteOthelloMovingPart S mate) (f := w)
    (fun x _hx => mate x)
    (fun x hx => by
      have hxData := Finset.mem_filter.mp hx
      rw [hneg x hxData.1 hxData.2]
      simp)
    (fun x hx _hw => (Finset.mem_filter.mp hx).2)
    (fun x hx => by
      have hxData := Finset.mem_filter.mp hx
      apply Finset.mem_filter.mpr
      refine ⟨hmem x hxData.1, ?_⟩
      intro hfix
      have hinvX := hinv x hxData.1
      have hEq : mate x = x := by
        calc
          mate x = mate (mate x) := hfix.symm
          _ = x := hinvX
      exact hxData.2 hEq)
    (fun x hx => hinv x (Finset.mem_filter.mp hx).1)

/-- The signed mass of the whole region is exactly the mass of its stable
states. -/
theorem sum_finiteOthelloRegion_eq_stable
    {α A : Type*} [DecidableEq α] [AddCommGroup A]
    (S : Finset α) (mate : α → α) (w : α → A)
    (hmem : ∀ x ∈ S, mate x ∈ S)
    (hinv : ∀ x ∈ S, mate (mate x) = x)
    (hneg : ∀ x ∈ S, mate x ≠ x → w (mate x) = -w x) :
    (∑ x ∈ S, w x) =
      ∑ x ∈ finiteOthelloStablePart S mate, w x := by
  classical
  have hpart := finiteOthelloMovingPart_union_stable S mate
  have hdisj := finiteOthelloMovingPart_disjoint_stable S mate
  calc
    (∑ x ∈ S, w x) =
        ∑ x ∈ finiteOthelloMovingPart S mate ∪
          finiteOthelloStablePart S mate, w x := by rw [hpart]
    _ = (∑ x ∈ finiteOthelloMovingPart S mate, w x) +
          ∑ x ∈ finiteOthelloStablePart S mate, w x := by
          rw [Finset.sum_union hdisj]
    _ = ∑ x ∈ finiteOthelloStablePart S mate, w x := by
          rw [sum_finiteOthelloMovingPart_eq_zero S mate w hmem hinv hneg]
          simp

/-- **Othello last-move bound.**  If an alternating-path reversal leaves at
most one stable unit-weight state in a finite region, the whole signed region
has absolute mass at most one. -/
theorem abs_sum_finiteOthelloRegion_le_one
    {α : Type*} [DecidableEq α]
    (S : Finset α) (mate : α → α) (w : α → ℤ)
    (hmem : ∀ x ∈ S, mate x ∈ S)
    (hinv : ∀ x ∈ S, mate (mate x) = x)
    (hneg : ∀ x ∈ S, mate x ≠ x → w (mate x) = -w x)
    (hunit : ∀ x ∈ finiteOthelloStablePart S mate, |w x| ≤ 1)
    (hstable : (finiteOthelloStablePart S mate).card ≤ 1) :
    |∑ x ∈ S, w x| ≤ 1 := by
  rw [sum_finiteOthelloRegion_eq_stable S mate w hmem hinv hneg]
  calc
    |∑ x ∈ finiteOthelloStablePart S mate, w x| ≤
        ∑ x ∈ finiteOthelloStablePart S mate, |w x| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x ∈ finiteOthelloStablePart S mate, (1 : ℤ) := by
          apply Finset.sum_le_sum
          intro x hx
          exact hunit x hx
    _ = ((finiteOthelloStablePart S mate).card : ℤ) := by simp
    _ ≤ 1 := by exact_mod_cast hstable

end RHLean.Proof
