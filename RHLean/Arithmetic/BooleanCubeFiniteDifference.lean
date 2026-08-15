import Mathlib
import RHLean.Arithmetic.TruncatedBooleanCube

open scoped BigOperators

noncomputable section

namespace RHLean.Arithmetic

/-!
# Exact Boolean-coordinate finite differences

A sign-reversing Boolean coordinate does not require the support predicate to be
downward closed.  Pairing the two halves of the cube at one pivot `a` writes the
complete alternating mass as the first discrete difference of the support
indicator.  Pairing a second pivot `b` writes it as the exact four-point second
difference

```text
I(u) - I(a+u) - I(b+u) + I(a+b+u).
```

This is the direct finite Walsh derivative behind the survivor prime-face
cancellation.  It is purely algebraic and makes no Markov, uniformity, or
probabilistic assumption.
-/

/-- Integer indicator of an arbitrary Boolean-face predicate. -/
noncomputable def booleanPredicateIndicator
    {α : Type*} (P : Finset α → Prop) (u : Finset α) : ℤ := by
  classical
  exact if P u then 1 else 0

/-- First discrete difference in one Boolean coordinate. -/
def booleanPivotDifference
    {α : Type*} [DecidableEq α]
    (a : α) (P : Finset α → Prop) (u : Finset α) : ℤ :=
  booleanPredicateIndicator P u -
    booleanPredicateIndicator P (insert a u)

/-- Four-point second discrete difference in two Boolean coordinates. -/
def booleanTwoPivotDifference
    {α : Type*} [DecidableEq α]
    (a b : α) (P : Finset α → Prop) (u : Finset α) : ℤ :=
  booleanPredicateIndicator P u -
    booleanPredicateIndicator P (insert a u) -
    booleanPredicateIndicator P (insert b u) +
    booleanPredicateIndicator P (insert a (insert b u))

/-- **One-coordinate exact finite difference.**  The alternating mass of an
arbitrary support is the signed first difference across any selected cube
coordinate. -/
theorem truncatedCubeAlternatingSum_eq_pivotDifference
    {α : Type*} [DecidableEq α]
    {s : Finset α} {a : α} (P : Finset α → Prop)
    (ha : a ∈ s) :
    truncatedCubeAlternatingSum s P =
      ∑ u ∈ (s.erase a).powerset,
        booleanCubeSign u * booleanPivotDifference a P u := by
  classical
  have hdecomp : s = insert a (s.erase a) :=
    (Finset.insert_erase ha).symm
  unfold truncatedCubeAlternatingSum
  rw [hdecomp]
  rw [Finset.sum_powerset_insert (Finset.notMem_erase a s)]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  have hau : a ∉ u :=
    Finset.notMem_of_mem_powerset_of_notMem
      hu (Finset.notMem_erase a s)
  have hsign :
      booleanCubeSign (insert a u) = -booleanCubeSign u := by
    simp [booleanCubeSign, Finset.card_insert_of_notMem, hau, pow_succ]
  unfold booleanPivotDifference booleanPredicateIndicator
  rw [hsign]
  by_cases h0 : P u <;> by_cases h1 : P (insert a u) <;>
    simp [h0, h1] <;> ring

/-- **Two-coordinate exact finite difference.**  Two independent sign toggles
reduce the arbitrary Boolean-supported alternating mass to the four-point
second derivative on faces omitting both pivots. -/
theorem truncatedCubeAlternatingSum_eq_twoPivotDifference
    {α : Type*} [DecidableEq α]
    {s : Finset α} {a b : α} (P : Finset α → Prop)
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) :
    truncatedCubeAlternatingSum s P =
      ∑ u ∈ ((s.erase a).erase b).powerset,
        booleanCubeSign u * booleanTwoPivotDifference a b P u := by
  classical
  rw [truncatedCubeAlternatingSum_eq_pivotDifference P ha]
  have hba : b ∈ s.erase a :=
    Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩
  have hdecomp : s.erase a = insert b ((s.erase a).erase b) :=
    (Finset.insert_erase hba).symm
  rw [hdecomp]
  rw [Finset.sum_powerset_insert (Finset.notMem_erase b (s.erase a))]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  have hbu : b ∉ u :=
    Finset.notMem_of_mem_powerset_of_notMem
      hu (Finset.notMem_erase b (s.erase a))
  have hsign :
      booleanCubeSign (insert b u) = -booleanCubeSign u := by
    simp [booleanCubeSign, Finset.card_insert_of_notMem, hbu, pow_succ]
  rw [hsign]
  unfold booleanPivotDifference booleanTwoPivotDifference
  ring

/-- The two-pivot difference is symmetric in the selected coordinates on faces
that omit both pivots. -/
theorem booleanTwoPivotDifference_comm
    {α : Type*} [DecidableEq α]
    (a b : α) (P : Finset α → Prop) (u : Finset α)
    (hau : a ∉ u) (hbu : b ∉ u) :
    booleanTwoPivotDifference a b P u =
      booleanTwoPivotDifference b a P u := by
  unfold booleanTwoPivotDifference
  have hins : insert a (insert b u) = insert b (insert a u) := by
    ext x
    simp [or_left_comm, or_assoc]
  rw [hins]
  ring

end RHLean.Arithmetic
