import Mathlib
import RHLean.Arithmetic.BooleanCubeCancellation

/-!
# Least-coordinate toggle duality

This is the finite sign-reversing involution behind the largest/smallest-prime
duality used in the Othello endgame.

Fix one distinguished coordinate `a` in a finite set `S`.  Give every nonempty
face the Boolean sign `(-1)^|t|`.  Suppose a payload `g` is unchanged when `a`
is inserted into any nonempty face which omits `a`.  Splitting the powerset at
`a` pairs every nonempty old face with its `a`-child with opposite signs.  The
empty old face has no payload, while its child `{a}` survives.  Therefore the
whole nonempty alternating cube is exactly `-g {a}`.

For prime-factor faces and `a` the least prime factor, a payload depending only
on the largest prime is insertion-invariant away from the singleton.  This is
the finite core of Alladi's largest/smallest-prime duality: an arbitrarily large
history fibre has one signed last move.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Alternating payload on the nonempty faces of a finite coordinate set. -/
def finiteNonemptyFaceAlternatingSum
    {α A : Type*} [DecidableEq α] [AddCommGroup A]
    (S : Finset α) (g : Finset α → A) : A :=
  ∑ t ∈ S.powerset, if t.Nonempty then booleanCubeSign t • g t else 0

/-- **Least-toggle singleton survival.**  If inserting the distinguished
coordinate preserves the payload on every nonempty face omitting it, then all
non-singleton histories cancel and only the singleton `{a}` remains. -/
theorem finiteNonemptyFaceAlternatingSum_eq_neg_singleton
    {α A : Type*} [DecidableEq α] [AddCommGroup A]
    (S : Finset α) (a : α) (g : Finset α → A)
    (ha : a ∈ S)
    (hinvariant : ∀ u ∈ (S.erase a).powerset, u.Nonempty →
      g (insert a u) = g u) :
    finiteNonemptyFaceAlternatingSum S g = -g {a} := by
  classical
  have hdecomp : S = insert a (S.erase a) := (Finset.insert_erase ha).symm
  have haErase : a ∉ S.erase a := Finset.notMem_erase a S
  unfold finiteNonemptyFaceAlternatingSum
  rw [hdecomp, Finset.sum_powerset_insert haErase]
  rw [← Finset.sum_add_distrib]
  calc
    (∑ u ∈ (S.erase a).powerset,
      (if u.Nonempty then booleanCubeSign u • g u else 0) +
        (if (insert a u).Nonempty then
          booleanCubeSign (insert a u) • g (insert a u) else 0)) =
      ∑ u ∈ (S.erase a).powerset,
        if u = ∅ then -g {a} else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      have hau : a ∉ u :=
        Finset.notMem_of_mem_powerset_of_notMem hu haErase
      have hinsNonempty : (insert a u).Nonempty := ⟨a, Finset.mem_insert_self _ _⟩
      by_cases huEmpty : u = ∅
      · subst u
        simp [booleanCubeSign]
      · have huNonempty : u.Nonempty := Finset.nonempty_iff_ne_empty.mpr huEmpty
        have hginv := hinvariant u hu huNonempty
        have hsign : booleanCubeSign (insert a u) = -booleanCubeSign u := by
          unfold booleanCubeSign
          rw [Finset.card_insert_of_notMem hau, pow_succ]
          ring
        simp only [huNonempty, hinsNonempty, if_true]
        rw [hginv, hsign]
        simp
    _ = -g {a} := by
      have hEmptyMem : (∅ : Finset α) ∈ (S.erase a).powerset := by simp
      simp [hEmptyMem]

end RHLean.Proof
