import OAI.NumberTheory.DirichletL.Hecke.DetectorRawFiber

/-!
# A fixed heavy slot and the exact two-channel subset split

This file formalizes the structural part of claims `20261024-wheel-1` and
`20261024-referee-1` on the original OAI `Fiber`.  The source supply
inequality produces one fixed slot whose width is at least the average forced
by `7 / 37`.  The full powerset sum then splits exactly according to whether
that same slot is absent or present.

No analytic coefficient estimate, moment bound, principal payment, signed NNS
bound, seven-eighths theorem, canonical VF estimate, or RH statement is used or
proved here.
-/

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths
namespace HeckeDetectorRawFiber

variable {M : Ideal HeckeFamily.O}
  {H : Subgroup (HeckeFamily.O ⧸ M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

/-- The original OAI supply condition forces a single fixed slot carrying at
least `7 / (37 * #slots)` of the width. -/
theorem Fiber.exists_heavy_slot
    (F : Fiber M H Label Slot U a ε tstar T allowance i) :
    ∃ s ∈ F.slots,
      7 / (37 * (F.slots.card : ℝ)) ≤ F.widths s := by
  have hslots : F.slots.Nonempty := by
    by_contra h
    have hempty : F.slots = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp h
    have hsupply : (7 / 37 : ℝ) ≤ 0 := by
      simpa only [hempty, Finset.sum_empty] using F.supply
    norm_num at hsupply
  have hcardNat : 0 < F.slots.card := Finset.card_pos.mpr hslots
  have hcard : (0 : ℝ) < F.slots.card := by
    exact_mod_cast hcardNat
  have hcard0 : (F.slots.card : ℝ) ≠ 0 := ne_of_gt hcard
  by_contra h
  push Not at h
  have hlt :
      (∑ s ∈ F.slots, F.widths s) <
        ∑ _s ∈ F.slots, 7 / (37 * (F.slots.card : ℝ)) :=
    Finset.sum_lt_sum_of_nonempty hslots (fun s hs => h s hs)
  have hconst :
      (∑ _s ∈ F.slots, 7 / (37 * (F.slots.card : ℝ))) = 7 / 37 := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    field_simp [hcard0]
  rw [hconst] at hlt
  exact (not_lt_of_ge F.supply) hlt

/-- Every subset occurrence is retained exactly once when the complete
powerset is paired according to absence or presence of a fixed slot. -/
theorem sum_powerset_two_channel
    {A : Type*} [AddCommMonoid A] (slots : Finset Slot)
    (s : Slot) (hs : s ∈ slots) (f : Finset Slot → A) :
    (∑ J ∈ slots.powerset, f J) =
      ∑ J ∈ (slots.erase s).powerset, (f J + f (insert s J)) := by
  rw [← Finset.insert_erase hs,
    Finset.sum_powerset_insert (Finset.notMem_erase s slots),
    ← Finset.sum_add_distrib]
  simp

/-- Original-source combined form: one fixed heavy slot also indexes an exact
two-channel decomposition of every additive complete-subset sum. -/
theorem Fiber.exists_heavy_slot_with_two_channel_sum
    {A : Type*} [AddCommMonoid A]
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (f : Finset Slot → A) :
    ∃ s ∈ F.slots,
      7 / (37 * (F.slots.card : ℝ)) ≤ F.widths s ∧
      (∑ J ∈ F.slots.powerset, f J) =
        ∑ J ∈ (F.slots.erase s).powerset, (f J + f (insert s J)) := by
  obtain ⟨s, hs, hwidth⟩ := F.exists_heavy_slot
  exact ⟨s, hs, hwidth, sum_powerset_two_channel F.slots s hs f⟩

#print axioms Fiber.exists_heavy_slot
#print axioms sum_powerset_two_channel
#print axioms Fiber.exists_heavy_slot_with_two_channel_sum

end HeckeDetectorRawFiber
end SevenEighths
end
end OAI
