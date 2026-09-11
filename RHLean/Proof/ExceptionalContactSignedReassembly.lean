import Mathlib
import RHLean.Proof.JointDaughterCrossEnergyAudit

/-!
# Signed exceptional contact reassembly

The exceptional `q^2` daughter must be reassembled before any norm is taken.
For `q = 5,7`, least-owner deletion does not destroy a full contact packet: every
deleted contact has a unique earlier exceptional owner.  This file packages that
fact as exact finite carrier and sum identities, valid for an arbitrary additive
weight.  It is the Buchstab-style owner reassignment needed before the existing
full-contact unit descents can be used.

No norm, absolute value, density estimate, or Mertens bound occurs here.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

/-- Restrict any physical cell carrier to a specified least square-prime owner. -/
def physicalCellsOwnedBy (S : Finset ℕ) (owner : ℕ) : Finset ℕ :=
  S.filter fun k => physicalLeastOddSquarePrime k = some owner

@[simp] theorem mem_physicalCellsOwnedBy
    {S : Finset ℕ} {owner k : ℕ} :
    k ∈ physicalCellsOwnedBy S owner ↔
      k ∈ S ∧ physicalLeastOddSquarePrime k = some owner := by
  simp [physicalCellsOwnedBy]

/-- Distinct least owners give disjoint subcarriers. -/
theorem physicalCellsOwnedBy_disjoint_of_ne
    (S : Finset ℕ) {a b : ℕ} (hab : a ≠ b) :
    Disjoint (physicalCellsOwnedBy S a) (physicalCellsOwnedBy S b) := by
  rw [Finset.disjoint_left]
  intro k hka hkb
  have ha := (mem_physicalCellsOwnedBy.mp hka).2
  have hb := (mem_physicalCellsOwnedBy.mp hkb).2
  have hs : (some a : Option ℕ) = some b := ha.symm.trans hb
  exact hab (Option.some.inj hs)

/-- **Owner-5 Buchstab partition.**  On any carrier consisting entirely of
`5^2` contacts, every cell is owned exactly by `5` or by the unique earlier
exceptional owner `3`. -/
theorem fiveHitCarrier_eq_ownerPartition
    (S : Finset ℕ)
    (h5 : ∀ k ∈ S, physicalSquarePrimeAtEdge k 5) :
    S = physicalCellsOwnedBy S 5 ∪ physicalCellsOwnedBy S 3 := by
  ext k
  simp only [Finset.mem_union, mem_physicalCellsOwnedBy]
  constructor
  · intro hk
    by_cases howner : physicalLeastOddSquarePrime k = some 5
    · exact Or.inl ⟨hk, howner⟩
    · have hthree := fiveContact_not_fiveOwner_implies_threeOwner (h5 k hk) howner
      exact Or.inr ⟨hk, hthree⟩
  · rintro (⟨hk, _⟩ | ⟨hk, _⟩) <;> exact hk

/-- The owner-5 partition preserves an arbitrary additive signed observable. -/
theorem fiveHitCarrier_sum_reassemble
    {A : Type*} [AddCommMonoid A]
    (S : Finset ℕ) (h5 : ∀ k ∈ S, physicalSquarePrimeAtEdge k 5)
    (f : ℕ → A) :
    (∑ k ∈ S, f k) =
      (∑ k ∈ physicalCellsOwnedBy S 5, f k) +
        ∑ k ∈ physicalCellsOwnedBy S 3, f k := by
  rw [fiveHitCarrier_eq_ownerPartition S h5,
    Finset.sum_union (physicalCellsOwnedBy_disjoint_of_ne S (by norm_num : 5 ≠ 3))]

/-- **Owner-7 Buchstab partition.**  On any carrier consisting entirely of
`7^2` contacts, every cell is owned exactly by `7`, `3`, or `5`.  The order is
lower triangular in the exceptional owners. -/
theorem sevenHitCarrier_eq_ownerPartition
    (S : Finset ℕ)
    (h7 : ∀ k ∈ S, physicalSquarePrimeAtEdge k 7) :
    S = (physicalCellsOwnedBy S 7 ∪ physicalCellsOwnedBy S 3) ∪
      physicalCellsOwnedBy S 5 := by
  ext k
  simp only [Finset.mem_union, mem_physicalCellsOwnedBy]
  constructor
  · intro hk
    by_cases howner : physicalLeastOddSquarePrime k = some 7
    · exact Or.inl (Or.inl ⟨hk, howner⟩)
    · rcases sevenContact_not_sevenOwner_implies_threeOrFiveOwner
        (h7 k hk) howner with hthree | hfive
      · exact Or.inl (Or.inr ⟨hk, hthree⟩)
      · exact Or.inr ⟨hk, hfive⟩
  · rintro ((⟨hk, _⟩ | ⟨hk, _⟩) | ⟨hk, _⟩) <;> exact hk

/-- The owner-7 partition preserves an arbitrary additive signed observable. -/
theorem sevenHitCarrier_sum_reassemble
    {A : Type*} [AddCommMonoid A]
    (S : Finset ℕ) (h7 : ∀ k ∈ S, physicalSquarePrimeAtEdge k 7)
    (f : ℕ → A) :
    (∑ k ∈ S, f k) =
      ((∑ k ∈ physicalCellsOwnedBy S 7, f k) +
        ∑ k ∈ physicalCellsOwnedBy S 3, f k) +
          ∑ k ∈ physicalCellsOwnedBy S 5, f k := by
  have h73 : Disjoint (physicalCellsOwnedBy S 7) (physicalCellsOwnedBy S 3) :=
    physicalCellsOwnedBy_disjoint_of_ne S (by norm_num : 7 ≠ 3)
  have hUnion5 :
      Disjoint (physicalCellsOwnedBy S 7 ∪ physicalCellsOwnedBy S 3)
        (physicalCellsOwnedBy S 5) := by
    rw [Finset.disjoint_union_left]
    exact ⟨
      physicalCellsOwnedBy_disjoint_of_ne S (by norm_num : 7 ≠ 5),
      physicalCellsOwnedBy_disjoint_of_ne S (by norm_num : 3 ≠ 5)⟩
  rw [sevenHitCarrier_eq_ownerPartition S h7,
    Finset.sum_union hUnion5, Finset.sum_union h73]

/-- The six physical `5^2` contact cells in period `L`. -/
def q5FullContactPeriodCells (L : ℕ) : Finset ℕ :=
  physicalTwentyFiveHitResidues.image fun r => 25 * L + r

/-- The six physical `7^2` contact cells in period `L`. -/
def q7FullContactPeriodCells (L : ℕ) : Finset ℕ :=
  physicalFortyNineHitResidues.image fun r => 49 * L + r

/-- Every cell in the displayed `5^2` period carrier is a genuine `5^2` contact. -/
theorem q5FullContactPeriodCells_hit
    {L k : ℕ} (hk : k ∈ q5FullContactPeriodCells L) :
    physicalSquarePrimeAtEdge k 5 := by
  rcases Finset.mem_image.mp hk with ⟨r, hr, rfl⟩
  rw [physicalSquarePrimeAtEdge_five_iff]
  have hrlt : r < 25 := by
    simp [physicalTwentyFiveHitResidues] at hr
    omega
  simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hrlt] using hr

/-- Every cell in the displayed `7^2` period carrier is a genuine `7^2` contact. -/
theorem q7FullContactPeriodCells_hit
    {L k : ℕ} (hk : k ∈ q7FullContactPeriodCells L) :
    physicalSquarePrimeAtEdge k 7 := by
  rcases Finset.mem_image.mp hk with ⟨r, hr, rfl⟩
  rw [physicalSquarePrimeAtEdge_seven_iff]
  have hrlt : r < 49 := by
    simp [physicalFortyNineHitResidues] at hr
    omega
  simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hrlt] using hr

/-- Reindex the existing owner-5 full-contact unit descent onto physical cells. -/
theorem q5_fullContactPeriodCells_q2Daughter_eq_lowerFourSlotCell (L : ℕ) :
    (∑ k ∈ q5FullContactPeriodCells L,
      physicalQ2DaughterCellIncrement 5 k) = fourSlotCellSum L := by
  unfold q5FullContactPeriodCells
  rw [Finset.sum_image]
  · exact q5_fullContactPeriod_q2Daughter_eq_lowerFourSlotCell L
  · intro a _ha b _hb hab
    omega

/-- Reindex the existing owner-7 full-contact unit descent onto physical cells. -/
theorem q7_fullContactPeriodCells_q2Daughter_eq_lowerFourSlotCell (L : ℕ) :
    (∑ k ∈ q7FullContactPeriodCells L,
      physicalQ2DaughterCellIncrement 7 k) = fourSlotCellSum L := by
  unfold q7FullContactPeriodCells
  rw [Finset.sum_image]
  · exact q7_fullContactPeriod_q2Daughter_eq_lowerFourSlotCell L
  · intro a _ha b _hb hab
    omega

/-- The `5^2` full daughter is restored exactly by adding the cells whose least
owner is `3`; only after this signed reassembly does the packet become the unit
lower four-cell. -/
theorem q5_completePeriod_q2Daughter_reassembled_by_owner (L : ℕ) :
    (∑ k ∈ physicalCellsOwnedBy (q5FullContactPeriodCells L) 5,
        physicalQ2DaughterCellIncrement 5 k) +
      (∑ k ∈ physicalCellsOwnedBy (q5FullContactPeriodCells L) 3,
        physicalQ2DaughterCellIncrement 5 k) =
      fourSlotCellSum L := by
  calc
    (∑ k ∈ physicalCellsOwnedBy (q5FullContactPeriodCells L) 5,
        physicalQ2DaughterCellIncrement 5 k) +
      (∑ k ∈ physicalCellsOwnedBy (q5FullContactPeriodCells L) 3,
        physicalQ2DaughterCellIncrement 5 k) =
        ∑ k ∈ q5FullContactPeriodCells L,
          physicalQ2DaughterCellIncrement 5 k :=
      (fiveHitCarrier_sum_reassemble (q5FullContactPeriodCells L)
        (fun k hk => q5FullContactPeriodCells_hit hk)
        (physicalQ2DaughterCellIncrement 5)).symm
    _ = fourSlotCellSum L :=
      q5_fullContactPeriodCells_q2Daughter_eq_lowerFourSlotCell L

/-- The `7^2` full daughter is restored exactly by adding its owner-3 and owner-5
overlap cells; the reassembled signed packet then descends with unit multiplicity. -/
theorem q7_completePeriod_q2Daughter_reassembled_by_owner (L : ℕ) :
    ((∑ k ∈ physicalCellsOwnedBy (q7FullContactPeriodCells L) 7,
        physicalQ2DaughterCellIncrement 7 k) +
      (∑ k ∈ physicalCellsOwnedBy (q7FullContactPeriodCells L) 3,
        physicalQ2DaughterCellIncrement 7 k)) +
      (∑ k ∈ physicalCellsOwnedBy (q7FullContactPeriodCells L) 5,
        physicalQ2DaughterCellIncrement 7 k) =
      fourSlotCellSum L := by
  calc
    ((∑ k ∈ physicalCellsOwnedBy (q7FullContactPeriodCells L) 7,
        physicalQ2DaughterCellIncrement 7 k) +
      (∑ k ∈ physicalCellsOwnedBy (q7FullContactPeriodCells L) 3,
        physicalQ2DaughterCellIncrement 7 k)) +
      (∑ k ∈ physicalCellsOwnedBy (q7FullContactPeriodCells L) 5,
        physicalQ2DaughterCellIncrement 7 k) =
        ∑ k ∈ q7FullContactPeriodCells L,
          physicalQ2DaughterCellIncrement 7 k :=
      (sevenHitCarrier_sum_reassemble (q7FullContactPeriodCells L)
        (fun k hk => q7FullContactPeriodCells_hit hk)
        (physicalQ2DaughterCellIncrement 7)).symm
    _ = fourSlotCellSum L :=
      q7_fullContactPeriodCells_q2Daughter_eq_lowerFourSlotCell L

end RHLean.Proof
