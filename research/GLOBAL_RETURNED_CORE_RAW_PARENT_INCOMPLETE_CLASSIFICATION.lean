import Mathlib
import «research.GLOBAL_RETURNED_CORE_RAW_PARENT_COMPLETED_GATE_SPLIT»
import «research.GLOBAL_RETURNED_CORE_DIRICHLET_INCIDENCE_CLOSURE»
import «research.GLOBAL_RETURNED_CORE_THRESHOLD_RECIPROCAL_INTERTWINING»

/-!
# Exact physical classification of incomplete raw-parent blocks

An occurring raw parent already supplies:

* a prime next owner `r > p`;
* r-free parent coordinates `(a,b)`;
* both parent coordinates inside the physical clock and in the same p-cell.

Therefore failure of the completed p/r block can occur only on one of six
remaining endpoint inequalities.  We group them into three chronological
classes:

1. **first-owner clipped:** `p*a` or `p*b` is already outside;
2. **next-owner clipped:** both p-children are admitted, but `r*a` or `r*b`
   leaves the clock;
3. **returned-next clipped:** the p- and r-children remain physical, but
   `p*(r*a)` or `p*(r*b)` leaves the clock.

These classes are not estimates.  The last two are immediately identified with
existing named boundary coordinates: a next-owner clipped child has zero
Dirichlet threshold incidence, while a returned-next clipped child is literally
a clipped p-base site after multiplication by r.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Original first-owner clipping on at least one raw-parent coordinate. -/
def LowOwnerRawParentFirstOwnerClipped
    (R p : ℕ) (parent : ℕ × ℕ) : Prop :=
  squareRootEndpoint R < p * parent.1 ∨
    squareRootEndpoint R < p * parent.2

/-- The p-children are admitted, but at least one moved r-child leaves the
physical clock. -/
def LowOwnerRawParentNextOwnerClipped
    (R p r : ℕ) (parent : ℕ × ℕ) : Prop :=
  p * parent.1 ≤ squareRootEndpoint R ∧
  p * parent.2 ≤ squareRootEndpoint R ∧
  (squareRootEndpoint R < r * parent.1 ∨
    squareRootEndpoint R < r * parent.2)

/-- Both p- and r-children are physical, but at least one returned p-after-r
corner leaves the clock. -/
def LowOwnerRawParentReturnedNextClipped
    (R p r : ℕ) (parent : ℕ × ℕ) : Prop :=
  p * parent.1 ≤ squareRootEndpoint R ∧
  p * parent.2 ≤ squareRootEndpoint R ∧
  r * parent.1 ≤ squareRootEndpoint R ∧
  r * parent.2 ≤ squareRootEndpoint R ∧
  (squareRootEndpoint R < p * (r * parent.1) ∨
    squareRootEndpoint R < p * (r * parent.2))

/-- **Exhaustive incomplete-block trichotomy.** -/
theorem lowOwnerFirstOwnerIncompletePolarizationRawParent_classification
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hp : p.Prime)
    (hparent : parent ∈
      lowOwnerFirstOwnerIncompletePolarizationRawParentSet R p sig r) :
    LowOwnerRawParentFirstOwnerClipped R p parent ∨
      LowOwnerRawParentNextOwnerClipped R p r parent ∨
      LowOwnerRawParentReturnedNextClipped R p r parent := by
  rcases Finset.mem_filter.mp hparent with ⟨hraw, hnotComplete⟩
  rcases lowOwnerFirstOwnerPolarizationRawParent_data hp hraw with
    ⟨hr, _hpr, haBase, hbBase, hra, hrb⟩
  have haCar := (Finset.mem_filter.mp haBase).1
  have hbCar := (Finset.mem_filter.mp hbBase).1
  have haIcc := (Finset.mem_filter.mp haCar).1
  have hbIcc := (Finset.mem_filter.mp hbCar).1
  have haX : parent.1 ≤ squareRootEndpoint R := (Finset.mem_Icc.mp haIcc).2
  have hbX : parent.2 ≤ squareRootEndpoint R := (Finset.mem_Icc.mp hbIcc).2
  by_cases hpa : p * parent.1 ≤ squareRootEndpoint R
  · by_cases hpb : p * parent.2 ≤ squareRootEndpoint R
    · by_cases hraX : r * parent.1 ≤ squareRootEndpoint R
      · by_cases hrbX : r * parent.2 ≤ squareRootEndpoint R
        · by_cases hpra : p * (r * parent.1) ≤ squareRootEndpoint R
          · by_cases hprb : p * (r * parent.2) ≤ squareRootEndpoint R
            · exfalso
              apply hnotComplete
              exact ⟨hr, hra, hrb,
                haX, hpa, hraX, hpra,
                hbX, hpb, hrbX, hprb⟩
            · exact Or.inr (Or.inr
                ⟨hpa, hpb, hraX, hrbX,
                  Or.inr (Nat.lt_of_not_ge hprb)⟩)
          · exact Or.inr (Or.inr
              ⟨hpa, hpb, hraX, hrbX,
                Or.inl (Nat.lt_of_not_ge hpra)⟩)
        · exact Or.inr (Or.inl
            ⟨hpa, hpb, Or.inr (Nat.lt_of_not_ge hrbX)⟩)
      · exact Or.inr (Or.inl
          ⟨hpa, hpb, Or.inl (Nat.lt_of_not_ge hraX)⟩)
    · exact Or.inl (Or.inr (Nat.lt_of_not_ge hpb))
  · exact Or.inl (Or.inl (Nat.lt_of_not_ge hpa))

/-- First-owner clipping is literally membership in the existing clipped base
fibre on the clipped coordinate. -/
theorem lowOwnerRawParentFirstOwnerClipped_mem_clippedBase
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hp : p.Prime)
    (hraw : parent ∈ lowOwnerFirstOwnerPolarizationRawParentSet R p sig r)
    (hclip : LowOwnerRawParentFirstOwnerClipped R p parent) :
    parent.1 ∈ lowOwnerFirstOwnerClippedBaseFiber R p sig ∨
      parent.2 ∈ lowOwnerFirstOwnerClippedBaseFiber R p sig := by
  rcases lowOwnerFirstOwnerPolarizationRawParent_data hp hraw with
    ⟨_hr, _hpr, haBase, hbBase, _hra, _hrb⟩
  rcases hclip with h | h
  · exact Or.inl (Finset.mem_filter.mpr ⟨haBase, h⟩)
  · exact Or.inr (Finset.mem_filter.mpr ⟨hbBase, h⟩)

/-- A next-owner clipped coordinate has exactly zero current-p incidence at the
moved child by Dirichlet extension. -/
theorem lowOwnerRawParentNextOwnerClipped_incidence_zero
    {R p r : ℕ} {parent : ℕ × ℕ}
    (hR : 2 ≤ R) (hp : p.Prime)
    (hclip : LowOwnerRawParentNextOwnerClipped R p r parent) :
    (squareRootEndpoint R < r * parent.1 ∧
        lowOwnerThresholdOwnerIncidenceWeight R p (r * parent.1) = 0) ∨
      (squareRootEndpoint R < r * parent.2 ∧
        lowOwnerThresholdOwnerIncidenceWeight R p (r * parent.2) = 0) := by
  rcases hclip.2.2 with h | h
  · exact Or.inl ⟨h,
      lowOwnerThresholdOwnerIncidenceWeight_eq_zero_of_next_clipped
        hR hp.one_le h⟩
  · exact Or.inr ⟨h,
      lowOwnerThresholdOwnerIncidenceWeight_eq_zero_of_next_clipped
        hR hp.one_le h⟩

/-- A returned-next clipped first coordinate is literally an existing clipped
p-base site after multiplication by r. -/
theorem lowOwnerRawParentReturnedNextClipped_left_mem_clippedBase
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hp : p.Prime)
    (hraw : parent ∈ lowOwnerFirstOwnerPolarizationRawParentSet R p sig r)
    (hclip : LowOwnerRawParentReturnedNextClipped R p r parent)
    (hleft : squareRootEndpoint R < p * (r * parent.1)) :
    r * parent.1 ∈ lowOwnerFirstOwnerClippedBaseFiber R p sig := by
  rcases lowOwnerFirstOwnerPolarizationRawParent_data hp hraw with
    ⟨hr, hpr, haBase, _hbBase, hra, _hrb⟩
  have haAdmitted : parent.1 ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig :=
    Finset.mem_filter.mpr ⟨haBase, hclip.1⟩
  exact lowOwnerFirstOwner_mul_larger_prime_mem_clippedBase
    hp hr hpr hra haAdmitted hclip.2.2.1 hleft

/-- Symmetric returned-next clipped identification on the second coordinate. -/
theorem lowOwnerRawParentReturnedNextClipped_right_mem_clippedBase
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hp : p.Prime)
    (hraw : parent ∈ lowOwnerFirstOwnerPolarizationRawParentSet R p sig r)
    (hclip : LowOwnerRawParentReturnedNextClipped R p r parent)
    (hright : squareRootEndpoint R < p * (r * parent.2)) :
    r * parent.2 ∈ lowOwnerFirstOwnerClippedBaseFiber R p sig := by
  rcases lowOwnerFirstOwnerPolarizationRawParent_data hp hraw with
    ⟨hr, hpr, _haBase, hbBase, _hra, hrb⟩
  have hbAdmitted : parent.2 ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig :=
    Finset.mem_filter.mpr ⟨hbBase, hclip.2.1⟩
  exact lowOwnerFirstOwner_mul_larger_prime_mem_clippedBase
    hp hr hpr hrb hbAdmitted hclip.2.2.2.1 hright

end RHLean.Proof
