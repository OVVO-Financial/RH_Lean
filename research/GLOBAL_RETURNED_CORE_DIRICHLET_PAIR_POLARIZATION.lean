import Mathlib
import «research.GLOBAL_RETURNED_CORE_DIRICHLET_INCIDENCE_CLOSURE»
import «research.GLOBAL_RETURNED_CORE_SIGNED_CELL_TELESCOPE»

/-!
# Pointwise Dirichlet polarization of one first-owner cell

The clipped population must remain inside the cell polarization.  This file
makes that requirement pointwise.

For a p-free base parent `a` define

* `ell(a)` = the physical AMP site on `a`;
* `j_p(a)` = the p-child coefficient pulled back to `a`, using Dirichlet zero
  outside the physical clock;
* `d_p(a) = ell(a) - j_p(a)`.

The signed polarization atom is

  Pi_p(a,b) = d_p(a)d_p(b) - ell(a)ell(b) - j_p(a)j_p(b).

Summed over the full p-free base fibre it is exactly the signed cell telescope.
Pointwise:

* admitted/admitted: `Pi = -ell(a)j(b) - j(a)ell(b)`;
* clipped/admitted: only the mixed clipped/child term remains;
* clipped/clipped: `Pi = 0` exactly.

Thus no `C^2` term exists in the pair ledger.  Greatest-owner recursion may be
applied only to the admitted/admitted sector; clipped atoms remain in the
polarization until they become inherited reciprocal exits.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Physical base site in parent coordinates. -/
def lowOwnerFirstOwnerDirichletBaseSite (R a : ℕ) : ℝ :=
  lowOwnerZeroFrequencyMobiusSite R a

/-- Dirichlet p-child coefficient pulled back to the p-free parent coordinate.
It is automatically zero when the child leaves the physical clock. -/
def lowOwnerFirstOwnerDirichletReturnedChildSite
    (R p a : ℕ) : ℝ :=
  lowOwnerPhysicalDirichletWeight R (p * a) * realMoebiusStep a

/-- Dirichlet incidence signed site. -/
def lowOwnerFirstOwnerDirichletIncidenceSite
    (R p a : ℕ) : ℝ :=
  lowOwnerPhysicalDirichletIncidenceWeight R p a * realMoebiusStep a

/-- One pointwise signed polarization atom. -/
def lowOwnerFirstOwnerDirichletPolarizationAtom
    (R p : ℕ) (ab : ℕ × ℕ) : ℝ :=
  lowOwnerFirstOwnerDirichletIncidenceSite R p ab.1 *
      lowOwnerFirstOwnerDirichletIncidenceSite R p ab.2 -
    lowOwnerFirstOwnerDirichletBaseSite R ab.1 *
      lowOwnerFirstOwnerDirichletBaseSite R ab.2 -
    lowOwnerFirstOwnerDirichletReturnedChildSite R p ab.1 *
      lowOwnerFirstOwnerDirichletReturnedChildSite R p ab.2

/-- On every physical base parent, the incidence site is base minus returned
Dirichlet child. -/
theorem lowOwnerFirstOwnerDirichletIncidenceSite_eq_base_sub_returned
    {R p a : ℕ} {sig : Finset ℕ}
    (ha : a ∈ lowOwnerFirstOwnerBaseFiber R p sig) :
    lowOwnerFirstOwnerDirichletIncidenceSite R p a =
      lowOwnerFirstOwnerDirichletBaseSite R a -
        lowOwnerFirstOwnerDirichletReturnedChildSite R p a := by
  rcases Finset.mem_filter.mp ha with ⟨haCar, _hbase⟩
  rcases Finset.mem_filter.mp haCar with ⟨haIcc, _hmu⟩
  have haX : a ≤ squareRootEndpoint R := (Finset.mem_Icc.mp haIcc).2
  unfold lowOwnerFirstOwnerDirichletIncidenceSite
    lowOwnerFirstOwnerDirichletBaseSite
    lowOwnerFirstOwnerDirichletReturnedChildSite
    lowOwnerPhysicalDirichletIncidenceWeight
    lowOwnerZeroFrequencyMobiusSite
  rw [lowOwnerPhysicalDirichletWeight_eq_weight_of_le haX]
  ring

/-- Universal algebraic form of one polarization atom on the base fibre. -/
theorem lowOwnerFirstOwnerDirichletPolarizationAtom_eq_mixed
    {R p a b : ℕ} {sig : Finset ℕ}
    (ha : a ∈ lowOwnerFirstOwnerBaseFiber R p sig)
    (hb : b ∈ lowOwnerFirstOwnerBaseFiber R p sig) :
    lowOwnerFirstOwnerDirichletPolarizationAtom R p (a, b) =
      -(lowOwnerFirstOwnerDirichletBaseSite R a *
          lowOwnerFirstOwnerDirichletReturnedChildSite R p b) -
        lowOwnerFirstOwnerDirichletReturnedChildSite R p a *
          lowOwnerFirstOwnerDirichletBaseSite R b := by
  unfold lowOwnerFirstOwnerDirichletPolarizationAtom
  rw [lowOwnerFirstOwnerDirichletIncidenceSite_eq_base_sub_returned ha,
    lowOwnerFirstOwnerDirichletIncidenceSite_eq_base_sub_returned hb]
  ring

/-- On an admitted parent, the returned Dirichlet child is the existing `J`
site. -/
theorem lowOwnerFirstOwnerDirichletReturnedChildSite_eq_returned_of_admitted
    {R p a : ℕ} {sig : Finset ℕ}
    (ha : a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig) :
    lowOwnerFirstOwnerDirichletReturnedChildSite R p a =
      lowOwnerZeroFrequencyMobiusWeight R (p * a) * realMoebiusStep a := by
  rcases Finset.mem_filter.mp ha with ⟨_haBase, hpaX⟩
  unfold lowOwnerFirstOwnerDirichletReturnedChildSite
  rw [lowOwnerPhysicalDirichletWeight_eq_weight_of_le hpaX]

/-- On a clipped parent, the returned child site is exactly zero. -/
theorem lowOwnerFirstOwnerDirichletReturnedChildSite_eq_zero_of_clipped
    {R p a : ℕ} {sig : Finset ℕ}
    (ha : a ∈ lowOwnerFirstOwnerClippedBaseFiber R p sig) :
    lowOwnerFirstOwnerDirichletReturnedChildSite R p a = 0 := by
  have hclip := (Finset.mem_filter.mp ha).2
  unfold lowOwnerFirstOwnerDirichletReturnedChildSite
  rw [lowOwnerPhysicalDirichletWeight_eq_zero_of_lt hclip]
  ring

/-- **Clipped/clipped atoms vanish pointwise.**  This is the strongest form of
"no standalone C^2 estimate": there is no such atom in the signed ledger. -/
theorem lowOwnerFirstOwnerDirichletPolarizationAtom_eq_zero_of_both_clipped
    {R p a b : ℕ} {sig : Finset ℕ}
    (ha : a ∈ lowOwnerFirstOwnerClippedBaseFiber R p sig)
    (hb : b ∈ lowOwnerFirstOwnerClippedBaseFiber R p sig) :
    lowOwnerFirstOwnerDirichletPolarizationAtom R p (a, b) = 0 := by
  have haBase := (Finset.mem_filter.mp ha).1
  have hbBase := (Finset.mem_filter.mp hb).1
  rw [lowOwnerFirstOwnerDirichletPolarizationAtom_eq_mixed haBase hbBase,
    lowOwnerFirstOwnerDirichletReturnedChildSite_eq_zero_of_clipped ha,
    lowOwnerFirstOwnerDirichletReturnedChildSite_eq_zero_of_clipped hb]
  ring

/-- Clipped/admitted atoms are exactly one mixed polarization term. -/
theorem lowOwnerFirstOwnerDirichletPolarizationAtom_eq_clipped_left
    {R p a b : ℕ} {sig : Finset ℕ}
    (ha : a ∈ lowOwnerFirstOwnerClippedBaseFiber R p sig)
    (hb : b ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig) :
    lowOwnerFirstOwnerDirichletPolarizationAtom R p (a, b) =
      -lowOwnerFirstOwnerDirichletBaseSite R a *
        lowOwnerFirstOwnerDirichletReturnedChildSite R p b := by
  have haBase := (Finset.mem_filter.mp ha).1
  have hbBase := (Finset.mem_filter.mp hb).1
  rw [lowOwnerFirstOwnerDirichletPolarizationAtom_eq_mixed haBase hbBase,
    lowOwnerFirstOwnerDirichletReturnedChildSite_eq_zero_of_clipped ha]
  ring

/-- Admitted/clipped is the symmetric mixed polarization term. -/
theorem lowOwnerFirstOwnerDirichletPolarizationAtom_eq_clipped_right
    {R p a b : ℕ} {sig : Finset ℕ}
    (ha : a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig)
    (hb : b ∈ lowOwnerFirstOwnerClippedBaseFiber R p sig) :
    lowOwnerFirstOwnerDirichletPolarizationAtom R p (a, b) =
      -lowOwnerFirstOwnerDirichletReturnedChildSite R p a *
        lowOwnerFirstOwnerDirichletBaseSite R b := by
  have haBase := (Finset.mem_filter.mp ha).1
  have hbBase := (Finset.mem_filter.mp hb).1
  rw [lowOwnerFirstOwnerDirichletPolarizationAtom_eq_mixed haBase hbBase,
    lowOwnerFirstOwnerDirichletReturnedChildSite_eq_zero_of_clipped hb]
  ring

/-- The pulled-back Dirichlet child sites sum to the existing returned-child
parent amplitude. -/
theorem sum_lowOwnerFirstOwnerDirichletReturnedChildSite_eq_returned
    {R p : ℕ} {sig : Finset ℕ} :
    (∑ a ∈ lowOwnerFirstOwnerBaseFiber R p sig,
      lowOwnerFirstOwnerDirichletReturnedChildSite R p a) =
      lowOwnerFirstOwnerReturnedChildParentAmplitude R p sig := by
  rw [← lowOwnerFirstOwnerBaseFiber_partition_admitted_clipped R p sig,
    Finset.sum_union
      (lowOwnerFirstOwnerAdmittedBase_disjoint_clipped R p sig)]
  unfold lowOwnerFirstOwnerReturnedChildParentAmplitude
  have hadmitted :
      (∑ a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig,
        lowOwnerFirstOwnerDirichletReturnedChildSite R p a) =
      ∑ a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig,
        lowOwnerZeroFrequencyMobiusWeight R (p * a) * realMoebiusStep a := by
    apply Finset.sum_congr rfl
    intro a ha
    exact lowOwnerFirstOwnerDirichletReturnedChildSite_eq_returned_of_admitted ha
  have hclipped :
      (∑ a ∈ lowOwnerFirstOwnerClippedBaseFiber R p sig,
        lowOwnerFirstOwnerDirichletReturnedChildSite R p a) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    exact lowOwnerFirstOwnerDirichletReturnedChildSite_eq_zero_of_clipped ha
  rw [hadmitted, hclipped, add_zero]

/-- **Exact pair-level Dirichlet polarization.**  The full signed cell telescope
is the ordered sum of pointwise polarization atoms over the p-free base fibre. -/
theorem lowOwnerFirstOwnerSignedCellTelescope_eq_sum_dirichletPolarizationAtoms
    {R p : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    lowOwnerFirstOwnerSignedCellTelescope R p sig =
      ∑ ab ∈ (lowOwnerFirstOwnerBaseFiber R p sig).product
          (lowOwnerFirstOwnerBaseFiber R p sig),
        lowOwnerFirstOwnerDirichletPolarizationAtom R p ab := by
  have hD := lowOwnerFirstOwnerDirichletIncidenceAmplitude_eq_base_add_child
    (R := R) (p := p) (sig := sig) hp
  have hJ := sum_lowOwnerFirstOwnerDirichletReturnedChildSite_eq_returned
    (R := R) (p := p) (sig := sig)
  unfold lowOwnerFirstOwnerSignedCellTelescope
  rw [lowOwnerFirstOwnerCompensatedInterior_eq_admitted_sub_returned hp]
  rw [lowOwnerFirstOwnerBaseAmplitude_eq_admittedBase_add_clipped]
  have hcomp :
      lowOwnerFirstOwnerAdmittedBaseAmplitude R p sig -
          lowOwnerFirstOwnerReturnedChildParentAmplitude R p sig =
        lowOwnerFirstOwnerDirichletIncidenceAmplitude R p sig -
          lowOwnerFirstOwnerClippedAmplitude R p sig := by
    rw [lowOwnerFirstOwnerDirichletIncidenceAmplitude_eq_compensated_add_clipped hp]
    ring
  rw [hcomp]
  have hAtomSum :
      (∑ ab ∈ (lowOwnerFirstOwnerBaseFiber R p sig).product
          (lowOwnerFirstOwnerBaseFiber R p sig),
        lowOwnerFirstOwnerDirichletPolarizationAtom R p ab) =
      lowOwnerFirstOwnerDirichletIncidenceAmplitude R p sig ^ 2 -
        lowOwnerFirstOwnerBaseAmplitude R p sig ^ 2 -
        lowOwnerFirstOwnerReturnedChildParentAmplitude R p sig ^ 2 := by
    unfold lowOwnerFirstOwnerDirichletPolarizationAtom
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    have hinc :
        (∑ ab ∈ (lowOwnerFirstOwnerBaseFiber R p sig).product
            (lowOwnerFirstOwnerBaseFiber R p sig),
          lowOwnerFirstOwnerDirichletIncidenceSite R p ab.1 *
            lowOwnerFirstOwnerDirichletIncidenceSite R p ab.2) =
          lowOwnerFirstOwnerDirichletIncidenceAmplitude R p sig ^ 2 := by
      rw [Finset.sum_product]
      unfold lowOwnerFirstOwnerDirichletIncidenceAmplitude
        lowOwnerFirstOwnerDirichletIncidenceSite
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _ha
      rw [Finset.mul_sum]
      ring
    have hbase :
        (∑ ab ∈ (lowOwnerFirstOwnerBaseFiber R p sig).product
            (lowOwnerFirstOwnerBaseFiber R p sig),
          lowOwnerFirstOwnerDirichletBaseSite R ab.1 *
            lowOwnerFirstOwnerDirichletBaseSite R ab.2) =
          lowOwnerFirstOwnerBaseAmplitude R p sig ^ 2 := by
      rw [Finset.sum_product]
      unfold lowOwnerFirstOwnerBaseAmplitude
        lowOwnerFirstOwnerDirichletBaseSite
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _ha
      rw [Finset.mul_sum]
      ring
    have hchild :
        (∑ ab ∈ (lowOwnerFirstOwnerBaseFiber R p sig).product
            (lowOwnerFirstOwnerBaseFiber R p sig),
          lowOwnerFirstOwnerDirichletReturnedChildSite R p ab.1 *
            lowOwnerFirstOwnerDirichletReturnedChildSite R p ab.2) =
          lowOwnerFirstOwnerReturnedChildParentAmplitude R p sig ^ 2 := by
      rw [Finset.sum_product]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _ha
      rw [Finset.mul_sum]
      rw [hJ]
      ring
    rw [hinc, hbase, hchild]
  rw [hAtomSum]
  rw [hD, lowOwnerFirstOwnerChildAmplitude_eq_neg_returnedParent hp]
  rw [lowOwnerFirstOwnerBaseAmplitude_eq_admittedBase_add_clipped]
  ring

end RHLean.Proof
