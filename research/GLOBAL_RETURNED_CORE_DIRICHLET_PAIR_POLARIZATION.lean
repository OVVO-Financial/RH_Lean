import Mathlib
import «research.GLOBAL_RETURNED_CORE_DIRICHLET_INCIDENCE_CLOSURE»
import «research.GLOBAL_RETURNED_CORE_SIGNED_OWNER_TELESCOPE»

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
Pointwise, clipped/clipped atoms vanish identically and mixed clipped/admitted
atoms are exactly the existing mixed polarization term.  There is no `C^2`
object to estimate.
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

/-- **Clipped/clipped atoms vanish pointwise.** -/
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
parent amplitude.  This is proved directly from the filter definition, with no
separate carrier-partition theorem. -/
theorem sum_lowOwnerFirstOwnerDirichletReturnedChildSite_eq_returned
    {R p : ℕ} {sig : Finset ℕ} :
    (∑ a ∈ lowOwnerFirstOwnerBaseFiber R p sig,
      lowOwnerFirstOwnerDirichletReturnedChildSite R p a) =
      lowOwnerFirstOwnerReturnedChildParentAmplitude R p sig := by
  unfold lowOwnerFirstOwnerReturnedChildParentAmplitude
    lowOwnerFirstOwnerAdmittedBaseFiber
    lowOwnerFirstOwnerDirichletReturnedChildSite
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _ha
  by_cases hpa : p * a ≤ squareRootEndpoint R
  · simp [hpa, lowOwnerPhysicalDirichletWeight]
  · have hclip : squareRootEndpoint R < p * a := Nat.lt_of_not_ge hpa
    simp [hpa, lowOwnerPhysicalDirichletWeight, hclip]

/-- Cartesian-product factorization for real pair products. -/
private theorem sum_product_mul_factor
    (s : Finset ℕ) (f g : ℕ → ℝ) :
    (∑ ab ∈ s.product s, f ab.1 * g ab.2) =
      (∑ a ∈ s, f a) * (∑ b ∈ s, g b) := by
  calc
    (∑ ab ∈ s.product s, f ab.1 * g ab.2) =
      ∑ a ∈ s, ∑ b ∈ s, f a * g b := by
        simpa only using
          (Finset.sum_product
            (s := s) (t := s)
            (f := fun ab : ℕ × ℕ => f ab.1 * g ab.2))
    _ = ∑ a ∈ s, f a * (∑ b ∈ s, g b) := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [Finset.mul_sum]
    _ = (∑ a ∈ s, f a) * (∑ b ∈ s, g b) := by
      rw [Finset.sum_mul]

/-- Sum of incidence sites is the existing Dirichlet incidence amplitude. -/
theorem sum_lowOwnerFirstOwnerDirichletIncidenceSite_eq_amplitude
    (R p : ℕ) (sig : Finset ℕ) :
    (∑ a ∈ lowOwnerFirstOwnerBaseFiber R p sig,
      lowOwnerFirstOwnerDirichletIncidenceSite R p a) =
      lowOwnerFirstOwnerDirichletIncidenceAmplitude R p sig := by
  rfl

/-- Sum of base sites is the existing base amplitude. -/
theorem sum_lowOwnerFirstOwnerDirichletBaseSite_eq_amplitude
    (R p : ℕ) (sig : Finset ℕ) :
    (∑ a ∈ lowOwnerFirstOwnerBaseFiber R p sig,
      lowOwnerFirstOwnerDirichletBaseSite R a) =
      lowOwnerFirstOwnerBaseAmplitude R p sig := by
  rfl

/-- **Exact pair-level Dirichlet polarization.**  The full signed cell telescope
is the ordered sum of pointwise polarization atoms over the p-free base fibre. -/
theorem lowOwnerFirstOwnerSignedCellTelescope_eq_sum_dirichletPolarizationAtoms
    {R p : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    lowOwnerFirstOwnerSignedCellTelescope R p sig =
      ∑ ab ∈ (lowOwnerFirstOwnerBaseFiber R p sig).product
          (lowOwnerFirstOwnerBaseFiber R p sig),
        lowOwnerFirstOwnerDirichletPolarizationAtom R p ab := by
  let s := lowOwnerFirstOwnerBaseFiber R p sig
  have hinc := sum_lowOwnerFirstOwnerDirichletIncidenceSite_eq_amplitude R p sig
  have hbase := sum_lowOwnerFirstOwnerDirichletBaseSite_eq_amplitude R p sig
  have hchild := sum_lowOwnerFirstOwnerDirichletReturnedChildSite_eq_returned
    (R := R) (p := p) (sig := sig)
  have hatoms :
      (∑ ab ∈ s.product s,
        lowOwnerFirstOwnerDirichletPolarizationAtom R p ab) =
      lowOwnerFirstOwnerDirichletIncidenceAmplitude R p sig ^ 2 -
        lowOwnerFirstOwnerBaseAmplitude R p sig ^ 2 -
        lowOwnerFirstOwnerReturnedChildParentAmplitude R p sig ^ 2 := by
    unfold lowOwnerFirstOwnerDirichletPolarizationAtom
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    rw [sum_product_mul_factor, sum_product_mul_factor, sum_product_mul_factor]
    dsimp [s] at hinc hbase hchild ⊢
    rw [hinc, hbase, hchild]
    ring
  have htel := two_mul_lowOwnerFirstOwnerCellGram_eq_completeTelescope_sub_clippedCross
    (R := R) (p := p) (sig := sig) hp
  have hdir := two_mul_lowOwnerFirstOwnerCellGram_eq_dirichletIncidence_sq_sub_branches
    (R := R) (p := p) (sig := sig) hp
  have hchildAmp := lowOwnerFirstOwnerChildAmplitude_eq_neg_returnedParent
    (R := R) (p := p) (sig := sig) hp
  have htelEq :
      lowOwnerFirstOwnerSignedCellTelescope R p sig =
        2 * lowOwnerFirstOwnerCellGram R p sig := by
    unfold lowOwnerFirstOwnerSignedCellTelescope
    exact htel.symm
  rw [htelEq, hdir, hchildAmp]
  rw [show (∑ ab ∈ (lowOwnerFirstOwnerBaseFiber R p sig).product
      (lowOwnerFirstOwnerBaseFiber R p sig),
        lowOwnerFirstOwnerDirichletPolarizationAtom R p ab) =
      lowOwnerFirstOwnerDirichletIncidenceAmplitude R p sig ^ 2 -
        lowOwnerFirstOwnerBaseAmplitude R p sig ^ 2 -
        lowOwnerFirstOwnerReturnedChildParentAmplitude R p sig ^ 2 by
    simpa [s] using hatoms]
  ring

end RHLean.Proof
