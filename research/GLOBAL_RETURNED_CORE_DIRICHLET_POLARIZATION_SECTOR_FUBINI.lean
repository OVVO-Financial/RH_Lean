import Mathlib
import «research.GLOBAL_RETURNED_CORE_DIRICHLET_PAIR_POLARIZATION»

/-!
# Sector Fubini for the Dirichlet polarization

The signed cell telescope has exactly two live pair sectors.

* admitted/admitted: the only sector eligible for greatest-owner recursion;
* clipped/admitted plus admitted/clipped: the existing mixed clipped
  polarization.

The clipped/clipped sector vanishes pointwise by the preceding file.  This file
computes the two live sectors directly and proves

  SignedCellTelescope = AdmittedPolarizationMass + ClippedMixedPolarizationMass.

Moreover the mixed clipped mass is exactly `-2 C J`.  It is not squared and is
not entered into the recursive `2/9` budget.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Admitted/admitted part of the pair-level polarization. -/
def lowOwnerFirstOwnerAdmittedPolarizationMass
    (R p : ℕ) (sig : Finset ℕ) : ℝ :=
  ∑ ab ∈ (lowOwnerFirstOwnerAdmittedBaseFiber R p sig).product
      (lowOwnerFirstOwnerAdmittedBaseFiber R p sig),
    lowOwnerFirstOwnerDirichletPolarizationAtom R p ab

/-- The two mixed sectors with exactly one clipped parent. -/
def lowOwnerFirstOwnerClippedMixedPolarizationMass
    (R p : ℕ) (sig : Finset ℕ) : ℝ :=
  (∑ ab ∈ (lowOwnerFirstOwnerClippedBaseFiber R p sig).product
      (lowOwnerFirstOwnerAdmittedBaseFiber R p sig),
    lowOwnerFirstOwnerDirichletPolarizationAtom R p ab) +
  (∑ ab ∈ (lowOwnerFirstOwnerAdmittedBaseFiber R p sig).product
      (lowOwnerFirstOwnerClippedBaseFiber R p sig),
    lowOwnerFirstOwnerDirichletPolarizationAtom R p ab)

private theorem sum_product_mul_factor_sector
    (s t : Finset ℕ) (f g : ℕ → ℝ) :
    (∑ ab ∈ s.product t, f ab.1 * g ab.2) =
      (∑ a ∈ s, f a) * (∑ b ∈ t, g b) := by
  calc
    (∑ ab ∈ s.product t, f ab.1 * g ab.2) =
      ∑ a ∈ s, ∑ b ∈ t, f a * g b := by
        simpa only using
          (Finset.sum_product
            (s := s) (t := t)
            (f := fun ab : ℕ × ℕ => f ab.1 * g ab.2))
    _ = ∑ a ∈ s, f a * (∑ b ∈ t, g b) := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [Finset.mul_sum]
    _ = (∑ a ∈ s, f a) * (∑ b ∈ t, g b) := by
      rw [Finset.sum_mul]

/-- Sum of base sites on admitted parents. -/
theorem sum_lowOwnerFirstOwnerDirichletBaseSite_admitted_eq
    (R p : ℕ) (sig : Finset ℕ) :
    (∑ a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig,
      lowOwnerFirstOwnerDirichletBaseSite R a) =
      lowOwnerFirstOwnerAdmittedBaseAmplitude R p sig := by
  unfold lowOwnerFirstOwnerAdmittedBaseAmplitude
  apply Finset.sum_congr rfl
  intro a ha
  have haBase := (Finset.mem_filter.mp ha).1
  rcases Finset.mem_filter.mp haBase with ⟨haCar, _hbase⟩
  rcases Finset.mem_filter.mp haCar with ⟨haIcc, _hmu⟩
  have haX : a ≤ squareRootEndpoint R := (Finset.mem_Icc.mp haIcc).2
  unfold lowOwnerFirstOwnerDirichletBaseSite lowOwnerZeroFrequencyMobiusSite
  rw [lowOwnerPhysicalDirichletWeight_eq_weight_of_le haX]

/-- Sum of base sites on clipped parents. -/
theorem sum_lowOwnerFirstOwnerDirichletBaseSite_clipped_eq
    (R p : ℕ) (sig : Finset ℕ) :
    (∑ a ∈ lowOwnerFirstOwnerClippedBaseFiber R p sig,
      lowOwnerFirstOwnerDirichletBaseSite R a) =
      lowOwnerFirstOwnerClippedAmplitude R p sig := by
  unfold lowOwnerFirstOwnerClippedAmplitude
  apply Finset.sum_congr rfl
  intro a ha
  have haBase := (Finset.mem_filter.mp ha).1
  rcases Finset.mem_filter.mp haBase with ⟨haCar, _hbase⟩
  rcases Finset.mem_filter.mp haCar with ⟨haIcc, _hmu⟩
  have haX : a ≤ squareRootEndpoint R := (Finset.mem_Icc.mp haIcc).2
  unfold lowOwnerFirstOwnerDirichletBaseSite lowOwnerZeroFrequencyMobiusSite
  rw [lowOwnerPhysicalDirichletWeight_eq_weight_of_le haX]

/-- Sum of returned child sites on admitted parents is `J`. -/
theorem sum_lowOwnerFirstOwnerDirichletReturnedChildSite_admitted_eq
    (R p : ℕ) (sig : Finset ℕ) :
    (∑ a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig,
      lowOwnerFirstOwnerDirichletReturnedChildSite R p a) =
      lowOwnerFirstOwnerReturnedChildParentAmplitude R p sig := by
  unfold lowOwnerFirstOwnerReturnedChildParentAmplitude
  apply Finset.sum_congr rfl
  intro a ha
  exact lowOwnerFirstOwnerDirichletReturnedChildSite_eq_returned_of_admitted ha

/-- Sum of incidence sites on admitted parents is the compensated interior. -/
theorem sum_lowOwnerFirstOwnerDirichletIncidenceSite_admitted_eq
    {R p : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    (∑ a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig,
      lowOwnerFirstOwnerDirichletIncidenceSite R p a) =
      lowOwnerFirstOwnerCompensatedInteriorAmplitude R p sig := by
  unfold lowOwnerFirstOwnerDirichletIncidenceSite
  unfold lowOwnerFirstOwnerCompensatedInteriorAmplitude
  apply Finset.sum_congr rfl
  intro a ha
  exact lowOwnerPhysicalDirichletIncidence_mul_moebius_eq_compensatedSite hp ha

/-- **Admitted sector is exactly the complete interior polarization.** -/
theorem lowOwnerFirstOwnerAdmittedPolarizationMass_eq
    {R p : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    lowOwnerFirstOwnerAdmittedPolarizationMass R p sig =
      lowOwnerFirstOwnerCompensatedInteriorAmplitude R p sig ^ 2 -
        lowOwnerFirstOwnerAdmittedBaseAmplitude R p sig ^ 2 -
        lowOwnerFirstOwnerReturnedChildParentAmplitude R p sig ^ 2 := by
  unfold lowOwnerFirstOwnerAdmittedPolarizationMass
    lowOwnerFirstOwnerDirichletPolarizationAtom
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  rw [sum_product_mul_factor_sector,
    sum_product_mul_factor_sector,
    sum_product_mul_factor_sector]
  rw [sum_lowOwnerFirstOwnerDirichletIncidenceSite_admitted_eq hp,
    sum_lowOwnerFirstOwnerDirichletBaseSite_admitted_eq,
    sum_lowOwnerFirstOwnerDirichletReturnedChildSite_admitted_eq]
  ring

/-- **Mixed clipped sector is exactly the existing `-2 C J` term.** -/
theorem lowOwnerFirstOwnerClippedMixedPolarizationMass_eq
    (R p : ℕ) (sig : Finset ℕ) :
    lowOwnerFirstOwnerClippedMixedPolarizationMass R p sig =
      -2 * lowOwnerFirstOwnerClippedAmplitude R p sig *
        lowOwnerFirstOwnerReturnedChildParentAmplitude R p sig := by
  unfold lowOwnerFirstOwnerClippedMixedPolarizationMass
  have hleft :
      (∑ ab ∈ (lowOwnerFirstOwnerClippedBaseFiber R p sig).product
          (lowOwnerFirstOwnerAdmittedBaseFiber R p sig),
        lowOwnerFirstOwnerDirichletPolarizationAtom R p ab) =
      -lowOwnerFirstOwnerClippedAmplitude R p sig *
        lowOwnerFirstOwnerReturnedChildParentAmplitude R p sig := by
    calc
      (∑ ab ∈ (lowOwnerFirstOwnerClippedBaseFiber R p sig).product
          (lowOwnerFirstOwnerAdmittedBaseFiber R p sig),
        lowOwnerFirstOwnerDirichletPolarizationAtom R p ab) =
        ∑ ab ∈ (lowOwnerFirstOwnerClippedBaseFiber R p sig).product
            (lowOwnerFirstOwnerAdmittedBaseFiber R p sig),
          -(lowOwnerFirstOwnerDirichletBaseSite R ab.1 *
            lowOwnerFirstOwnerDirichletReturnedChildSite R p ab.2) := by
          apply Finset.sum_congr rfl
          intro ab hab
          rcases Finset.mem_product.mp hab with ⟨ha, hb⟩
          rw [lowOwnerFirstOwnerDirichletPolarizationAtom_eq_clipped_left ha hb]
          ring
      _ = -((∑ a ∈ lowOwnerFirstOwnerClippedBaseFiber R p sig,
              lowOwnerFirstOwnerDirichletBaseSite R a) *
            (∑ b ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig,
              lowOwnerFirstOwnerDirichletReturnedChildSite R p b)) := by
          rw [← sum_product_mul_factor_sector]
          rw [← Finset.sum_neg_distrib]
      _ = _ := by
          rw [sum_lowOwnerFirstOwnerDirichletBaseSite_clipped_eq,
            sum_lowOwnerFirstOwnerDirichletReturnedChildSite_admitted_eq]
          ring
  have hright :
      (∑ ab ∈ (lowOwnerFirstOwnerAdmittedBaseFiber R p sig).product
          (lowOwnerFirstOwnerClippedBaseFiber R p sig),
        lowOwnerFirstOwnerDirichletPolarizationAtom R p ab) =
      -lowOwnerFirstOwnerReturnedChildParentAmplitude R p sig *
        lowOwnerFirstOwnerClippedAmplitude R p sig := by
    calc
      (∑ ab ∈ (lowOwnerFirstOwnerAdmittedBaseFiber R p sig).product
          (lowOwnerFirstOwnerClippedBaseFiber R p sig),
        lowOwnerFirstOwnerDirichletPolarizationAtom R p ab) =
        ∑ ab ∈ (lowOwnerFirstOwnerAdmittedBaseFiber R p sig).product
            (lowOwnerFirstOwnerClippedBaseFiber R p sig),
          -(lowOwnerFirstOwnerDirichletReturnedChildSite R p ab.1 *
            lowOwnerFirstOwnerDirichletBaseSite R ab.2) := by
          apply Finset.sum_congr rfl
          intro ab hab
          rcases Finset.mem_product.mp hab with ⟨ha, hb⟩
          rw [lowOwnerFirstOwnerDirichletPolarizationAtom_eq_clipped_right ha hb]
          ring
      _ = -((∑ a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig,
              lowOwnerFirstOwnerDirichletReturnedChildSite R p a) *
            (∑ b ∈ lowOwnerFirstOwnerClippedBaseFiber R p sig,
              lowOwnerFirstOwnerDirichletBaseSite R b)) := by
          rw [← sum_product_mul_factor_sector]
          rw [← Finset.sum_neg_distrib]
      _ = _ := by
          rw [sum_lowOwnerFirstOwnerDirichletReturnedChildSite_admitted_eq,
            sum_lowOwnerFirstOwnerDirichletBaseSite_clipped_eq]
          ring
  rw [hleft, hright]
  ring

/-- **Legal sector decomposition of the signed cell telescope.** -/
theorem lowOwnerFirstOwnerSignedCellTelescope_eq_admitted_add_clippedMixed
    {R p : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    lowOwnerFirstOwnerSignedCellTelescope R p sig =
      lowOwnerFirstOwnerAdmittedPolarizationMass R p sig +
        lowOwnerFirstOwnerClippedMixedPolarizationMass R p sig := by
  rw [lowOwnerFirstOwnerAdmittedPolarizationMass_eq hp,
    lowOwnerFirstOwnerClippedMixedPolarizationMass_eq]
  unfold lowOwnerFirstOwnerSignedCellTelescope
  ring

end RHLean.Proof
