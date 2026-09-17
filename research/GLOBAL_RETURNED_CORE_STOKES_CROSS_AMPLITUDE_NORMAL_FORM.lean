import Mathlib
import «research.GLOBAL_RETURNED_CORE_DIRICHLET_PAIR_POLARIZATION»

/-!
# Cross-amplitude normal form of one signed Stokes cell

The Dirichlet polarization is not genuinely a difference of three unrelated
energies.  Pointwise, because the incidence coordinate is `base - returned`,

  d(a)d(b) - ell(a)ell(b) - j(a)j(b)
    = -ell(a)j(b) - j(a)ell(b).

Summing the full base-fibre square therefore factorizes exactly.  One signed
cell telescope is `-2` times the base amplitude times the returned-child
amplitude.  This is an equality before every norm or inequality.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

private theorem sum_product_cross_factor
    (s : Finset ℕ) (f g : ℕ → ℝ) :
    (∑ ab ∈ s.product s,
      (-(f ab.1 * g ab.2) - g ab.1 * f ab.2)) =
      -2 * (∑ a ∈ s, f a) * (∑ b ∈ s, g b) := by
  have hfg :
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
  have hgf :
      (∑ ab ∈ s.product s, g ab.1 * f ab.2) =
        (∑ a ∈ s, g a) * (∑ b ∈ s, f b) := by
    calc
      (∑ ab ∈ s.product s, g ab.1 * f ab.2) =
          ∑ a ∈ s, ∑ b ∈ s, g a * f b := by
            simpa only using
              (Finset.sum_product
                (s := s) (t := s)
                (f := fun ab : ℕ × ℕ => g ab.1 * f ab.2))
      _ = ∑ a ∈ s, g a * (∑ b ∈ s, f b) := by
        apply Finset.sum_congr rfl
        intro a _ha
        rw [Finset.mul_sum]
      _ = (∑ a ∈ s, g a) * (∑ b ∈ s, f b) := by
        rw [Finset.sum_mul]
  rw [← Finset.sum_neg_distrib, Finset.sum_sub_distrib]
  rw [hfg, hgf]
  ring

/-- **Exact cell cross-amplitude factorization.** -/
theorem lowOwnerFirstOwnerSignedCellTelescope_eq_neg_two_base_mul_returned
    {R p : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    lowOwnerFirstOwnerSignedCellTelescope R p sig =
      -2 * lowOwnerFirstOwnerBaseAmplitude R p sig *
        lowOwnerFirstOwnerReturnedChildParentAmplitude R p sig := by
  rw [lowOwnerFirstOwnerSignedCellTelescope_eq_sum_dirichletPolarizationAtoms hp]
  let s := lowOwnerFirstOwnerBaseFiber R p sig
  have hatom :
      ∀ ab ∈ s.product s,
        lowOwnerFirstOwnerDirichletPolarizationAtom R p ab =
          -(lowOwnerFirstOwnerDirichletBaseSite R ab.1 *
              lowOwnerFirstOwnerDirichletReturnedChildSite R p ab.2) -
            lowOwnerFirstOwnerDirichletReturnedChildSite R p ab.1 *
              lowOwnerFirstOwnerDirichletBaseSite R ab.2 := by
    intro ab hab
    rcases Finset.mem_product.mp hab with ⟨ha, hb⟩
    exact lowOwnerFirstOwnerDirichletPolarizationAtom_eq_mixed ha hb
  change
    (∑ ab ∈ s.product s,
      lowOwnerFirstOwnerDirichletPolarizationAtom R p ab) = _
  calc
    (∑ ab ∈ s.product s,
        lowOwnerFirstOwnerDirichletPolarizationAtom R p ab) =
      ∑ ab ∈ s.product s,
        (-(lowOwnerFirstOwnerDirichletBaseSite R ab.1 *
            lowOwnerFirstOwnerDirichletReturnedChildSite R p ab.2) -
          lowOwnerFirstOwnerDirichletReturnedChildSite R p ab.1 *
            lowOwnerFirstOwnerDirichletBaseSite R ab.2) := by
              apply Finset.sum_congr rfl
              intro ab hab
              exact hatom ab hab
    _ = -2 *
        (∑ a ∈ s, lowOwnerFirstOwnerDirichletBaseSite R a) *
        (∑ b ∈ s, lowOwnerFirstOwnerDirichletReturnedChildSite R p b) := by
          exact sum_product_cross_factor s
            (lowOwnerFirstOwnerDirichletBaseSite R)
            (lowOwnerFirstOwnerDirichletReturnedChildSite R p)
    _ = -2 * lowOwnerFirstOwnerBaseAmplitude R p sig *
        lowOwnerFirstOwnerReturnedChildParentAmplitude R p sig := by
          rw [show (∑ a ∈ s, lowOwnerFirstOwnerDirichletBaseSite R a) =
              lowOwnerFirstOwnerBaseAmplitude R p sig by
                simpa [s] using
                  sum_lowOwnerFirstOwnerDirichletBaseSite_eq_amplitude R p sig,
            show (∑ b ∈ s,
                lowOwnerFirstOwnerDirichletReturnedChildSite R p b) =
              lowOwnerFirstOwnerReturnedChildParentAmplitude R p sig by
                simpa [s] using
                  (sum_lowOwnerFirstOwnerDirichletReturnedChildSite_eq_returned
                    (R := R) (p := p) (sig := sig))]

/-- Global signed telescope in pure cross-amplitude currency. -/
theorem sum_signedCellTelescope_eq_neg_two_sum_base_mul_returned
    (R : ℕ) :
    (∑ p ∈ primesUpTo (squareRootEndpoint R),
      ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
        lowOwnerFirstOwnerSignedCellTelescope R p sig) =
      ∑ p ∈ primesUpTo (squareRootEndpoint R),
        ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
          (-2 * lowOwnerFirstOwnerBaseAmplitude R p sig *
            lowOwnerFirstOwnerReturnedChildParentAmplitude R p sig) := by
  apply Finset.sum_congr rfl
  intro p hpMem
  have hp : p.Prime := (mem_primesUpTo.mp hpMem).1
  apply Finset.sum_congr rfl
  intro sig _hsig
  exact lowOwnerFirstOwnerSignedCellTelescope_eq_neg_two_base_mul_returned hp

end RHLean.Proof
