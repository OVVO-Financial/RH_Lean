import OAI.NumberTheory.DirichletL.Moments.Unequal

/-!
# Unconditional signed sextic residue completion: actual OpenAI character

Unlike the positive Gram and arbitrary source-energy comparisons, this
retains a NONPRINCIPAL sextic character before any norm/Cauchy-Schwarz.
The existing original OAI result
  CenteredMomentUnequal.lifted_character_sum_zero
says that the full (lifted) residue block vanishes. The new results
quantitatively bound EVERY nonuniform physical weight by its deviation
from a constant on that exact full residue block.

No 'favorable covariance' or power saving is assumed. The separate
geometric estimate required to show that the actual low physical rows
are nearly uniform across residue classes is NOT proved here.
-/

namespace OAI
noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.LowSignedSixthCompletion
open ActualEisensteinCubic
open SevenEighths.CenteredMomentUnequal

/-- Exact signed annihilation of a constant physical weight on the
complete original lifted sextic residue family. This is the ORIGINAL
finite OAI character cancellation, not a hypothesis. -/
theorem original_lifted_nonprincipal_constant_mode_zero
    (p v : O) (hpv : p ∣ v)
    [Fintype (Residue p)] [Fintype (Residue v)]
    (chiV : MulChar (Residue v) ℂ)
    (chi : MulChar (Residue p) ℂ) (hchi : chi ≠ 1)
    (hlift : ∀ x : O, chiV (Ideal.Quotient.mk _ x) =
      chi (Ideal.Quotient.mk _ x))
    (c : ℂ) :
    (∑ y : Residue v, c * chiV y) = 0 := by
  have hzero := lifted_character_sum_zero p v hpv chiV chi hchi hlift
  rw [← Finset.mul_sum, hzero, mul_zero]

/-- Actual signed NNS/character payment BEFORE abs values. If the
physical weight is constant on a complete residue block, the source
vanishes. For arbitrary nonuniform weights, ONLY the weight deviation
survives, with no fictitious per-fiber density assumption. -/
theorem original_lifted_nonprincipal_weight_variation
    (p v : O) (hpv : p ∣ v)
    [Fintype (Residue p)] [Fintype (Residue v)]
    (chiV : MulChar (Residue v) ℂ)
    (chi : MulChar (Residue p) ℂ) (hchi : chi ≠ 1)
    (hlift : ∀ x : O, chiV (Ideal.Quotient.mk _ x) =
      chi (Ideal.Quotient.mk _ x))
    (W : Residue v → ℂ) (c : ℂ) :
    ‖∑ y : Residue v, W y * chiV y‖ ≤
      ∑ y : Residue v, ‖W y - c‖ := by
  have hzero := lifted_character_sum_zero p v hpv chiV chi hchi hlift
  have hshift :
      (∑ y : Residue v, (W y - c) * chiV y) =
        ∑ y : Residue v, W y * chiV y := by
    simp_rw [sub_mul, Finset.sum_sub_distrib]
    rw [← Finset.mul_sum, hzero, mul_zero, sub_zero]
  rw [← hshift]
  calc
    ‖∑ y : Residue v, (W y - c) * chiV y‖ ≤
        ∑ y : Residue v, ‖(W y - c) * chiV y‖ :=
      norm_sum_le _ _
    _ ≤ ∑ y : Residue v, ‖W y - c‖ := by
      apply Finset.sum_le_sum
      intro y hy
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (QuadraticInitialBound.norm_finite_character_le_one chiV y)

/-- The finite PHYSICAL weighting is exactly insensitive to the
constant residue mode. A user must now bound the ACTUAL deviation
of the compensated OpenAI physical row weight from a constant,
rather than postulate an unexplained negative covariance. -/
theorem original_weighted_residue_centering_exact
    (p v : O) (hpv : p ∣ v)
    [Fintype (Residue p)] [Fintype (Residue v)]
    (chiV : MulChar (Residue v) ℂ)
    (chi : MulChar (Residue p) ℂ) (hchi : chi ≠ 1)
    (hlift : ∀ x : O, chiV (Ideal.Quotient.mk _ x) =
      chi (Ideal.Quotient.mk _ x))
    (W : Residue v → ℂ) (c : ℂ) :
    (∑ y : Residue v, W y * chiV y) =
      ∑ y : Residue v, (W y - c) * chiV y := by
  have hzero := lifted_character_sum_zero p v hpv chiV chi hchi hlift
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, hzero, mul_zero, sub_zero]

#print axioms original_lifted_nonprincipal_constant_mode_zero
#print axioms original_lifted_nonprincipal_weight_variation
#print axioms original_weighted_residue_centering_exact

end SevenEighths.LowSignedSixthCompletion
end OAI
