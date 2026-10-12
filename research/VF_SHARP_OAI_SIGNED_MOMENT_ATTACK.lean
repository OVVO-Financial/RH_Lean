import «research.VF_MID_919_OAI_NATIVE_PRINCIPAL_WELD»

/-!
# Analytic attack: actual sharp centered physical owner-two row

This module records the exact *one-sided* signed moment that would pay
the native owner-two Gram. It uses both literal AMP physical weights
and the constructed excluded-six norm coefficients. No smooth-profile
admissibility, ideal-semantic identification or uniform analytic bound
is assumed.

A single centered OpenAI row is ruled out occurrencewise by #919's
rank-three witness. This difference is a norm-weighted PHYSICAL kernel,
not a claim that it is an admissible OAI centered row.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic
attribute [local instance] Classical.propDecidable

/-- Keep both native AMP legs at the same literal rational Mobius site. -/
def vfSharpOAIPhysicalCenteredWeight (R n : ℕ) : ℂ :=
  (vf919OwnerTwoPhysicalParentSiteWeight R n : ℂ) -
    (vf919OwnerTwoPhysicalReturnedSiteWeight R n : ℂ)

/-- The physical centered row, in the exact excluded-six norm currency. -/
def vfSharpOAIPhysicalCenteredNormRow (R : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 (squareRootEndpoint R),
    vf919ExcludedNormCoefficients m *
      vf919PhysicalHeckeKernel (squareRootEndpoint R)
        (vfSharpOAIPhysicalCenteredWeight R) m

/-- The centered source is exactly H_R - J_R, with no replacement of
the parent cutoff, the returned-child n -> 2n cutoff, or the Mobius sign. -/
theorem vfSharpOAIPhysicalCenteredNormRow_eq_native_difference
    (R : ℕ) :
    vfSharpOAIPhysicalCenteredNormRow R =
      vf919OwnerTwoParentPrincipalNormSum R -
        vf919OwnerTwoReturnedPrincipalNormSum R := by
  unfold vfSharpOAIPhysicalCenteredNormRow
    vfSharpOAIPhysicalCenteredWeight
    vf919OwnerTwoParentPrincipalNormSum
    vf919OwnerTwoReturnedPrincipalNormSum
  simp_rw [vf919PhysicalHeckeKernel_sub]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m _hm
  ring

/-- A purely complex polarization identity retaining the real signed cross.
It does not assert any analytic cancellation. -/
theorem vfSharpOAIComplexCenteredPolarization (H J : ℂ) :
    Complex.normSq (H - J) =
      Complex.normSq H + Complex.normSq J -
        2 * (H * star J).re := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

/-- EXACT original native p=2 signed Gram as centered physical energy
minus the two nonnegative diagonal energies. -/
theorem vfSharpOAIActualGram_eq_centered_sub_diagonals
    (R : ℕ) (hX : 12 ≤ squareRootEndpoint R) :
    2 * lowOwnerFirstOwnerCellGram R 2 ∅ =
      Complex.normSq (vfSharpOAIPhysicalCenteredNormRow R) -
        Complex.normSq (vf919OwnerTwoParentPrincipalNormSum R) -
        Complex.normSq (vf919OwnerTwoReturnedPrincipalNormSum R) := by
  rw [vfSharpOAIPhysicalCenteredNormRow_eq_native_difference]
  rw [vf919OwnerTwoSignedGram_eq_constructedPrincipalNormPairing R hX]
  rw [vfSharpOAIComplexCenteredPolarization]
  ring

/-- The correctly directed analytic inlet. Any genuine upper bound on
the PHYSICAL centered norm-square pays the signed owner-two Gram.
The required upper bound itself is NOT proved here. -/
theorem vfSharpOAIActualGram_le_centeredEnergy
    (R : ℕ) (hX : 12 ≤ squareRootEndpoint R) :
    2 * lowOwnerFirstOwnerCellGram R 2 ∅ ≤
      Complex.normSq (vfSharpOAIPhysicalCenteredNormRow R) := by
  rw [vfSharpOAIActualGram_eq_centered_sub_diagonals R hX]
  have hH : 0 ≤ Complex.normSq (vf919OwnerTwoParentPrincipalNormSum R) := by
    rw [Complex.normSq_eq_norm_sq]
    positivity
  have hJ : 0 ≤ Complex.normSq (vf919OwnerTwoReturnedPrincipalNormSum R) := by
    rw [Complex.normSq_eq_norm_sq]
    positivity
  linarith

/-- Explicit analytic acceptance gate. The only new assumption is the
one-sided bound on the *exact* centered row, not on a proxy profile. -/
theorem vfSharpOAIActualGram_le_of_physical_centered_moment
    (R : ℕ) (hX : 12 ≤ squareRootEndpoint R) (B : ℝ)
    (hMoment : Complex.normSq (vfSharpOAIPhysicalCenteredNormRow R) ≤ B) :
    2 * lowOwnerFirstOwnerCellGram R 2 ∅ ≤ B :=
  (vfSharpOAIActualGram_le_centeredEnergy R hX).trans hMoment

end RHLean.Proof
