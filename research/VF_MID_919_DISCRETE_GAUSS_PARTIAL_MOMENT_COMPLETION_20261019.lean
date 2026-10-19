import Mathlib.Analysis.Fourier.ZMod
import RHLean.Analysis.FiniteTorusFourierPairing
import «research.VF_MID_919_OAI_PARTIAL_MOMENT_TAILS»
import «research.VF_919_NATIVE_DISCRETE_GAUSS_PARTIAL_MOMENTS_20261019»

/-!
# Discrete character completion in native NNS UPM/LPM coordinates

No integrals, no OAI theorems, no custom axioms. The full finite
Fourier completion is already available natively as
`RHLean.Analysis.finiteTorusPairing_eq_spectral`.

This module turns its EXACT signed complex coefficients into the NNS
zero-target UPM(1)-LPM(1) convention and obtains a finite character
completion inequality by triangle inequalities. The multiplicative
character sum over a COMPLETE residue system is exactly zero if the
character is nonprincipal. The incomplete weighted sum is controlled
by the ENTIRE additive Fourier spectrum; this norm bound makes no
power-saving claim without proving a sharp Gauss bound and a bound
on the dual interval/window Fourier coefficients.

The ZMod model is the local split-prime component of the Eisenstein
ideal quotient. A full composite Eisenstein ideal uses the CRT product
of such components (including inert/ramified conductors).
-/

open scoped BigOperators

noncomputable section
namespace RHLean.Analysis

/-! Canonical native zero-target UPM1/LPM1 definitions are imported above.
     Reuse them instead of introducing distinct same-named declarations. -/

/-- Literal cancellation: the signed sum is UPM(1)-LPM(1).
    It is an EXACT sum, rather than a numerical quadrature. -/
theorem vf919DiscreteSignedSum_eq_UPM1_sub_LPM1
    {ι : Type*} (S : Finset ι) (f : ι → ℝ) :
    (∑ x ∈ S, f x) =
      vf919DiscreteUPM1 S f - vf919DiscreteLPM1 S f := by
  unfold vf919DiscreteUPM1 vf919DiscreteLPM1
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  simpa using (partialUpper_sub_partialLower (f x) 0).symm

/-- The real component of an arbitrary complex character row is exactly
    its positive-minus-negative zero-target partial mass. -/
theorem vf919DiscreteComplexRe_UPM_sub_LPM
    {ι : Type*} (S : Finset ι) (f : ι → ℂ) :
    (∑ x ∈ S, f x).re =
      vf919DiscreteUPM1 S (fun x => (f x).re) -
      vf919DiscreteLPM1 S (fun x => (f x).re) := by
  rw [Complex.re_sum]
  exact vf919DiscreteSignedSum_eq_UPM1_sub_LPM1
    S (fun x => (f x).re)

/-- The imaginary component is a SECOND signed partial moment.
    One scalar UPM/LPM row alone cannot encode a sextic complex phase. -/
theorem vf919DiscreteComplexIm_UPM_sub_LPM
    {ι : Type*} (S : Finset ι) (f : ι → ℂ) :
    (∑ x ∈ S, f x).im =
      vf919DiscreteUPM1 S (fun x => (f x).im) -
      vf919DiscreteLPM1 S (fun x => (f x).im) := by
  rw [Complex.im_sum]
  exact vf919DiscreteSignedSum_eq_UPM1_sub_LPM1
    S (fun x => (f x).im)

/-- Nonprincipal MULTIPLICATIVE character orthogonality on a COMPLETE
    residue system, now in both real and imaginary NNS partial moments.
    This does NOT assert zero on incomplete dyadic/box intervals. -/
theorem vf919NonprincipalCompleteResidue_UPM_LPM
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) :
    (vf919DiscreteUPM1 (Finset.univ : Finset (ZMod N))
        (fun x => (χ x).re) -
      vf919DiscreteLPM1 (Finset.univ : Finset (ZMod N))
        (fun x => (χ x).re) = 0) ∧
    (vf919DiscreteUPM1 (Finset.univ : Finset (ZMod N))
        (fun x => (χ x).im) -
      vf919DiscreteLPM1 (Finset.univ : Finset (ZMod N))
        (fun x => (χ x).im) = 0) := by
  have hz : (∑ x : ZMod N, χ x) = 0 :=
    MulChar.sum_eq_zero_of_ne_one hχ
  constructor
  · rw [← vf919DiscreteComplexRe_UPM_sub_LPM]
    simp [hz]
  · rw [← vf919DiscreteComplexIm_UPM_sub_LPM]
    simp [hz]

/-- ZERO ADDITIVE FREQUENCY of a nonprincipal character, with its true
    all-unit/nonunit mask, exactly from the finite DFT formula. -/
theorem vf919NonprincipalZeroGaussFrequency
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) :
    ZMod.dft (⇑χ) 0 = 0 := by
  rw [ZMod.dft_apply_zero]
  exact MulChar.sum_eq_zero_of_ne_one hχ

/-- Literal discrete additive Fourier/Gauss completion on ZMod N.
    The Fourier-side `r` is the genuine additive frequency, and
    `g` is the actual weighted physical interval/box cutoff. -/
theorem vf919DiscreteCharacterFourierCompletion
    {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N)
    (g : ZMod N → ℂ) :
    (∑ x : ZMod N, χ x * g x) =
      ((N : ℂ)⁻¹) *
        ∑ r : ZMod N, ZMod.dft (⇑χ) r *
          ZMod.dft g (-r) := by
  simpa only [finiteTorusPairing, finiteTorusSpectralPairing]
    using (finiteTorusPairing_eq_spectral (⇑χ) g)

/-- Stronger primitive-character completion: the additive spectrum of
    χ is its ACTUAL complex Gauss sum times the inverse character.
    The theorem is a FINITE-FOURIER identity, not an analytic estimate. -/
theorem vf919PrimitiveCharacterGaussCompletion
    {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)
    (g : ZMod N → ℂ) :
    (∑ x : ZMod N, χ x * g x) =
      (N : ℂ)⁻¹ * gaussSum χ ZMod.stdAddChar *
        ∑ r : ZMod N, χ⁻¹ (-r) * ZMod.dft g (-r) := by
  rw [vf919DiscreteCharacterFourierCompletion]
  simp_rw [hχ.fourierTransform_eq_inv_mul_gaussSum]
  calc
    (N : ℂ)⁻¹ *
      (∑ r : ZMod N,
        χ⁻¹ (-r) * gaussSum χ ZMod.stdAddChar * ZMod.dft g (-r)) =
      (N : ℂ)⁻¹ *
        (gaussSum χ ZMod.stdAddChar *
          ∑ r : ZMod N, χ⁻¹ (-r) * ZMod.dft g (-r)) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = _ := by ring

/-- **Quantitative finite Fourier completion**, in a form that can be
    instantiated by a true sextic Gauss bound. Crucially the hgauss
    hypothesis is an explicit finite additive spectrum estimate, NOT
    falsely deduced from Parseval energy. All dual frequencies remain. -/
theorem vf919DiscreteCharacterCompletion_norm_bound
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (g : ZMod N → ℂ) (H : ℝ)
    (hgauss : ∀ r : ZMod N, ‖ZMod.dft (⇑χ) r‖ ≤ H) :
    ‖∑ x : ZMod N, χ x * g x‖ ≤
      ‖(N : ℂ)⁻¹‖ * H *
        ∑ r : ZMod N, ‖ZMod.dft g (-r)‖ := by
  rw [vf919DiscreteCharacterFourierCompletion, norm_mul]
  calc
    ‖(N : ℂ)⁻¹‖ *
      ‖∑ r : ZMod N, ZMod.dft (⇑χ) r * ZMod.dft g (-r)‖ ≤
        ‖(N : ℂ)⁻¹‖ *
          ∑ r : ZMod N,
            ‖ZMod.dft (⇑χ) r * ZMod.dft g (-r)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
    _ = ‖(N : ℂ)⁻¹‖ *
          ∑ r : ZMod N,
            ‖ZMod.dft (⇑χ) r‖ * ‖ZMod.dft g (-r)‖ := by
      simp_rw [norm_mul]
    _ ≤ ‖(N : ℂ)⁻¹‖ *
          ∑ r : ZMod N, H * ‖ZMod.dft g (-r)‖ := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply Finset.sum_le_sum
      intro r _
      exact mul_le_mul_of_nonneg_right (hgauss r) (norm_nonneg _)
    _ = ‖(N : ℂ)⁻¹‖ * H *
          ∑ r : ZMod N, ‖ZMod.dft g (-r)‖ := by
      rw [← Finset.mul_sum]
      ring

#print axioms vf919DiscreteSignedSum_eq_UPM1_sub_LPM1
#print axioms vf919DiscreteComplexRe_UPM_sub_LPM
#print axioms vf919DiscreteComplexIm_UPM_sub_LPM
#print axioms vf919NonprincipalCompleteResidue_UPM_LPM
#print axioms vf919NonprincipalZeroGaussFrequency
#print axioms vf919DiscreteCharacterFourierCompletion
#print axioms vf919PrimitiveCharacterGaussCompletion
#print axioms vf919DiscreteCharacterCompletion_norm_bound

end RHLean.Analysis
