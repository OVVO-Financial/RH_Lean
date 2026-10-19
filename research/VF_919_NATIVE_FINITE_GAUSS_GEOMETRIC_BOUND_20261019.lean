import «research.VF_919_NATIVE_DISCRETE_GAUSS_PARTIAL_MOMENTS_20261019»
import RHLean.Analysis.PrimeWheelCoconductorTailBound

/-!
# The native finite Gauss and incomplete-window geometric bound

This uses only Mathlib finite Gauss sums and RHLean's existing
primeWheelDirichletKernel pointwise geometric-series estimate.
There is no Lebesgue integral, no OAI imported lemma and no
postulated sextic cancellation inequality.

A primitive nontrivial character modulo a split rational prime p
has an exact Gauss amplitude squared p. The separate actual
Eisenstein ideal-to-Dirichlet-character identification is needed
to apply that to a given ideal P|p.

The incomplete-window result is fully quantitative: it pairs any
valid Fourier coefficient bound B with RHLean's already proved
pointwise geometric Dirichlet-kernel majorants at EVERY frequency.
This is the correct finite Fourier completion step prior to a
uniform logarithmic l1 estimate and a varying-conductor moment bound.
-/

noncomputable section
open scoped BigOperators
open AddChar MulChar

namespace RHLean.Analysis

/-- Finite-field Gauss identity, including the complex star.
This is the square-root mechanism for a nontrivial character over
a prime field. It does NOT require analytic Fourier integration. -/
theorem vf919SplitPrimeGauss_mul_star_card
    {p : ℕ} [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) :
    gaussSum χ (ZMod.stdAddChar : AddChar (ZMod p) ℂ) *
        star (gaussSum χ (ZMod.stdAddChar : AddChar (ZMod p) ℂ)) =
      (p : ℂ) := by
  let ψ : AddChar (ZMod p) ℂ := ZMod.stdAddChar
  have hψ : ψ.IsPrimitive := ZMod.isPrimitive_stdAddChar p
  have hstar : star (gaussSum χ ψ) = gaussSum χ⁻¹ ψ⁻¹ := by
    calc
      _ = ∑ x : ZMod p, star (ψ x) * χ⁻¹ x := by
        simp [gaussSum, star_mul, MulChar.star_apply']
      _ = ∑ x : ZMod p, ψ⁻¹ x * χ⁻¹ x := by
        simp [← starRingEnd_apply, map_neg_eq_conj]
      _ = _ := by simp [mul_comm, gaussSum]
  have hpair : gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹ =
      (Fintype.card (ZMod p) : ℂ) :=
    gaussSum_mul_gaussSum_eq_card hχ hψ
  change gaussSum χ ψ * star (gaussSum χ ψ) = (p : ℂ)
  rw [hstar]
  simpa using hpair

/-- EXACT sqrt(p) Gauss amplitude in squared-norm form on a
nontrivial complex multiplicative character of F_p. -/
theorem vf919SplitPrimeGauss_norm_sq
    {p : ℕ} [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) :
    ‖gaussSum χ (ZMod.stdAddChar : AddChar (ZMod p) ℂ)‖ ^ 2 =
      (p : ℝ) := by
  let g : ℂ := gaussSum χ (ZMod.stdAddChar : AddChar (ZMod p) ℂ)
  have hpair : g * star g = (p : ℂ) :=
    vf919SplitPrimeGauss_mul_star_card χ hχ
  have hnormSq : ((Complex.normSq g : ℝ) : ℂ) = (p : ℂ) := by
    calc
      ((Complex.normSq g : ℝ) : ℂ) = g * star g := by
        rw [Complex.star_def, Complex.mul_conj]
      _ = (p : ℂ) := hpair
  have hreal : Complex.normSq g = (p : ℝ) := by
    exact_mod_cast hnormSq
  exact (Complex.sq_norm g).trans hreal

/-- Genuine primitive character Fourier transform equals its Gauss
constant times an inverse character. No analytic character mean
input is assumed. -/
theorem vf919PrimitiveDirichlet_dft_eq_phase_gauss
    {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N)
    (hχ : χ.IsPrimitive) (v : ZMod N) :
    ZMod.dft (fun x => χ x) v =
      χ⁻¹ (-v) * gaussSum χ (ZMod.stdAddChar) :=
  hχ.fourierTransform_eq_inv_mul_gaussSum v

/-- Exact pointwise window Fourier estimate on the native prime-wheel
physical interval. Each additive frequency is paid by RHLean's
compiled min(length, reciprocal chord) majorant. -/
theorem vf919NativeWindow_dft_le_geometric
    (W : RHLean.Arithmetic.PrimeWheelFiniteSystem)
    (L : ℕ) (v : ZMod W.modulus)
    (hL : W.lower + L ≤ W.upper) :
    ‖ZMod.dft (W.torusPrefixWindow (W.lower + L)) (-v)‖ ≤
      primeWheelDirichletPointBound W L v := by
  change ‖W.prefixWindowSpectrum (W.lower + L) (-v)‖ ≤
    primeWheelDirichletPointBound W L v
  rw [prefixWindowSpectrum_neg_eq_phase_mul_dirichlet W L v hL, norm_mul]
  have hphase : ‖primeWheelPinnedPhase W v‖ = 1 := by
    simp [primeWheelPinnedPhase, ZMod.stdAddChar_apply]
  rw [hphase, one_mul]
  exact norm_primeWheelDirichletKernel_le_pointBound W L v

/-- Native fully discrete incomplete-window character estimate,
combining actual Fourier completion with the source's own exact
geometric point-bound. The only input is the explicit character
Gauss-envelope B, not any power-saving analytic estimate. -/
theorem vf919NativeWindow_character_le_geometric
    (W : RHLean.Arithmetic.PrimeWheelFiniteSystem)
    (χ : DirichletCharacter ℂ W.modulus)
    (L : ℕ) (hL : W.lower + L ≤ W.upper)
    (B : ℝ)
    (hB : ∀ v : ZMod W.modulus,
      ‖ZMod.dft (fun x => χ x) v‖ ≤ B) :
    ‖∑ x : ZMod W.modulus,
        χ x * W.torusPrefixWindow (W.lower + L) x‖ ≤
      ‖(W.modulus : ℂ)⁻¹‖ * B *
        ∑ v : ZMod W.modulus,
          primeWheelDirichletPointBound W L v := by
  have hbase := vf919IncompleteCharacter_FourierEnvelope
    χ (W.torusPrefixWindow (W.lower + L)) B hB
  have hwin :
      (∑ v : ZMod W.modulus,
        ‖ZMod.dft (W.torusPrefixWindow (W.lower + L)) (-v)‖) ≤
      ∑ v : ZMod W.modulus,
        primeWheelDirichletPointBound W L v := by
    exact Finset.sum_le_sum fun v _ =>
      vf919NativeWindow_dft_le_geometric W L v hL
  have hB0 : 0 ≤ B := by
    exact le_trans (norm_nonneg _) (hB 0)
  calc
    ‖∑ x : ZMod W.modulus,
        χ x * W.torusPrefixWindow (W.lower + L) x‖ ≤
      ‖(W.modulus : ℂ)⁻¹‖ * B *
        (∑ v : ZMod W.modulus,
          ‖ZMod.dft (W.torusPrefixWindow (W.lower + L)) (-v)‖) :=
        hbase
    _ ≤ ‖(W.modulus : ℂ)⁻¹‖ * B *
          ∑ v : ZMod W.modulus,
            primeWheelDirichletPointBound W L v :=
      mul_le_mul_of_nonneg_left hwin
        (mul_nonneg (norm_nonneg _) hB0)

#print axioms vf919SplitPrimeGauss_mul_star_card
#print axioms vf919SplitPrimeGauss_norm_sq
#print axioms vf919PrimitiveDirichlet_dft_eq_phase_gauss
#print axioms vf919NativeWindow_dft_le_geometric
#print axioms vf919NativeWindow_character_le_geometric

end RHLean.Analysis
