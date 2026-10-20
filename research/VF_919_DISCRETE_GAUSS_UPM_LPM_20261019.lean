import «research.VF_MID_919_OAI_PARTIAL_MOMENT_TAILS»
import RHLean.Analysis.FiniteTorusFourierPairing
import «research.VF_919_NATIVE_PRIME_GAUSS_NORM_20261019»

/-!
# Native finite Gauss/Fourier cancellation in zero-target NNS partial moments

Everything here is a FINITE sum (Finset/ZMod/Fintype).  No Lebesgue
integration, probabilistic independence, continuous Fourier transforms,
OAI imports, or asserted 7/8 zero-free theorem.

A real signed character sum is precisely UPM_1 - LPM_1.
For a complex sextic phase this applies SEPARATELY to real and imaginary
parts. Complete nontrivial-character sums vanish exactly.

The incomplete-window Fourier identity uses the native
RHLean.Analysis.finiteTorusPairing_eq_spectral. Its norm is bounded by
Gauss Fourier amplitude times the L1 norm of the WINDOW transform.
No pointwise square-root Gauss bound is deduced from Parseval alone.

The Gauss-product identity below proves the needed square-root
GAUSS MAGNITUDE for a nontrivial multiplicative character on a
FINITE FIELD and a primitive additive character, using the ordinary
finite algebra from Mathlib.NumberTheory.GaussSum. This is distinct
from a uniform Eisenstein-ideal family bound and from the stage-II
inverse/plain character moments.
-/

open scoped BigOperators

noncomputable section

namespace RHLean.Analysis

/-! The native finite Gauss import already DEFINES vf919DiscreteUPM1 and
vf919DiscreteLPM1. Reuse those declarations rather than redeclare them. -/

/-- The EXACT signed sum is UPM_1 - LPM_1. No approximation
    or quadrature, and no cancellation assumed. -/
theorem vf919DiscreteUPM1_sub_LPM1
    {ι : Type*} (S : Finset ι) (f : ι → ℝ) :
    vf919DiscreteUPM1 S f - vf919DiscreteLPM1 S f =
      ∑ x ∈ S, f x := by
  unfold vf919DiscreteUPM1 vf919DiscreteLPM1
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  simpa using partialUpper_sub_partialLower (f x) 0

/-- The zero target real and imaginary parts of any finite complex
    arithmetic sum are EXACTLY its two signed partial moments. -/
theorem vf919DiscreteComplexUPMLPM
    {ι : Type*} (S : Finset ι) (f : ι → ℂ) :
    vf919DiscreteUPM1 S (fun x => (f x).re) -
      vf919DiscreteLPM1 S (fun x => (f x).re) =
        (∑ x ∈ S, f x).re ∧
    vf919DiscreteUPM1 S (fun x => (f x).im) -
      vf919DiscreteLPM1 S (fun x => (f x).im) =
        (∑ x ∈ S, f x).im := by
  constructor
  · rw [vf919DiscreteUPM1_sub_LPM1]
    simp only [Complex.re_sum]
  · rw [vf919DiscreteUPM1_sub_LPM1]
    simp only [Complex.im_sum]

/-- COMPLETE-residue zero sum translates to TWO independent
    UPM_1 = LPM_1 identities, never a probabilistic argument. -/
theorem vf919CompleteResidueUPMLPM_eq
    (N : ℕ) [NeZero N] (χ : ZMod N → ℂ)
    (hzero : ∑ x : ZMod N, χ x = 0) :
    vf919DiscreteUPM1 Finset.univ (fun x => (χ x).re) =
      vf919DiscreteLPM1 Finset.univ (fun x => (χ x).re) ∧
    vf919DiscreteUPM1 Finset.univ (fun x => (χ x).im) =
      vf919DiscreteLPM1 Finset.univ (fun x => (χ x).im) := by
  have h := vf919DiscreteComplexUPMLPM Finset.univ χ
  constructor
  · have hreal := h.1
    rw [hzero] at hreal
    exact sub_eq_zero.mp (by simpa using hreal)
  · have himag := h.2
    rw [hzero] at himag
    exact sub_eq_zero.mp (by simpa using himag)

/-- FINITE character orthogonality supplies complete-residue
    cancellation for every nontrivial Dirichlet character. -/
theorem vf919NonprincipalCompleteResidueSum_zero
    (N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    (∑ x : ZMod N, χ x) = 0 := by
  exact MulChar.sum_eq_zero_of_ne_one hχ

/-- A GENUINE nontrivial finite character has equal zero-target upper
    and lower first moments in both complex coordinates. -/
theorem vf919NonprincipalCompleteResidueUPMLPM
    (N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    vf919DiscreteUPM1 Finset.univ (fun x => (χ x).re) =
      vf919DiscreteLPM1 Finset.univ (fun x => (χ x).re) ∧
    vf919DiscreteUPM1 Finset.univ (fun x => (χ x).im) =
      vf919DiscreteLPM1 Finset.univ (fun x => (χ x).im) :=
  vf919CompleteResidueUPMLPM_eq N χ
    (vf919NonprincipalCompleteResidueSum_zero N χ hχ)

/-- Exact INCOMPLETE character-window Fourier pairing, in the native
    finite ZMod torus. The arbitrary weight g can be a finite interval
    indicator or a discretely smoothed native owner window. -/
theorem vf919IncompleteWindowFourier
    (N : ℕ) [NeZero N]
    (χ g : ZMod N → ℂ) :
    (∑ x : ZMod N, χ x * g x) =
      ((N : ℂ)⁻¹) *
        ∑ v : ZMod N, ZMod.dft χ v * ZMod.dft g (-v) := by
  exact finiteTorusPairing_eq_spectral χ g

/-- Fully discrete Fourier completion in zero-target NNS currency;
    the complex phase must remain COMPLEX until after the transform.
    Real and imaginary UPM_1-LPM_1 identities are separate. -/
theorem vf919IncompleteWindowFourier_UPMLPM
    (N : ℕ) [NeZero N] (χ g : ZMod N → ℂ) :
    vf919DiscreteUPM1 Finset.univ (fun x => (χ x * g x).re) -
      vf919DiscreteLPM1 Finset.univ (fun x => (χ x * g x).re) =
        (((N : ℂ)⁻¹) *
          ∑ v : ZMod N, ZMod.dft χ v * ZMod.dft g (-v)).re ∧
    vf919DiscreteUPM1 Finset.univ (fun x => (χ x * g x).im) -
      vf919DiscreteLPM1 Finset.univ (fun x => (χ x * g x).im) =
        (((N : ℂ)⁻¹) *
          ∑ v : ZMod N, ZMod.dft χ v * ZMod.dft g (-v)).im := by
  have h := vf919DiscreteComplexUPMLPM Finset.univ
    (fun x => χ x * g x)
  constructor
  · rw [h.1, vf919IncompleteWindowFourier]
  · rw [h.2, vf919IncompleteWindowFourier]

/-- Exact finite Fourier incomplete-window bound: a Gauss-spectrum
    cap B times the L1 Fourier norm of the window. The B hypothesis
    is EXPLICIT (not a fictitious consequence of Parseval). -/
theorem vf919IncompleteWindowNorm_le_GaussL1
    (N : ℕ) [NeZero N] (χ g : ZMod N → ℂ) (B : ℝ)
    (hB : ∀ v : ZMod N, ‖ZMod.dft χ v‖ ≤ B) :
    ‖∑ x : ZMod N, χ x * g x‖ ≤
      ‖((N : ℂ)⁻¹)‖ * B *
        (∑ v : ZMod N, ‖ZMod.dft g (-v)‖) := by
  rw [vf919IncompleteWindowFourier, norm_mul]
  have hcore :
      ‖∑ v : ZMod N, ZMod.dft χ v * ZMod.dft g (-v)‖ ≤
        B * ∑ v : ZMod N, ‖ZMod.dft g (-v)‖ := by
    calc
      ‖∑ v : ZMod N, ZMod.dft χ v * ZMod.dft g (-v)‖ ≤
          ∑ v : ZMod N, ‖ZMod.dft χ v * ZMod.dft g (-v)‖ :=
            norm_sum_le _ _
      _ = ∑ v : ZMod N,
          ‖ZMod.dft χ v‖ * ‖ZMod.dft g (-v)‖ := by
            simp_rw [norm_mul]
      _ ≤ ∑ v : ZMod N, B * ‖ZMod.dft g (-v)‖ := by
            apply Finset.sum_le_sum
            intro v _
            exact mul_le_mul_of_nonneg_right (hB v) (norm_nonneg _)
      _ = B * ∑ v : ZMod N, ‖ZMod.dft g (-v)‖ := by
            rw [Finset.mul_sum]
  calc
    ‖((N : ℂ)⁻¹)‖ *
        ‖∑ v : ZMod N, ZMod.dft χ v * ZMod.dft g (-v)‖ ≤
      ‖((N : ℂ)⁻¹)‖ *
        (B * ∑ v : ZMod N, ‖ZMod.dft g (-v)‖) :=
          mul_le_mul_of_nonneg_left hcore (norm_nonneg _)
    _ = ‖((N : ℂ)⁻¹)‖ * B *
        (∑ v : ZMod N, ‖ZMod.dft g (-v)‖) := by ring

/-- A genuinely unconditional Gauss magnitude identity, using FINITE
    multiplicative-character orthogonality and primitive additive
    characters on a finite field. This proof is algebraic, no integrals.
    The sextic/ideal case must supply a genuine finite field or
    correct primitive-conductor quotient to apply it. -/
theorem vf919FiniteFieldPrimitiveGauss_norm_sq
    {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ≠ 1) (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ ^ 2 = (Fintype.card F : ℝ) := by
  -- Reuse the already warning-fatal, standard-axiom-verified native theorem.
  -- Its explicit conjugation argument does not depend on Mathlib's
  -- star_gaussSum_eq.
  exact vf919FiniteFieldGauss_squaredNorm χ ψ hχ hψ

#print axioms vf919DiscreteUPM1_sub_LPM1
#print axioms vf919DiscreteComplexUPMLPM
#print axioms vf919NonprincipalCompleteResidueUPMLPM
#print axioms vf919IncompleteWindowFourier
#print axioms vf919IncompleteWindowFourier_UPMLPM
#print axioms vf919IncompleteWindowNorm_le_GaussL1
#print axioms vf919FiniteFieldPrimitiveGauss_norm_sq

end RHLean.Analysis
