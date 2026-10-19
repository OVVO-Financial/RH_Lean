import «research.VF_MID_919_OAI_PARTIAL_MOMENT_TAILS»
import RHLean.Analysis.FiniteTorusFourierPairing

/-!
# Sextic-ready complete and incomplete character sums without integration

This is the native discrete arithmetic framework:

* exact unnormalized NNS zero-target UPM1/LPM1 decomposition;
* COMPLETE nonprincipal multiplicative-character orthogonality over ZMod N;
* separately zero real and imaginary partial-moment imbalances;
* EXACT incomplete-window Fourier completion on the finite additive torus;
* a quantitative incomplete-window estimate derived from an EXPLICIT
  pointwise Fourier coefficient envelope B and the actual window Fourier
  l1 mass. This inequality is unconditional as a FINITE inequality;
  the bound B is a parameter, NOT an asserted sextic Gauss theorem.

No OAI modules, Lebesgue integration, asymptotic character assumptions,
or conditional 7/8 nonvanishing inputs are imported. This module reuses
RHLean's true finiteTorusPairing_eq_spectral and partialUpper /
partialLower definitions, hence the original physical mask can be
passed directly as g once the ideal indexing has been established.

The full primitive sextic ideal-row Gauss amplitude and uniform
l1 window estimates still require source-specific hypotheses/proofs;
finite orthogonality alone never implies pointwise cancellation on
a restricted window.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

/-- Unnormalized zero-target upper first partial moment (genuine NNS UPM1). -/
def vf919DiscreteUPM1 {ι : Type*} (S : Finset ι) (f : ι → ℝ) : ℝ :=
  ∑ x ∈ S, partialUpper (f x) 0

/-- Unnormalized zero-target lower first partial moment (genuine NNS LPM1). -/
def vf919DiscreteLPM1 {ι : Type*} (S : Finset ι) (f : ι → ℝ) : ℝ :=
  ∑ x ∈ S, partialLower (f x) 0

/-- Every finite signed row is EXACTLY its zero-target UPM1 minus LPM1.
No continuum integral, population normalization or random-row assumption. -/
theorem vf919DiscreteUPM1_sub_LPM1_eq_sum
    {ι : Type*} (S : Finset ι) (f : ι → ℝ) :
    vf919DiscreteUPM1 S f - vf919DiscreteLPM1 S f =
      ∑ x ∈ S, f x := by
  unfold vf919DiscreteUPM1 vf919DiscreteLPM1
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  simpa only [sub_zero] using partialUpper_sub_partialLower (f x) 0

/-- The two first partial moments also reconstruct the genuine l1 mass. -/
theorem vf919DiscreteUPM1_add_LPM1_eq_absSum
    {ι : Type*} (S : Finset ι) (f : ι → ℝ) :
    vf919DiscreteUPM1 S f + vf919DiscreteLPM1 S f =
      ∑ x ∈ S, |f x| := by
  unfold vf919DiscreteUPM1 vf919DiscreteLPM1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : 0 ≤ f x
  · have hn : ¬ f x < 0 := not_lt_of_ge hx
    simp [partialUpper, partialLower, hx, hn, abs_of_nonneg hx]
  · have hlt : f x < 0 := lt_of_not_ge hx
    simp [partialUpper, partialLower, hx, hlt, abs_of_neg hlt]

/-- The EXACT real and imaginary signed moment coordinates of a complex
character row. This retains both components of each sextic phase. -/
theorem vf919ComplexUPM_LPM_reassembly
    {ι : Type*} (S : Finset ι) (χ : ι → ℂ) :
    ((∑ x ∈ S, χ x).re =
      vf919DiscreteUPM1 S (fun x => (χ x).re) -
        vf919DiscreteLPM1 S (fun x => (χ x).re)) ∧
    ((∑ x ∈ S, χ x).im =
      vf919DiscreteUPM1 S (fun x => (χ x).im) -
        vf919DiscreteLPM1 S (fun x => (χ x).im)) := by
  constructor
  · rw [Complex.re_sum]
    exact (vf919DiscreteUPM1_sub_LPM1_eq_sum S
      (fun x => (χ x).re)).symm
  · rw [Complex.im_sum]
    exact (vf919DiscreteUPM1_sub_LPM1_eq_sum S
      (fun x => (χ x).im)).symm

/-- COMPLETE residue cancellation of an actual nontrivial multiplicative
character, including its zero extension at nonunits. No heuristic
independence: this is the finite-character orthogonality theorem. -/
theorem vf919CompleteResidueCharacter_sum_zero
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) :
    (∑ x : ZMod N, χ x) = 0 := by
  exact MulChar.sum_eq_zero_of_ne_one hχ

/-- Exact zero-target UPM1/LPM1 cancellation in BOTH sextic phase
coordinates on a COMPLETE residue system, not an incomplete window. -/
theorem vf919CompleteResidueCharacter_partialMomentBalance
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) :
    (vf919DiscreteUPM1 (Finset.univ : Finset (ZMod N))
        (fun x => (χ x).re) =
      vf919DiscreteLPM1 Finset.univ (fun x => (χ x).re)) ∧
    (vf919DiscreteUPM1 (Finset.univ : Finset (ZMod N))
        (fun x => (χ x).im) =
      vf919DiscreteLPM1 Finset.univ (fun x => (χ x).im)) := by
  have hz := vf919CompleteResidueCharacter_sum_zero χ hχ
  obtain ⟨hreal, himag⟩ :=
    vf919ComplexUPM_LPM_reassembly (Finset.univ : Finset (ZMod N))
      (fun x => χ x)
  constructor
  · have hzre : (∑ x : ZMod N, χ x).re = 0 := by rw [hz]; rfl
    rw [hzre] at hreal
    exact (sub_eq_zero.mp hreal.symm)
  · have hzim : (∑ x : ZMod N, χ x).im = 0 := by rw [hz]; rfl
    rw [hzim] at himag
    exact (sub_eq_zero.mp himag.symm)

/-- Exact discrete finite-Fourier completion for EVERY bounded/
incomplete window g, with RHLean's established sign convention:
the window transform is evaluated at -v. -/
theorem vf919IncompleteCharacter_exactFourier
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (g : ZMod N → ℂ) :
    (∑ x : ZMod N, χ x * g x) =
      (N : ℂ)⁻¹ *
        ∑ v : ZMod N, ZMod.dft (fun x => χ x) v *
          ZMod.dft g (-v) := by
  exact finiteTorusPairing_eq_spectral (fun x => χ x) g

/-- Bound for an incomplete character sum using the TRUE Fourier envelope
and the actual window Fourier l1 mass, with NO Lebesgue integral.
Unlike complete orthogonality, this controls arbitrary g only after a
valid pointwise Gauss envelope B has been supplied. -/
theorem vf919IncompleteCharacter_FourierEnvelope
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (g : ZMod N → ℂ) (B : ℝ)
    (hB : ∀ v : ZMod N, ‖ZMod.dft (fun x => χ x) v‖ ≤ B) :
    ‖∑ x : ZMod N, χ x * g x‖ ≤
      ‖(N : ℂ)⁻¹‖ * B *
        (∑ v : ZMod N, ‖ZMod.dft g (-v)‖) := by
  rw [vf919IncompleteCharacter_exactFourier χ g]
  rw [norm_mul]
  have htri :
      ‖∑ v : ZMod N, ZMod.dft (fun x => χ x) v *
          ZMod.dft g (-v)‖ ≤
        ∑ v : ZMod N,
          ‖ZMod.dft (fun x => χ x) v * ZMod.dft g (-v)‖ :=
    norm_sum_le _ _
  have henv :
      (∑ v : ZMod N,
        ‖ZMod.dft (fun x => χ x) v * ZMod.dft g (-v)‖) ≤
      B * (∑ v : ZMod N, ‖ZMod.dft g (-v)‖) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro v _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hB v) (norm_nonneg _)
  calc
    ‖(N : ℂ)⁻¹‖ *
        ‖∑ v : ZMod N,
            ZMod.dft (fun x => χ x) v * ZMod.dft g (-v)‖ ≤
      ‖(N : ℂ)⁻¹‖ * (∑ v : ZMod N,
          ‖ZMod.dft (fun x => χ x) v * ZMod.dft g (-v)‖) :=
        mul_le_mul_of_nonneg_left htri (norm_nonneg _)
    _ ≤ ‖(N : ℂ)⁻¹‖ * (B *
          ∑ v : ZMod N, ‖ZMod.dft g (-v)‖) :=
        mul_le_mul_of_nonneg_left henv (norm_nonneg _)
    _ = ‖(N : ℂ)⁻¹‖ * B *
          (∑ v : ZMod N, ‖ZMod.dft g (-v)‖) := by ring

#print axioms vf919DiscreteUPM1_sub_LPM1_eq_sum
#print axioms vf919DiscreteUPM1_add_LPM1_eq_absSum
#print axioms vf919ComplexUPM_LPM_reassembly
#print axioms vf919CompleteResidueCharacter_sum_zero
#print axioms vf919CompleteResidueCharacter_partialMomentBalance
#print axioms vf919IncompleteCharacter_exactFourier
#print axioms vf919IncompleteCharacter_FourierEnvelope

end RHLean.Analysis
