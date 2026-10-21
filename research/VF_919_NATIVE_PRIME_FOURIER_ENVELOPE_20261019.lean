import «research.VF_919_NATIVE_PRIME_GAUSS_NORM_20261019»

/-!
# Fully discrete prime-field character cancellation: exact sqrt-p envelope

Source: RHLean's Finset FTs, exact UPM/LPM reassembly, and the
finite-field Gauss product. No OAI theorem, integration, randomness, or
assumed Fourier coefficient envelope enters.

The true dependence on the incomplete window remains its ACTUAL
finite-Fourier l1 mass. A uniform estimate for that mass on the
Eisenstein two-dimensional annular/slot windows, and the full
variable-conductor sextic moment estimates, are additional theorems;
this result must not be reported as the whole seven-eighths theorem.
-/

noncomputable section

namespace RHLean.Analysis

/-- Pointwise square-root Fourier envelope for every nontrivial
character at a split PRIME ideal. At zero frequency, complete
character orthogonality applies; at a nonzero frequency, the
shifted additive character is primitive on the field ZMod p,
and the exact finite Gauss-product gives squared norm p. -/
theorem vf919SplitPrimeFourier_norm_le_sqrt
    (p : ℕ) [NeZero p] (hp : p.Prime)
    (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1)
    (v : ZMod p) :
    ‖ZMod.dft (fun x : ZMod p => χ x) v‖ ≤
      Real.sqrt (p : ℝ) := by
  let : Fact p.Prime := ⟨hp⟩
  by_cases hv : v = 0
  · subst v
    have hz : (∑ x : ZMod p, χ x) = 0 :=
      MulChar.sum_eq_zero_of_ne_one hχ
    rw [ZMod.dft_apply_zero, hz]
    simp [Real.sqrt_nonneg]
  · have hnonzero : (-v : ZMod p) ≠ 0 :=
      neg_ne_zero.mpr hv
    have hψnontrivial :
        (ZMod.stdAddChar (N := p)).mulShift (-v) ≠ 1 := by
      intro htrivial
      have heval := congrArg
        (fun ψ : AddChar (ZMod p) ℂ => ψ (1 : ZMod p)) htrivial
      have hchar : (ZMod.stdAddChar (N := p)) (-v) = 1 := by
        simpa [AddChar.mulShift_apply] using heval
      have hz : (-v : ZMod p) = 0 :=
        ZMod.injective_stdAddChar (by simpa using hchar)
      exact hnonzero hz
    have hψ : ((ZMod.stdAddChar (N := p)).mulShift (-v)).IsPrimitive :=
      AddChar.IsPrimitive.of_ne_one hψnontrivial
    have hfourier :
        ZMod.dft (fun x : ZMod p => χ x) v =
          gaussSum χ ((ZMod.stdAddChar (N := p)).mulShift (-v)) := by
      simpa using
        (DirichletCharacter.fourierTransform_eq_gaussSum_mulShift χ v)
    have hsq :
        ‖ZMod.dft (fun x : ZMod p => χ x) v‖ ^ 2 = (p : ℝ) := by
      rw [hfourier]
      simpa only [ZMod.card] using
        (vf919FiniteFieldGauss_squaredNorm χ _ hχ hψ)
    have hp0 : 0 ≤ (p : ℝ) := by positivity
    have hsqrt := Real.sq_sqrt hp0
    have hsqrt0 := Real.sqrt_nonneg (p : ℝ)
    have hnorm0 : 0 ≤ ‖ZMod.dft (fun x : ZMod p => χ x) v‖ :=
      norm_nonneg _
    nlinarith

/-- Genuine unconditional Pólya–Vinogradov INPUT at a split
prime ideal: for ANY incomplete window, the character Fourier
side costs exactly the proven sqrt(p) Gauss envelope times the
actual finite Fourier l1 mass of that window. -/
theorem vf919SplitPrimeIncompleteCharacter_sqrtGauss
    (p : ℕ) [NeZero p] (hp : p.Prime)
    (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1)
    (g : ZMod p → ℂ) :
    ‖∑ x : ZMod p, χ x * g x‖ ≤
      ‖(p : ℂ)⁻¹‖ * Real.sqrt (p : ℝ) *
        (∑ v : ZMod p, ‖ZMod.dft g (-v)‖) := by
  let : Fact p.Prime := ⟨hp⟩
  exact vf919IncompleteCharacter_FourierEnvelope χ g
    (Real.sqrt (p : ℝ))
    (vf919SplitPrimeFourier_norm_le_sqrt p hp χ hχ)

#print axioms vf919SplitPrimeFourier_norm_le_sqrt
#print axioms vf919SplitPrimeIncompleteCharacter_sqrtGauss

end RHLean.Analysis
