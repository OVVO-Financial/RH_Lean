import «research.UNIVERSAL_ENVELOPE_ZERO_FORCED»

/-! Independent exact-type gate for the analytic kernel and actual-zero input.
The full arithmetic acceptance remains separately required.
-/

noncomputable section
set_option autoImplicit false
open scoped ArithmeticFunction.Moebius BigOperators
open RHLean.Analysis RHLean.Analysis.UniversalEnvelope RHLean.Proof

example (F : ℕ → ℂ) {N : ℕ} (hN : 1 ≤ N) :
    (∑ d ∈ Finset.Icc 1 N, (((μ d : ℤ) : ℂ)) *
      ∑ n ∈ Finset.Icc 1 (N / d), F (d * n)) = F 1 :=
  moebius_product_kernel_inversion F hN

example {F κ : ℝ → ℂ} (hFone : F 1 = 0)
    (hF : ∀ v : ℝ, 1 ≤ v → HasDerivAt F (κ v / (v : ℂ)) v)
    {C : ℝ} (hC : 0 ≤ C)
    (hκ : ∀ u : ℝ, 1 ≤ u → ‖divisorKernel κ u‖ ≤ C)
    {N : ℕ} (hN : 1 ≤ N) :
    ‖F N‖ ≤ 8 * C * Real.sqrt (squareRootHistoricalK N) * Real.sqrt (N : ℝ) :=
  potential_norm_le_historical_sqrt hFone hF hC hκ hN

example {ρ : ℂ} (hzero : riemannZeta ρ = 0)
    (hβ : 0 < ρ.re) (hβ1 : ρ.re < 1) {u : ℝ} (hu : 1 ≤ u) :
    ‖divisorKernel (zeroSeed ρ) u‖ ≤ zeroKernelConstant ρ :=
  zeroSeed_kernel_norm_le hzero hβ hβ1 hu

example {ρ : ℂ} (hzero : riemannZeta ρ = 0)
    (hβ : 0 < ρ.re) (hβ1 : ρ.re < 1) {N : ℕ} (hN : 1 ≤ N) :
    ‖(1 - ρ) / ρ‖ * ((N : ℝ) ^ ρ.re - 1) - Real.log (N : ℝ) ≤
      8 * zeroKernelConstant ρ * Real.sqrt (squareRootHistoricalK N) * Real.sqrt (N : ℝ) :=
  zero_forces_historical_finite hzero hβ hβ1 hN

example {ρ : ℂ} (hzero : riemannZeta ρ = 0)
    (hβ : (1 / 2 : ℝ) < ρ.re) (hβ1 : ρ.re < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ R : ℕ in Filter.atTop,
      c * (R : ℝ) ^ (2 * ρ.re - 1) ≤ squareRootHistoricalK R :=
  zero_forces_historical_power hzero hβ hβ1

end
