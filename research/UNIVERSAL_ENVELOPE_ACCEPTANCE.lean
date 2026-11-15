import «research.UNIVERSAL_ENVELOPE_ARITHMETIC»
import «research.UNIVERSAL_ENVELOPE_KERNEL»
import «research.UNIVERSAL_ENVELOPE_ZERO_FORCED»
import «research.UNIVERSAL_ENVELOPE_HISTORY»
import «research.UNIVERSAL_ENVELOPE_LAWS»
import «research.UNIVERSAL_ENVELOPE_AMPLIFICATION_LAW»
import «research.UNIVERSAL_ENVELOPE_OWNER_EQUIVALENCE»
import «research.UNIVERSAL_ENVELOPE_ZERO_LOG»

/-!
Exact-type acceptance for the original arithmetic source. These examples
retain the strict-history denominator, every positive loss, and the actual
native owner source. None asserts an open RH-strength premise.
-/

noncomputable section
set_option autoImplicit false

open scoped ArithmeticFunction.Moebius BigOperators
open RHLean.Proof RHLean.Analysis RHLean.Analysis.MertensExponent
open RHLean.Analysis.UniversalEnvelope RHLean.Analysis.OwnerPrefix

example (lam eta : ℝ) :
    EnvelopeBound lam eta ↔
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℕ, 2 ≤ R →
        ‖mertensSummatory (squareRootEndpoint R) - 1‖ ≤
          C * (R : ℝ) ^ (1 + eta + ε) *
            squareRootHistoricalK R ^ (lam / 2) := Iff.rfl

example {lam eta : ℝ} (hlam0 : 0 ≤ lam) (hlam2 : lam < 2)
    (heta : 0 ≤ eta) (h : EnvelopeBound lam eta) :
    zetaRightmostRealPart ≤ 1 / 2 + eta / (2 - lam) :=
  rightmost_le_of_envelopeBound hlam0 hlam2 heta h

example {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam2 : lam < 2) :
    EnvelopeBound lam 0 ↔ MertensGrowthAtMost (1 / 2 : ℝ) :=
  envelopeBound_zero_iff_mertens_half hlam0 hlam2

example (F : ℕ → ℂ) {N : ℕ} (hN : 1 ≤ N) :
    (∑ d ∈ Finset.Icc 1 N, (((μ d : ℤ) : ℂ)) *
      ∑ n ∈ Finset.Icc 1 (N / d), F (d * n)) = F 1 :=
  moebius_product_kernel_inversion F hN

example (F : ℝ → ℂ) {N : ℕ} (hN : 1 ≤ N) :
    (∑ d ∈ Finset.Icc 1 N, (((μ d : ℤ) : ℂ)) *
      divisorKernel F ((N : ℝ) / d)) = F N :=
  divisorKernel_inversion F hN

example {F κ : ℝ → ℂ} (hFone : F 1 = 0)
    (hF : ∀ v : ℝ, 1 ≤ v → HasDerivAt F (κ v / (v : ℂ)) v)
    {C : ℝ} (hC : 0 ≤ C)
    (hκ : ∀ u : ℝ, 1 ≤ u → ‖divisorKernel κ u‖ ≤ C)
    {N : ℕ} (hN : 1 ≤ N) :
    ‖F N‖ ≤ 8 * C * Real.sqrt (squareRootHistoricalK N) * Real.sqrt (N : ℝ) :=
  potential_norm_le_historical_sqrt hFone hF hC hκ hN

example {ρ : ℂ} (hzero : riemannZeta ρ = 0)
    (hβ : (1 / 2 : ℝ) < ρ.re) (hβ1 : ρ.re < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ R : ℕ in Filter.atTop,
      c * (R : ℝ) ^ (2 * ρ.re - 1) ≤ squareRootHistoricalK R :=
  zero_forces_historical_power hzero hβ hβ1

example (Y : ℕ) :
    squareRootHistoricalK Y ≤
      8 * (1 + squareRootAmplificationMax Y) * squareRootHistoricalK (Nat.sqrt Y + 1) :=
  historical_le_amplification_mul_sqrt_history Y

example {Y : ℕ} (hY : 1 ≤ Y) :
    ((Nat.sqrt Y + 1 : ℕ) : ℝ) ^ 2 ≤ 4 * (Y : ℝ) :=
  sqrt_cutoff_square_le hY

example : EnvelopeBound 2 0 := universal_envelope_bound

example {lam eta : ℝ} (hlam0 : 0 ≤ lam) (hlam2 : lam < 2) (heta : 0 ≤ eta) :
    EnvelopeBound lam eta ↔ zetaRightmostRealPart ≤ 1 / 2 + eta / (2 - lam) :=
  envelopeBound_iff_rightmost_le hlam0 hlam2 heta

example : Filter.Tendsto
    (fun R : ℕ => Real.log (squareRootHistoricalK R) / Real.log (R : ℝ))
    Filter.atTop (nhds (2 * envelopeExponent)) := historical_log_ratio_tendsto

example : Filter.Tendsto squareRootAmplificationLogRatio Filter.atTop
    (nhds envelopeExponent) := amplification_logRatio_tendsto

example : NativeOwnerBound 0 ↔ MertensGrowthAtMost (1 / 2 : ℝ) :=
  native_owner_zero_iff_mertens_half

example : NativeOwnerBound 0 ↔
    ∀ ρ : ℂ, NontrivialZetaZero ρ → ρ.re = (1 / 2 : ℝ) :=
  native_owner_zero_iff_criticalZeros

example : SquareRootAmplificationZeroLogGrowthStatement ↔
    MertensGrowthAtMost (1 / 2 : ℝ) := zeroLog_iff_mertens_half

example : SquareRootAmplificationZeroLogGrowthStatement ↔
    ∀ ρ : ℂ, NontrivialZetaZero ρ → ρ.re = (1 / 2 : ℝ) :=
  zeroLog_iff_criticalZeros

example (h : SquareRootAmplificationZeroLogGrowthStatement) :
    EnvelopeBound 1 0 := envelopeBound_one_zero_of_zeroLog h

end
