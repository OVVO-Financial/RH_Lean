import «research.UNIVERSAL_ENVELOPE_ARITHMETIC»
import «research.UNIVERSAL_ENVELOPE_KERNEL»
import «research.UNIVERSAL_ENVELOPE_ZERO_FORCED»
import «research.UNIVERSAL_ENVELOPE_HISTORY»
import «research.UNIVERSAL_ENVELOPE_LAWS»
import «research.UNIVERSAL_ENVELOPE_AMPLIFICATION_LAW»
import «research.UNIVERSAL_ENVELOPE_SQUARED_DICTIONARY»
import «research.UNIVERSAL_ENVELOPE_MERTENS_MAX»
import «research.UNIVERSAL_ENVELOPE_FROZEN_Q»
import «research.UNIVERSAL_ENVELOPE_RH_BRIDGES»
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

example {ρ : ℂ} (hzero : riemannZeta ρ = 0)
    (hβ : 0 < ρ.re) (hβ1 : ρ.re < 1) {N : ℕ} (hN : 1 ≤ N) :
    ‖(1 - ρ) / ρ‖ * ((N : ℝ) ^ ρ.re - 1) - Real.log (N : ℝ) ≤
      8 * zeroKernelConstant ρ * Real.sqrt (squareRootHistoricalK N) * Real.sqrt (N : ℝ) :=
  zero_forces_historical_finite hzero hβ hβ1 hN

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

example (p : ℝ) : SquaredEnvelopeBound p ↔
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℕ, 2 ≤ R →
      ‖mertensSummatory (squareRootEndpoint R) - 1‖ ^ 2 ≤
        C * (R : ℝ) ^ (p + ε) * squareRootHistoricalK R := Iff.rfl

example {p : ℝ} (hp : 2 ≤ p) :
    SquaredEnvelopeBound p ↔ zetaRightmostRealPart ≤ (p - 1) / 2 :=
  squaredEnvelope_iff_rightmost_le hp

example : SquaredEnvelopeBound 2 ↔ SquareRootAmplificationZeroLogGrowthStatement :=
  squaredEnvelope_two_iff_zeroLog

example (hfinite : SquareRootMertensEndpointAmplificationStatement) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ j : ℕ,
      squareRootHistoricalK (2 ^ 2 ^ j) ≤ B ^ j :=
  historical_double_exponential_of_finiteAmplification hfinite

example (B : ℕ) (hB : 2 ≤ B) (C : ℝ) :
    mertensPrefixBudget B ≤ C ↔ ∀ n : ℕ, 1 ≤ n → n < B →
      ‖mertensSummatory n‖ / Real.sqrt (n : ℝ) ≤ C :=
  mertensPrefixBudget_le_iff B hB C

example (B : ℕ) : squareRootHistoricalK B ≤ 4 * mertensPrefixBudget B ^ 2 :=
  historical_le_four_prefixBudget_sq B

example (B : ℕ) (hB : 2 ≤ B) :
    mertensPrefixBudget B ^ 2 ≤ 9 * squareRootHistoricalK B :=
  prefixBudget_sq_le_nine_historical B hB

example : Filter.Tendsto
    (fun B : ℕ => Real.log (mertensPrefixBudget B) / Real.log (B : ℝ))
    Filter.atTop (nhds envelopeExponent) := prefixBudget_log_ratio_tendsto

example (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ B : ℕ, 2 ≤ B →
      mertensPrefixBudget (B ^ k) ≤ C * (B : ℝ) ^ ε * mertensPrefixBudget B ^ k :=
  prefixBudget_critical_lift k hk ε hε

example (k : ℕ) (hk : 1 ≤ k) (r : ℝ) (hr0 : 0 ≤ r) (hrk : r < (k : ℝ))
    (B : ℕ → ℕ) (hB : Filter.Tendsto B Filter.atTop Filter.atTop) :
    MertensPrefixLiftOn B k r ↔ MertensGrowthAtMost (1 / 2 : ℝ) :=
  subcritical_prefixLiftOn_iff_mertens_half k hk r hr0 hrk B hB

example (B : ℕ → ℕ) (k : ℕ) (r : ℝ) : MertensPrefixLiftOn B k r ↔
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ j : ℕ in Filter.atTop,
      mertensPrefixBudget ((B j) ^ k) ≤
        C * (B j : ℝ) ^ ε * (mertensPrefixBudget (B j)) ^ r := Iff.rfl

example (k : ℕ) (hk : 1 ≤ k) (r : ℝ) (hr0 : 0 ≤ r) (hrk : r < (k : ℝ)) :
    MertensPrefixLiftBound k r ↔ MertensGrowthAtMost (1 / 2 : ℝ) :=
  subcritical_prefixLiftBound_iff_mertens_half k hk r hr0 hrk

example (k : ℕ) (hk : 1 ≤ k) (r : ℝ) (hr0 : 0 ≤ r) (hrk : r < (k : ℝ))
    (B : ℕ → ℕ) (G : ℕ → ℝ) (hB : Filter.Tendsto B Filter.atTop Filter.atTop)
    (hG : ∀ᶠ j : ℕ in Filter.atTop, 1 ≤ G j)
    (hlogG : Filter.Tendsto
      (fun j => Real.log (G j) / Real.log (B j : ℝ)) Filter.atTop (nhds 0))
    (hstep : ∀ᶠ j : ℕ in Filter.atTop,
      mertensPrefixBudget ((B j) ^ k) ≤ G j * (mertensPrefixBudget (B j)) ^ r) :
    MertensGrowthAtMost (1 / 2 : ℝ) :=
  mertens_half_of_subcritical_subpower_gain k hk r hr0 hrk B G hB hG hlogG hstep

example (B : ℕ → ℕ) (k : ℕ) (r : ℝ) : MertensPrefixSubpowerGainLiftOn B k r ↔
    ∃ G : ℕ → ℝ,
      (∀ᶠ j : ℕ in Filter.atTop, 1 ≤ G j) ∧
      Filter.Tendsto (fun j => Real.log (G j) / Real.log (B j : ℝ))
        Filter.atTop (nhds 0) ∧
      ∀ᶠ j : ℕ in Filter.atTop,
        mertensPrefixBudget ((B j) ^ k) ≤ G j * (mertensPrefixBudget (B j)) ^ r := Iff.rfl

example (k : ℕ) (hk : 1 ≤ k) (r : ℝ) (hr0 : 0 ≤ r) (hrk : r < (k : ℝ))
    (B : ℕ → ℕ) (hB : Filter.Tendsto B Filter.atTop Filter.atTop) :
    MertensPrefixSubpowerGainLiftOn B k r ↔ MertensGrowthAtMost (1 / 2 : ℝ) :=
  subcritical_subpower_gain_iff_mertens_half k hk r hr0 hrk B hB

example (k : ℕ) (hk : 1 ≤ k) (r : ℝ) (hrk : r < (k : ℝ))
    (B : ℕ → ℕ) (hB : Filter.Tendsto B Filter.atTop Filter.atTop) :
    MertensPrefixSubpowerGainLiftOn B k r ↔ MertensGrowthAtMost (1 / 2 : ℝ) :=
  subcritical_subpower_gain_iff_mertens_half_of_lt k hk r hrk B hB

example (lam eta : ℝ) : FrozenQEnvelopeBound lam eta ↔
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℕ, 2 ≤ R →
      ‖eulerSelfDualBilinear R‖ ≤
        C * (R : ℝ) ^ (1 + eta + ε) * squareRootHistoricalK R ^ (lam / 2) := Iff.rfl

example {lam eta : ℝ} (hlam : 0 ≤ lam) (hlam2 : lam < 2) (heta : 0 ≤ eta) :
    FrozenQEnvelopeBound lam eta ↔ zetaRightmostRealPart ≤ 1 / 2 + eta / (2 - lam) :=
  frozenQEnvelope_iff_rightmost_le hlam hlam2 heta

example : FrozenQEnvelopeBound 2 0 := universal_frozenQ_envelope

example : MertensGrowthAtMost (1 / 2 : ℝ) ↔ RiemannHypothesis :=
  mertens_half_iff_riemannHypothesis

example : SquareRootAmplificationZeroLogGrowthStatement ↔ RiemannHypothesis :=
  zeroLog_iff_riemannHypothesis

example : SquareRootAmplificationZeroLogGrowthStatement ↔ MertensEnergyBoundedStatement :=
  zeroLog_iff_mertensEnergy

example : NativeOwnerBound 0 ↔ RiemannHypothesis :=
  native_owner_zero_iff_riemannHypothesis

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
