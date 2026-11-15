import «research.UNIVERSAL_ENVELOPE_ARITHMETIC»
import RHLean.Proof.SquareRootAmplificationZeroLogConsumer
import RHLean.Proof.SquareRootAmplificationPowerBounds
import RHLean.Proof.SquareRootAncestryRoot

/-!
# Zero logarithmic amplification is equivalent to the critical Mertens bound

The running maximum and its denominator are the original strict-history
objects.  A zero logarithmic limit gives a simultaneous eventual budget for
every admitted endpoint.  Evaluating that budget at `N + R^2`, where `N` is
its fixed threshold, absorbs every small root into one finite constant and
produces the all-positive-loss square-root-history envelope.

The arithmetic envelope consumer then forces the zero boundary to 1/2.
Conversely, the critical Mertens bound and the already proved `K_R >= 1`
give the zero logarithmic limit.  This equivalence does not use the proposed
zero-forced historical lower envelope, and proves neither RH nor a uniform
finite amplification constant.
-/

noncomputable section

namespace RHLean.Analysis.UniversalEnvelope

open Filter RHLean.Proof RHLean.Analysis.MertensExponent

/-- Exponentiating the existing simultaneous zero-log budget gives the
original square-root-history envelope at every root.  The cutoff `N+R^2`
absorbs the finite exceptional range without changing the historical source. -/
theorem envelopeBound_one_zero_of_zeroLog
    (hzero : SquareRootAmplificationZeroLogGrowthStatement) :
    EnvelopeBound 1 0 := by
  intro ε hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (squareRootAmplificationZeroLog_eventually_native_envelope hzero hε)
  refine ⟨Real.sqrt (((N : ℝ) + 1) ^ ε), Real.sqrt_nonneg _, ?_⟩
  intro R hR
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by
    exact_mod_cast (show 1 ≤ R by omega)
  have hR0 : (0 : ℝ) < (R : ℝ) := by linarith
  have hRsq : (1 : ℝ) ≤ (R : ℝ) ^ 2 := by nlinarith
  have hXnat : squareRootEndpoint R ≤ N + R ^ 2 := by
    unfold squareRootEndpoint
    omega
  have hX0 : (0 : ℝ) < ((N + R ^ 2 : ℕ) : ℝ) := by
    have hRpow : 0 < R ^ 2 := pow_pos (by omega : 0 < R) 2
    exact_mod_cast (show 0 < N + R ^ 2 by omega)
  have hscale : ((N + R ^ 2 : ℕ) : ℝ) ≤
      ((N : ℝ) + 1) * (R : ℝ) ^ 2 := by
    calc
      ((N + R ^ 2 : ℕ) : ℝ) = (N : ℝ) + (R : ℝ) ^ 2 := by
        simp only [Nat.cast_add, Nat.cast_pow]
      _ ≤ (N : ℝ) * (R : ℝ) ^ 2 + (R : ℝ) ^ 2 :=
        by nlinarith only [le_mul_of_one_le_right (Nat.cast_nonneg N) hRsq]
      _ = ((N : ℝ) + 1) * (R : ℝ) ^ 2 := by ring
  have hpower : Real.exp (ε * Real.log ((N + R ^ 2 : ℕ) : ℝ)) ≤
      ((N : ℝ) + 1) ^ ε * (R : ℝ) ^ (2 * ε) := by
    calc
      Real.exp (ε * Real.log ((N + R ^ 2 : ℕ) : ℝ)) =
          ((N + R ^ 2 : ℕ) : ℝ) ^ ε := by
        rw [Real.rpow_def_of_pos hX0]
        congr 1
        ring
      _ ≤ (((N : ℝ) + 1) * (R : ℝ) ^ 2) ^ ε :=
        Real.rpow_le_rpow hX0.le hscale hε.le
      _ = ((N : ℝ) + 1) ^ ε * ((R : ℝ) ^ 2) ^ ε :=
        Real.mul_rpow (by positivity) (sq_nonneg _)
      _ = ((N : ℝ) + 1) ^ ε * (R : ℝ) ^ (2 * ε) := by
        rw [← Real.rpow_natCast (R : ℝ) 2, ← Real.rpow_mul hR0.le]
        norm_num
  have hcenter : ‖mertensSummatory (squareRootEndpoint R) - 1‖ =
      |((mertensSummatoryInt (squareRootEndpoint R) - 1 : ℤ) : ℝ)| := by
    have hcast : mertensSummatory (squareRootEndpoint R) - 1 =
        ((mertensSummatoryInt (squareRootEndpoint R) - 1 : ℤ) : ℂ) := by
      rw [Int.cast_sub, Int.cast_one, mertensSummatoryInt_cast]
    rw [hcast, Complex.norm_intCast]
  have hraw := hN (N + R ^ 2) (by omega) R hR hXnat
  have hnative : ‖mertensSummatory (squareRootEndpoint R) - 1‖ ^ 2 ≤
      Real.exp (ε * Real.log ((N + R ^ 2 : ℕ) : ℝ)) *
        (R : ℝ) ^ 2 * squareRootHistoricalK R := by
    simpa only [hcenter, sq_abs] using hraw
  have hK0 : 0 ≤ squareRootHistoricalK R := squareRootHistoricalK_nonneg R
  have hmajorant : ‖mertensSummatory (squareRootEndpoint R) - 1‖ ^ 2 ≤
      (((N : ℝ) + 1) ^ ε * (R : ℝ) ^ (2 * ε)) *
        (R : ℝ) ^ 2 * squareRootHistoricalK R :=
    hnative.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hpower (sq_nonneg _)) hK0)
  have hRpower : ((R : ℝ) ^ (1 + ε)) ^ (2 : ℕ) =
      (R : ℝ) ^ (2 * ε) * (R : ℝ) ^ (2 : ℕ) := by
    rw [pow_two, ← Real.rpow_add hR0]
    rw [show (1 + ε) + (1 + ε) = 2 * ε + (2 : ℝ) by ring,
      Real.rpow_add hR0]
    rw [Real.rpow_two]
  have hsquare :
      (Real.sqrt (((N : ℝ) + 1) ^ ε) * (R : ℝ) ^ (1 + ε) *
        Real.sqrt (squareRootHistoricalK R)) ^ 2 =
      (((N : ℝ) + 1) ^ ε * (R : ℝ) ^ (2 * ε)) *
        (R : ℝ) ^ 2 * squareRootHistoricalK R := by
    rw [mul_pow, mul_pow,
      Real.sq_sqrt (Real.rpow_nonneg (by positivity) ε),
      Real.sq_sqrt hK0, hRpower]
    ring
  have hroot : ‖mertensSummatory (squareRootEndpoint R) - 1‖ ≤
      Real.sqrt (((N : ℝ) + 1) ^ ε) * (R : ℝ) ^ (1 + ε) *
        Real.sqrt (squareRootHistoricalK R) := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [hsquare]
    exact hmajorant
  simpa only [add_zero, Real.sqrt_eq_rpow] using hroot

/-- The converse uses only the existing power-bound transport and the proved
positive historical denominator.  Constants are fixed before each cutoff. -/
theorem zeroLog_of_mertens_half
    (hgrowth : MertensGrowthAtMost (1 / 2 : ℝ)) :
    SquareRootAmplificationZeroLogGrowthStatement := by
  change Tendsto squareRootAmplificationLogRatio atTop (nhds (0 : ℝ))
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with X hX
    exact lt_of_lt_of_le ha (squareRootAmplificationLogRatio_nonneg hX)
  · intro b hb
    obtain ⟨C, hC, hbound⟩ := hgrowth (b / 8) (by linarith)
    have hInteger : ∀ n : ℕ, 1 ≤ n →
        |(mertensSummatoryInt n : ℝ)| ≤
          C * (n : ℝ) ^ ((1 : ℝ) / 2 + b / 8) := by
      intro n hn
      have h := hbound n hn
      rw [← mertensSummatoryInt_cast n, Complex.norm_intCast] at h
      exact h
    have hevent := squareRootAmplificationLogRatio_eventually_le_of_mertensPower
      (by linarith : (1 / 2 : ℝ) ≤ (1 / 2 : ℝ) + b / 8)
      hC hInteger (b / 4) (by linarith)
    filter_upwards [hevent] with X hX
    linarith only [hX, hb]

/-- Zero logarithmic growth supplies the exact square-root-history source
bound needed by the arithmetic zero-boundary consumer. -/
theorem mertens_half_of_zeroLog
    (hzero : SquareRootAmplificationZeroLogGrowthStatement) :
    MertensGrowthAtMost (1 / 2 : ℝ) := by
  have hboundary := rightmost_le_of_envelopeBound
    (lam := 1) (eta := 0) (by norm_num) (by norm_num) (by norm_num)
    (envelopeBound_one_zero_of_zeroLog hzero)
  apply (growthAtMost_iff_rightmost_le (by norm_num : (0 : ℝ) ≤ 1 / 2)).mpr
  simpa only [zero_div, add_zero] using hboundary

/-- The literal original zero-log target is exactly the critical Mertens
growth statement.  Uniform finite amplification remains a separate target. -/
theorem zeroLog_iff_mertens_half :
    SquareRootAmplificationZeroLogGrowthStatement ↔
      MertensGrowthAtMost (1 / 2 : ℝ) :=
  ⟨mertens_half_of_zeroLog, zeroLog_of_mertens_half⟩

/-- Critical-zero formulation through the existing analytic identification. -/
theorem zeroLog_iff_criticalZeros :
    SquareRootAmplificationZeroLogGrowthStatement ↔
      ∀ ρ : ℂ, NontrivialZetaZero ρ → ρ.re = (1 / 2 : ℝ) :=
  zeroLog_iff_mertens_half.trans growthAtMost_half_iff_criticalZeros

end RHLean.Analysis.UniversalEnvelope

end
