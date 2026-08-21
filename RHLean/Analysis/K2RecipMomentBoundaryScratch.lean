import RHLean.Analysis.K2RecipMomentAnalyticClosure
import RHLean.Analysis.StrongMertensLogNineBalance

noncomputable section

open Filter Set Topology
open scoped ArithmeticFunction.Moebius LSeries.notation

namespace RHLean.Analysis

local notation "gammaE" => Real.eulerMascheroniConstant

/-- The log-square Mobius L-series has the reciprocal-zeta boundary value from
the right of `1`. -/
theorem k2MobiusLogSqLSeries_tendsto_right_one :
    Tendsto
      (fun sigma : ℝ =>
        LSeries (LSeries.logMul^[2] (fun n : ℕ => (μ n : ℂ))) (sigma : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (-2 * gammaE : ℂ)) := by
  have hcomplex :
      Tendsto (fun s : ℂ => iteratedDeriv 2 k2InvZetaRegular s)
        (𝓝 (1 : ℂ)) (𝓝 (-2 * gammaE : ℂ)) := by
    have h := (k2InvZetaRegular_analyticAt_one.iterated_deriv 2).continuousAt.tendsto
    simpa [k2InvZetaRegular_iteratedDeriv_two] using h
  have hreal :
      Tendsto (fun sigma : ℝ => (sigma : ℂ))
        (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) := by
    exact tendsto_nhdsWithin_of_tendsto_nhds
      RCLike.continuous_ofReal.continuousAt.tendsto
  apply (hcomplex.comp hreal).congr'
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  have hs : 1 < sigma := by simpa using hsigma
  exact (k2InvZetaRegular_iteratedDeriv_two_eq_moebiusLogSqLSeries
    (s := (sigma : ℂ)) (by simpa using hs)).symm

/-- Strong Mertens kills every fixed logarithmic reciprocal endpoint.  This is
the endpoint term in Abel summation for the order-two and order-three K2
moments. -/
theorem k2StrongMertens_logRecip_endpoint_tendsto_zero (m : ℕ) :
    Tendsto
      (fun N : ℕ => nativeMertensSummatory N * k2LogRecipWeight m N)
      atTop (𝓝 0) := by
  obtain ⟨c, C, hc, hC, hM⟩ := strongNativeMertensSubexp
  have hpolyexp :
      Tendsto (fun r : ℝ => r ^ (10 * m) * Real.exp (-c * r)) atTop (𝓝 0) := by
    have h := (isLittleO_pow_exp_pos_mul_atTop (10 * m) hc).tendsto_div_nhds_zero
    refine h.congr' ?_
    filter_upwards with r
    rw [div_eq_mul_inv, ← Real.exp_neg]
    ring_nf
  have hscaleN :
      Tendsto (fun N : ℕ => strongMertensScale (N : ℝ)) atTop atTop :=
    strongMertensScale_tendsto_atTop.comp tendsto_natCast_atTop_atTop
  have hmajor :
      Tendsto
        (fun N : ℕ =>
          C * (strongMertensScale (N : ℝ) ^ (10 * m) *
            Real.exp (-c * strongMertensScale (N : ℝ))))
        atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (hpolyexp.comp hscaleN)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_ hmajor
  filter_upwards [eventually_ge_atTop 3] with N hN
  have hNposNat : 0 < N := by omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNposNat
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNposNat
  have hlognonneg : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hw_nonneg : 0 ≤ k2LogRecipWeight m N := by
    unfold k2LogRecipWeight
    positivity
  have hlogpow :
      (Real.log (N : ℝ)) ^ m =
        strongMertensScale (N : ℝ) ^ (10 * m) := by
    have hs := strongMertensScale_pow_ten (X := (N : ℝ)) hN1
    calc
      (Real.log (N : ℝ)) ^ m = (strongMertensScale (N : ℝ) ^ 10) ^ m := by rw [hs]
      _ = strongMertensScale (N : ℝ) ^ (10 * m) := (pow_mul _ _ _).symm
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw_nonneg]
  calc
    |nativeMertensSummatory N| * k2LogRecipWeight m N
        ≤ (C * (N : ℝ) *
            Real.exp (-c * strongMertensScale (N : ℝ))) *
          k2LogRecipWeight m N :=
      mul_le_mul_of_nonneg_right (hM N hN) hw_nonneg
    _ = C * (Real.log (N : ℝ)) ^ m *
        Real.exp (-c * strongMertensScale (N : ℝ)) := by
      unfold k2LogRecipWeight
      field_simp [ne_of_gt hNpos]
      ring
    _ = C * (strongMertensScale (N : ℝ) ^ (10 * m) *
        Real.exp (-c * strongMertensScale (N : ℝ))) := by
      rw [hlogpow]
      ring

end RHLean.Analysis
