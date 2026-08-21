import RHLean.Analysis.K2RecipMomentAnalyticClosure

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

end RHLean.Analysis
