import RHLean.Analysis.AlpogeThin.Formalism.LandauZeroFreeBounds.NoZeroComplexOf
import RHLean.Analysis.AlpogeThin.Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.EulerFactorLogDerivBound
import RHLean.Analysis.AlpogeThin.Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.ZetaLogDerivLandauBound

/-!
# Reconstructed same-host thin-source dependency

Mathematical source: Levent Alpöge (with Claude).
Source: src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/TrivLogDeriv.lean.
Pinned source: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/TrivLogDeriv.lean

This local proof reconstruction adapts the module/namespace boundary to native
RH_Lean. No upstream compiled artifact or terminal RH theorem is imported.
The source archive/mirror states no license; this notice preserves attribution
without assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace RHLean.Analysis.AlpogeThin

open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

theorem trivial_log_deriv_bound : TrivLogDeriv := by
  obtain ⟨K, hK0, hK⟩ := zeta_neg_log_deriv_re_bound
  refine ⟨K + 1, fun q _ σ t hσ hσ2 => ?_⟩
  have hs : 1 < ((σ : ℂ) + t * I).re := by simpa using hσ
  have h1 := re_negLogDeriv_le q ((σ : ℂ) + t * I) hs
  have h2 := hK σ t hσ hσ2
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq
  have hT : 0 ≤ Real.log (|t| + 2) := Real.log_nonneg (by linarith [abs_nonneg t])
  have hlog : Real.log ((q : ℝ) * (|t| + 2)) = Real.log q + Real.log (|t| + 2) :=
    Real.log_mul (by linarith : (0 : ℝ) < q).ne' (by linarith [abs_nonneg t] : (0 : ℝ) < |t| + 2).ne'
  rw [hlog]
  nlinarith [mul_nonneg hK0 hlq]

end Formalism.ZeroFreeDirichlet

end

end RHLean.Analysis.AlpogeThin
