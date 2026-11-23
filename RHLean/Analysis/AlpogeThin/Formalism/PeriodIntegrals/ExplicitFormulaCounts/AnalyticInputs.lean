import RHLean.Analysis.AlpogeThin.Formalism.PeriodIntegrals.DiscIn
import RHLean.Analysis.AlpogeThin.Formalism.PeriodIntegrals.ZerosWindowIn
import RHLean.Analysis.AlpogeThin.Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LandauLocal3
import RHLean.Analysis.AlpogeThin.Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LGrowth
import RHLean.Analysis.AlpogeThin.Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LRight
import RHLean.Analysis.AlpogeThin.Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZetaGrowth

/-!
# Reconstructed same-host thin-source dependency

Mathematical source: Levent Alpöge (with Claude).
Source: src/Formalism/PeriodIntegrals/ExplicitFormulaCounts/AnalyticInputs.lean.
Pinned source: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/PeriodIntegrals/ExplicitFormulaCounts/AnalyticInputs.lean

This local proof reconstruction adapts the module/namespace boundary to native
RH_Lean. No upstream compiled artifact or terminal RH theorem is imported.
The source archive/mirror states no license; this notice preserves attribution
without assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace RHLean.Analysis.AlpogeThin

theorem chk_discFactor : PI.DiscFactor := Formalism.ZF.zeroFactorization
theorem chk_discLog : PI.DiscLog := fun _ _ _ hf hne => Formalism.ZF.zflb_exists_log hf hne

theorem chk_zetaBoundRight : PI.ZetaBoundRight := Formalism.ZF.growthBound

theorem chk_lInvRight : PI.LInvRight := Formalism.ZeroFreeDirichlet.inverseBound

theorem chk_lBoundRight : PI.LBoundRight := by
  intro q _ χ hχ s hs
  have h := Formalism.FX.l_function_partial_sum q χ hχ ((q : ℝ) + 1)
    (fun M => Formalism.ZeroFreeDirichlet.norm_character_sum_Icc_le χ hχ M) s hs 1 le_rfl
  simp only [Finset.Icc_self, Finset.sum_singleton, Nat.cast_one, map_one, Complex.one_cpow, mul_one,
    Real.one_rpow] at h
  calc ‖DirichletCharacter.LFunction χ s‖
      = ‖(1 : ℂ) + (DirichletCharacter.LFunction χ s - 1)‖ := by congr 1; ring
    _ ≤ ‖(1 : ℂ)‖ + ‖DirichletCharacter.LFunction χ s - 1‖ := norm_add_le _ _
    _ ≤ 1 + 2 * ((q : ℝ) + 1) * (1 + ‖s‖ / s.re) := by rw [norm_one]; linarith

end RHLean.Analysis.AlpogeThin
