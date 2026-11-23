import RHLean.Analysis.AlpogeThin.Formalism.PeriodIntegrals.ExplicitFormulaCounts.AnalyticInputs
import RHLean.Analysis.AlpogeThin.Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ZerosWindow
import RHLean.Analysis.AlpogeThin.Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ExplicitFormula

/-!
# Reconstructed same-host thin-source dependency

Mathematical source: Levent Alpöge (with Claude).
Source: src/Formalism/PeriodIntegrals/ExplicitFormulaCounts/ExplicitFormula.lean.
Pinned source: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/PeriodIntegrals/ExplicitFormulaCounts/ExplicitFormula.lean

This local proof reconstruction adapts the module/namespace boundary to native
RH_Lean. No upstream compiled artifact or terminal RH theorem is imported.
The source archive/mirror states no license; this notice preserves attribution
without assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace RHLean.Analysis.AlpogeThin

theorem zerosWindow_closed : PI.ZerosWindow :=
  zerosWindow_of chk_lBoundRight chk_zetaBoundRight chk_lInvRight

theorem explicitFormula_closed : PI.ExplicitFormula :=
  explicitFormula_of zerosWindow_closed chk_discFactor chk_discLog chk_lBoundRight chk_zetaBoundRight
    chk_lInvRight

end RHLean.Analysis.AlpogeThin
