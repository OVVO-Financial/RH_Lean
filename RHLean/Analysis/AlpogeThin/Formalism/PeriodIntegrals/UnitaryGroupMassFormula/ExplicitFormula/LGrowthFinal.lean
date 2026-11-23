import RHLean.Analysis.AlpogeThin.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LGrowthMain
import RHLean.Analysis.AlpogeThin.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LGrowthZeta

/-!
# Reconstructed same-host thin-source dependency

Mathematical source: Levent Alpöge (with Claude).
Source: src/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LGrowthFinal.lean.
Pinned source: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LGrowthFinal.lean

This local proof reconstruction adapts the module/namespace boundary to native
RH_Lean. No upstream compiled artifact or terminal RH theorem is imported.
The source archive/mirror states no license; this notice preserves attribution
without assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace RHLean.Analysis.AlpogeThin

namespace PI.EF

theorem lGrowth_of_right (hB : PI.LBoundRight) (hZ : PI.ZetaBoundRight) : LGrowth 7 300000 := by
  have h := lGrowth_of hB (zetaGrowth_of hZ)
  have hm : max (300000 : ℝ) 53946 = 300000 := by norm_num
  rwa [hm] at h

end PI.EF

end RHLean.Analysis.AlpogeThin
