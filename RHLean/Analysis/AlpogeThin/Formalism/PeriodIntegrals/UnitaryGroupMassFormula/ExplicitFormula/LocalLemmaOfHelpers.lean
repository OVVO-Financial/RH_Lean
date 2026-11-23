import Mathlib
import RHLean.Analysis.AlpogeThin.Formalism.PeriodIntegrals.DiscIn
import RHLean.Analysis.AlpogeThin.Formalism.PeriodIntegrals.ZerosWindowIn
import RHLean.Analysis.AlpogeThin.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.Assemble
import RHLean.Analysis.AlpogeThin.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.PerronGlue
import RHLean.Analysis.AlpogeThin.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LocalProofs
import RHLean.Analysis.AlpogeThin.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LogWindowLe
import RHLean.Analysis.AlpogeThin.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LGrowthFinal

/-!
# Reconstructed same-host thin-source dependency

Mathematical source: Levent Alpöge (with Claude).
Source: src/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LocalLemmaOfHelpers.lean.
Pinned source: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LocalLemmaOfHelpers.lean

This local proof reconstruction adapts the module/namespace boundary to native
RH_Lean. No upstream compiled artifact or terminal RH theorem is imported.
The source archive/mirror states no license; this notice preserves attribution
without assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace RHLean.Analysis.AlpogeThin

noncomputable section

namespace PI.EF

theorem localLemma_of_helpers (hZW : PI.ZerosWindow) (hDF : PI.DiscFactor) (hDL : PI.DiscLog)
    (hLB : PI.LBoundRight) (hZB : PI.ZetaBoundRight) (hLI : PI.LInvRight) :
    ∃ C, 0 < C ∧ LocalLemma C :=
  localLemma_of hLI (localAbstract_of hDF hDL)
    ⟨7, max 300000 53946, by norm_num, lt_max_of_lt_left (by norm_num),
      lGrowth_of hLB (zetaGrowth_of hZB)⟩ zeroLocus hZW

theorem explicitFormula_main (hZW : PI.ZerosWindow) (hDF : PI.DiscFactor) (hDL : PI.DiscLog)
    (hLB : PI.LBoundRight) (hZB : PI.ZetaBoundRight) (hLI : PI.LInvRight) : PI.ExplicitFormula :=
  explicitFormula_of_local hZW (localLemma_of_helpers hZW hDF hDL hLB hZB hLI) perron_gluing_sides

end PI.EF

end

end RHLean.Analysis.AlpogeThin
