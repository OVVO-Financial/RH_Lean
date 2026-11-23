import RHLean.Analysis.AlpogeThin.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.GoodHeightExists
import RHLean.Analysis.AlpogeThin.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LocalAbstract

/-!
# Reconstructed same-host thin-source dependency

Mathematical source: Levent Alpöge (with Claude).
Source: src/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LocalProofs.lean.
Pinned source: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LocalProofs.lean

This local proof reconstruction adapts the module/namespace boundary to native
RH_Lean. No upstream compiled artifact or terminal RH theorem is imported.
The source archive/mirror states no license; this notice preserves attribution
without assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace RHLean.Analysis.AlpogeThin

namespace PI.EF

theorem localAbstract_of (hDF : PI.DiscFactor) (hDL : PI.DiscLog) : LocalAbstract := by
  intro r R' R hr hrR' hR'R
  exact ⟨Loc.locC r R' R, Loc.locC_pos hr hrR' hR'R, fun f s₀ M hf hf0 hM hb =>
    Loc.local_abstract hDF hDL hr hrR' hR'R f s₀ M hf hf0 hM hb⟩

end PI.EF

end RHLean.Analysis.AlpogeThin
