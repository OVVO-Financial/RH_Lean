import Mathlib
import RHLean.Analysis.AlpogeThin.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.ExplicitFormulaFromGluing
import RHLean.Analysis.AlpogeThin.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.PerronKernelB
import RHLean.Analysis.AlpogeThin.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.PerronLOf
import RHLean.Analysis.AlpogeThin.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.ContinuousInvSqrt

/-!
# Reconstructed same-host thin-source dependency

Mathematical source: Levent Alpöge (with Claude).
Source: src/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronGlue.lean.
Pinned source: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronGlue.lean

This local proof reconstruction adapts the module/namespace boundary to native
RH_Lean. No upstream compiled artifact or terminal RH theorem is imported.
The source archive/mirror states no license; this notice preserves attribution
without assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace RHLean.Analysis.AlpogeThin

namespace PI.EF

theorem perron_gluing_sides : GlueSides := by
  rintro κ _ ⟨C1, hC1, hH⟩ ⟨C2, hC2, hL⟩
  exact ⟨21 * C1 + 8 * C2, by positivity, PK.sidesBound_of hC1.le hC2.le hH hL⟩

end PI.EF

end RHLean.Analysis.AlpogeThin
