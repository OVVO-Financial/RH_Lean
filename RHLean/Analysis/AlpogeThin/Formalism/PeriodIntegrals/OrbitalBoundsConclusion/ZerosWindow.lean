import Mathlib
import RHLean.Analysis.AlpogeThin.Formalism.PeriodIntegrals.ZerosWindow
import RHLean.Analysis.AlpogeThin.Formalism.PeriodIntegrals.ZerosWindowIn
import RHLean.Analysis.AlpogeThin.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ZeroWindow.Assemble
import RHLean.Analysis.AlpogeThin.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ZeroWindow.Transfer

/-!
# Reconstructed same-host thin-source dependency

Mathematical source: Levent Alpöge (with Claude).
Source: src/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/ZerosWindow.lean.
Pinned source: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/ZerosWindow.lean

This local proof reconstruction adapts the module/namespace boundary to native
RH_Lean. No upstream compiled artifact or terminal RH theorem is imported.
The source archive/mirror states no license; this notice preserves attribution
without assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace RHLean.Analysis.AlpogeThin

theorem zerosWindow_of : PI.LBoundRight → PI.ZetaBoundRight → PI.LInvRight → PI.ZerosWindow :=
  fun hL hZ hI => PI.ZW.zerosWindow_of_transfer PI.ZW.transfer hL hZ hI

end RHLean.Analysis.AlpogeThin
