import RHLean.Analysis.AlpogeThin.Formalism.ZeroFreeRegion.FinalZFR
import RHLean.Analysis.AlpogeThin.Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.SmallHeightLogDeriv
import RHLean.Analysis.AlpogeThin.Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.LogDerivRegionOf
import RHLean.Analysis.AlpogeThin.Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.Perron
import RHLean.Analysis.AlpogeThin.Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.RectDoublePole
import RHLean.Analysis.AlpogeThin.Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.LaurentAtOne
import RHLean.Analysis.AlpogeThin.Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.RectShiftOf
import RHLean.Analysis.AlpogeThin.Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.GzPNTOf

/-!
# Reconstructed same-host thin-source dependency

Mathematical source: Levent Alpöge (with Claude).
Source: src/Formalism/ZeroFreeRegion/LogDerivRegion.lean.
Pinned source: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/ZeroFreeRegion/LogDerivRegion.lean

This local proof reconstruction adapts the module/namespace boundary to native
RH_Lean. No upstream compiled artifact or terminal RH theorem is imported.
The source archive/mirror states no license; this notice preserves attribution
without assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace RHLean.Analysis.AlpogeThin

noncomputable section

namespace Formalism.ZF

theorem logDerivRegion : LogDerivRegion :=
  logDerivBoundInRegionOfBounds zeroFreeRegion logDerivBoundRightHalfPlane growthBound zetaInvBound_statement
    logDerivBoundedHeight landauLocal

theorem rectShift : RectShift := rectangleShiftOfResidue rectangle_double_pole laurentExpansionAtOne

theorem gzPNT : GzPNT :=
  zetaPrimeSumErrorBoundOfBounds zeroFreeRegion logDerivRegion logDerivBoundRightHalfPlane perron_formula rectShift

end Formalism.ZF

end

end RHLean.Analysis.AlpogeThin
