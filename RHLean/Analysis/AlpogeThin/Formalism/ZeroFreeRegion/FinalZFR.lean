import RHLean.Analysis.AlpogeThin.Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.LogDerivBound
import RHLean.Analysis.AlpogeThin.Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZeroFactor
import RHLean.Analysis.AlpogeThin.Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.LandauLocalOf
import RHLean.Analysis.AlpogeThin.Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ThreeFourOne
import RHLean.Analysis.AlpogeThin.Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.LogDerivRight
import RHLean.Analysis.AlpogeThin.Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZetaGrowth
import RHLean.Analysis.AlpogeThin.Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZetaInvBound
import RHLean.Analysis.AlpogeThin.Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.SmallHeight
import RHLean.Analysis.AlpogeThin.Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZeroFreeOf

/-!
# Reconstructed same-host thin-source dependency

Mathematical source: Levent Alpöge (with Claude).
Source: src/Formalism/ZeroFreeRegion/FinalZFR.lean.
Pinned source: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/ZeroFreeRegion/FinalZFR.lean

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

theorem landauLocal : LandauLocal := localZeroExpansionOfFactorization zeroFactorization logDerivBoundOnBall

theorem zeroFreeRegion : ZeroFreeRegion :=
  classicalZeroFreeRegionOfBounds mertensInequality logDerivBoundRightHalfPlane growthBound zetaInvBound_statement
    zeroFreeBoundedHeight landauLocal

end Formalism.ZF

end RHLean.Analysis.AlpogeThin
