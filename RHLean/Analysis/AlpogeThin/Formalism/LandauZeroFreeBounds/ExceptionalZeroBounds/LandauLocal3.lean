import RHLean.Analysis.AlpogeThin.Formalism.LandauZeroFreeBounds.LogDerivRegionChiOf
import RHLean.Analysis.AlpogeThin.Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.ExistsLocalZeroExpansionOfBound

/-!
# Reconstructed same-host thin-source dependency

Mathematical source: Levent Alpöge (with Claude).
Source: src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LandauLocal3.lean.
Pinned source: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LandauLocal3.lean

This local proof reconstruction adapts the module/namespace boundary to native
RH_Lean. No upstream compiled artifact or terminal RH theorem is imported.
The source archive/mirror states no license; this notice preserves attribution
without assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace RHLean.Analysis.AlpogeThin

noncomputable section

namespace Formalism.ZeroFreeDirichlet

theorem landau_local3 : LandauLocal3 :=
  fun f z₀ r M hr hM hf hfz₀ hbound => exists_localZeroExpansion_of_bound f z₀ r M hr hM hf hfz₀ hbound

end Formalism.ZeroFreeDirichlet

end

end RHLean.Analysis.AlpogeThin
