import RHLean.Analysis.AlpogeThin.Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.CharExists
import RHLean.Analysis.AlpogeThin.Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.BqCoeff
import RHLean.Analysis.AlpogeThin.Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.BqEntire
import RHLean.Analysis.AlpogeThin.Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.BqGrowth
import RHLean.Analysis.AlpogeThin.Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LFunctionOneUpperBound
import RHLean.Analysis.AlpogeThin.Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.BqKeyOf
import RHLean.Analysis.AlpogeThin.Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.ZetaNegReal
import RHLean.Analysis.AlpogeThin.Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LRealPos
import RHLean.Analysis.AlpogeThin.Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.SameCharacterLFunctionOne
import RHLean.Analysis.AlpogeThin.Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.SiegelOf

/-!
# Reconstructed same-host thin-source dependency

Mathematical source: Levent Alpöge (with Claude).
Source: src/Formalism/LandauZeroFreeBounds/FinalSiegel.lean.
Pinned source: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/LandauZeroFreeBounds/FinalSiegel.lean

This local proof reconstruction adapts the module/namespace boundary to native
RH_Lean. No upstream compiled artifact or terminal RH theorem is imported.
The source archive/mirror states no license; this notice preserves attribution
without assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace RHLean.Analysis.AlpogeThin

namespace Formalism.ZeroFreeDirichlet

theorem bqKey : BqKey :=
  product_lfunction_key_inequality dirichlet_product_coefficients dirichlet_product_entire product_lfunction_growth_bound lfunction_one_upper_bound

theorem siegelLower : SiegelLower :=
  siegel_theorem_of exists_product_character exists_real_nontrivial_character bqKey lfunction_one_upper_bound zeta_negative_real_axis
    real_lfunction_real_on_reals lfunction_one_same_character

end Formalism.ZeroFreeDirichlet

end RHLean.Analysis.AlpogeThin
