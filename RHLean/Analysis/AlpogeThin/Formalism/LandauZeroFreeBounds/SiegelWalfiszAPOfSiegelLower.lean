import RHLean.Analysis.AlpogeThin.Formalism.LandauZeroFreeBounds.NoZeroComplex
import RHLean.Analysis.AlpogeThin.Formalism.LandauZeroFreeBounds.FinalSiegel
import RHLean.Analysis.AlpogeThin.Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LandauLocal3
import RHLean.Analysis.AlpogeThin.Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.PerronChi
import RHLean.Analysis.AlpogeThin.Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.RectShiftChi
import RHLean.Analysis.AlpogeThin.Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LogDerivRegionChiOf
import RHLean.Analysis.AlpogeThin.Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.SmoothChiOf
import RHLean.Analysis.AlpogeThin.Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.PsiChiBoundOf
import RHLean.Analysis.AlpogeThin.Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LDerivNearOne
import RHLean.Analysis.AlpogeThin.Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.ExcBoundOf
import RHLean.Analysis.AlpogeThin.Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.SiegelWalfiszOf
import RHLean.Analysis.AlpogeThin.Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.SiegelWalfiszAPOf
import RHLean.Analysis.AlpogeThin.Formalism.ZeroFreeRegion.LogDerivRegion

/-!
# Reconstructed same-host thin-source dependency

Mathematical source: Levent Alpöge (with Claude).
Source: src/Formalism/LandauZeroFreeBounds/SiegelWalfiszAPOfSiegelLower.lean.
Pinned source: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/LandauZeroFreeBounds/SiegelWalfiszAPOfSiegelLower.lean

This local proof reconstruction adapts the module/namespace boundary to native
RH_Lean. No upstream compiled artifact or terminal RH theorem is imported.
The source archive/mirror states no license; this notice preserves attribution
without assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace RHLean.Analysis.AlpogeThin

namespace Formalism.ZeroFreeDirichlet

theorem logDerivRegionChi : LogDerivRegionChi :=
  log_deriv_in_zero_free_region landau_local3 lfunction_polynomial_growth inverseBound l_log_deriv_right

theorem smoothChi : SmoothChi :=
  smoothed_character_sum_of perron_formula_character rectangle_contour_shift_character logDerivRegionChi l_log_deriv_right

theorem psiChiBound : PsiChiBound :=
  chebyshev_character_bound_of smoothChi Formalism.ZF.gzPNT

theorem excBound_of_siegelLower (hS : SiegelLower) : ExcBound :=
  exceptional_zero_bound_of hS lfunction_deriv_near_one

theorem siegelWalfisz_of_siegelLower (hS : SiegelLower) : SiegelWalfisz :=
  siegel_walfisz_character_of psiChiBound zFRDirichlet (excBound_of_siegelLower hS)

theorem excBound : ExcBound := excBound_of_siegelLower siegelLower

theorem siegelWalfisz : SiegelWalfisz := siegelWalfisz_of_siegelLower siegelLower

end Formalism.ZeroFreeDirichlet

end RHLean.Analysis.AlpogeThin
