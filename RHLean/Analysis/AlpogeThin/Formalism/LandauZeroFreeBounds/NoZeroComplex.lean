import RHLean.Analysis.AlpogeThin.Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LocalZeroExpansionWithMultiplicity
import RHLean.Analysis.AlpogeThin.Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LGrowth
import RHLean.Analysis.AlpogeThin.Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LRight
import RHLean.Analysis.AlpogeThin.Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Positivity
import RHLean.Analysis.AlpogeThin.Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.TrivLogDeriv
import RHLean.Analysis.AlpogeThin.Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.TrivReal
import RHLean.Analysis.AlpogeThin.Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LocalZerosOf
import RHLean.Analysis.AlpogeThin.Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.NoZeroComplexOf
import RHLean.Analysis.AlpogeThin.Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.RealLargeTOf
import RHLean.Analysis.AlpogeThin.Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.RealSmallTOf
import RHLean.Analysis.AlpogeThin.Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.TwoRealOf
import RHLean.Analysis.AlpogeThin.Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.ZFRDirichletOf
import RHLean.Analysis.AlpogeThin.Formalism.ZeroFreeRegion.FinalZFR

/-!
# Reconstructed same-host thin-source dependency

Mathematical source: Levent Alpöge (with Claude).
Source: src/Formalism/LandauZeroFreeBounds/NoZeroComplex.lean.
Pinned source: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/LandauZeroFreeBounds/NoZeroComplex.lean

This local proof reconstruction adapts the module/namespace boundary to native
RH_Lean. No upstream compiled artifact or terminal RH theorem is imported.
The source archive/mirror states no license; this notice preserves attribution
without assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace RHLean.Analysis.AlpogeThin

namespace Formalism.ZeroFreeDirichlet

theorem localZeros : LocalZeros :=
  localZeroSumBoundOfBounds localZeroExpansionWithMultiplicity lfunction_polynomial_growth inverseBound

theorem noZeroComplex : NoZeroComplex :=
  zeroFreeNonRealCharOfBounds localZeros l_log_deriv_right negLogDerivPositivity

theorem realLargeT : RealLargeT :=
  realCharZeroFreeLargeHeightOfBounds localZeros l_log_deriv_right negLogDerivPositivity trivial_log_deriv_bound

theorem realSmallT : RealSmallT :=
  realCharZeroSmallHeightOfBounds localZeros l_log_deriv_right negLogDerivPositivity realCharConj

theorem twoReal : TwoReal :=
  twoRealCharNoCommonZeroOfBounds localZeros l_log_deriv_right negLogDerivPositivity

theorem zFRDirichlet : ZFRDirichlet :=
  zeroFreeRegionExceptionalZeroOfBounds Formalism.ZF.zeroFreeRegion trivialCharZerosOfZeta noZeroComplex realLargeT realSmallT twoReal

end Formalism.ZeroFreeDirichlet

end RHLean.Analysis.AlpogeThin
