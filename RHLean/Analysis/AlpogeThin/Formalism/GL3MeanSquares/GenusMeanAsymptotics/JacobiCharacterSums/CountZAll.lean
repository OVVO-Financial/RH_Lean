import RHLean.Analysis.AlpogeThin.Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZDual
import RHLean.Analysis.AlpogeThin.Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZTwist
import RHLean.Analysis.AlpogeThin.Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZMoll
import RHLean.Analysis.AlpogeThin.Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZBlock
import RHLean.Analysis.AlpogeThin.Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZDetect
import RHLean.Analysis.AlpogeThin.Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZFinal
import RHLean.Analysis.AlpogeThin.Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZNum
import RHLean.Analysis.AlpogeThin.Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZPair
import RHLean.Analysis.AlpogeThin.Formalism.LFunctionBounds.LFunctionBoundsProofs.DivisorBound

/-!
# Reconstructed same-host thin-source dependency

Mathematical source: Levent Alpöge (with Claude).
Source: src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZAll.lean.
Pinned source: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZAll.lean

This local proof reconstruction adapts the module/namespace boundary to native
RH_Lean. No upstream compiled artifact or terminal RH theorem is imported.
The source archive/mirror states no license; this notice preserves attribution
without assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace RHLean.Analysis.AlpogeThin

namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD

theorem zero_density_box : Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZeroDensityBox :=
  final_bound_of_assembly (coefficient_square_bound Formalism.FX.divisor_weight_bound) (zero_detection mollifier_identity)
    (blockCountOf_statement duality_inequality (pair_twist_bound pair_sum_bound)) numeric_constants

end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD

end RHLean.Analysis.AlpogeThin
