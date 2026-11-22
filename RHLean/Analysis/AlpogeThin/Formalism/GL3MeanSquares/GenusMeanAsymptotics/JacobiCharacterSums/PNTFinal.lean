import RHLean.Analysis.AlpogeThin.Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTRangeA
import RHLean.Analysis.AlpogeThin.Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTGlue
import RHLean.Analysis.AlpogeThin.Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PrimeCountOfPsi
import RHLean.Analysis.AlpogeThin.Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTSharp
import RHLean.Analysis.AlpogeThin.Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTBAsm
import RHLean.Analysis.AlpogeThin.Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTZSum
import RHLean.Analysis.AlpogeThin.Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDens
import RHLean.Analysis.AlpogeThin.Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplMain
import RHLean.Analysis.AlpogeThin.Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTZSumL
import RHLean.Analysis.AlpogeThin.Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHB

/-!
# Reconstructed same-host thin-source dependency

Mathematical source: Levent Alpöge (with Claude).
Source: src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTFinal.lean.
Pinned source: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTFinal.lean

This local proof reconstruction adapts the module/namespace boundary to native
RH_Lean. No upstream compiled artifact or terminal RH theorem is imported.
The source archive/mirror states no license; this notice preserves attribution
without assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace RHLean.Analysis.AlpogeThin

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

theorem explicitS_proof' : ExplicitS := smoothed_explicit_formula

theorem logDensityM_proof' : LogDensityM := Dens.log_density_bound

theorem deuringHeilbronnMB_proof' : DeuringHeilbronnMB := deuring_heilbronn_lossy

theorem pnt_progressions_relative_weak_holds : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.PNTAPRelW :=
  prime_count_of_psi (glue_ranges psi_relative_near_range
    (psi_relative_far_range explicitS_proof' differenced_explicit_formula (zero_sum_bound_lossy logDensityM_proof' deuringHeilbronnMB_proof')))

end Formalism.HermitianLattices.Ext.PrimesInProgressions

end

end RHLean.Analysis.AlpogeThin
