import RHLean.Analysis.AlpogeThin.Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHPos
import RHLean.Analysis.AlpogeThin.Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHCauchy
import RHLean.Analysis.AlpogeThin.Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHLocal
import RHLean.Analysis.AlpogeThin.Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.TuranPowerSumBound
import RHLean.Analysis.AlpogeThin.Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHDom
import RHLean.Analysis.AlpogeThin.Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHIneqF
import RHLean.Analysis.AlpogeThin.Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHHyper
import RHLean.Analysis.AlpogeThin.Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHPrime
import RHLean.Analysis.AlpogeThin.Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.DeuringHeilbronnFinishTuran

/-!
# Reconstructed same-host thin-source dependency

Mathematical source: Levent Alpöge (with Claude).
Source: src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHB.lean.
Pinned source: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHB.lean

This local proof reconstruction adapts the module/namespace boundary to native
RH_Lean. No upstream compiled artifact or terminal RH theorem is imported.
The source archive/mirror states no license; this notice preserves attribution
without assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace RHLean.Analysis.AlpogeThin

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

theorem deuring_heilbronn_lossy : DeuringHeilbronnMB :=
  deuring_heilbronn_finish_turan turan_power_sum_bound (deuring_heilbronn_inequality deuring_heilbronn_positivity (deuring_heilbronn_local deuring_heilbronn_cauchy) deuring_heilbronn_dominant)
    (deuring_heilbronn_prime_sum deuring_heilbronn_hypergeometric)

end Formalism.HermitianLattices.Ext.PrimesInProgressions

end RHLean.Analysis.AlpogeThin
