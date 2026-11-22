import RHLean.Analysis.AlpogeThin.Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.DHFinish2Of
import RHLean.Analysis.AlpogeThin.Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Turan2Main

/-!
# Reconstructed same-host thin-source dependency

Mathematical source: Levent Alpöge (with Claude).
Source: src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TuranPowerSumBound.lean.
Pinned source: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TuranPowerSumBound.lean

This local proof reconstruction adapts the module/namespace boundary to native
RH_Lean. No upstream compiled artifact or terminal RH theorem is imported.
The source archive/mirror states no license; this notice preserves attribution
without assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace RHLean.Analysis.AlpogeThin

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

theorem turan_power_sum_bound : DHTuran2 := by
  refine ⟨1600, 1, by norm_num, le_rfl, fun n m z hn hz hz1 => ?_⟩
  obtain ⟨k, h1, h2, h3⟩ := T2.turan2Main n m z hn hz hz1
  exact ⟨k, h1, by simpa using h2, by simpa using h3⟩

end Formalism.HermitianLattices.Ext.PrimesInProgressions

end RHLean.Analysis.AlpogeThin
