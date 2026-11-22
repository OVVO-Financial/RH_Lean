import Mathlib
import RHLean.Analysis.AlpogeThin.Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions

/-!
# Reconstructed same-host thin-source dependency

Mathematical source: Levent Alpöge (with Claude).
Source: src/Formalism/GL3MeanSquares/HookFormulaTorsion/SizeEstimates.lean.
Pinned source: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/GL3MeanSquares/HookFormulaTorsion/SizeEstimates.lean

This local proof reconstruction adapts the module/namespace boundary to native
RH_Lean. No upstream compiled artifact or terminal RH theorem is imported.
The source archive/mirror states no license; this notice preserves attribution
without assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace RHLean.Analysis.AlpogeThin

open Finset Filter Topology ArithmeticFunction

noncomputable section

namespace Formalism.HermitianLattices.P.JacobiSumIdentities

private def jHom (q : ℕ) : ℤ →* ℤ where
  toFun a := jacobiSym a q
  map_one' := jacobiSym.one_left q
  map_mul' a b := jacobiSym.mul_left a b q

private lemma cn_nonneg (x : ℝ) (hx : 0 ≤ x) (n : ℕ) : 0 ≤ Formalism.HermitianLattices.GL2PrimeSums.cn x n := by
  unfold Formalism.HermitianLattices.GL2PrimeSums.cn
  exact mul_nonneg vonMangoldt_nonneg (le_min zero_le_one (div_nonneg hx (Nat.cast_nonneg n)))

private lemma sP_nonneg (x : ℝ) (hx : 0 ≤ x) (p : ℕ) : 0 ≤ Formalism.HermitianLattices.GL2a2.sP x p := by
  unfold Formalism.HermitianLattices.GL2a2.sP
  exact Finset.sum_nonneg (fun i _ => cn_nonneg x hx _)

end Formalism.HermitianLattices.P.JacobiSumIdentities

end RHLean.Analysis.AlpogeThin
