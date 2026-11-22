import Mathlib
import RHLean.Analysis.AlpogeThin.Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.DeuringHeilbronnM

/-!
# Reconstructed same-host thin-source dependency

Mathematical source: Levent Alpöge (with Claude).
Source: src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplDefs.lean.
Pinned source: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplDefs.lean

This local proof reconstruction adapts the module/namespace boundary to native
RH_Lean. No upstream compiled artifact or terminal RH theorem is imported.
The source archive/mirror states no license; this notice preserves attribution
without assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace RHLean.Analysis.AlpogeThin

open Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.ZeroFreeDirichlet

def exLF {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) : ℂ → ℂ :=
  if χ = 1 then DirichletCharacter.LFunctionTrivChar₁ M else DirichletCharacter.LFunction χ

def exOrd {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (ρ : ℂ) : ℕ :=
  analyticOrderNatAt (exLF χ) ρ

def exKer (y : ℝ) (w : ℂ) : ℂ := (y : ℂ) ^ w / (w * (w - 1))

def explicitFormulaConstant {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) : ℂ := -(deriv (exLF χ) 1 / exLF χ 1)

end Formalism.HermitianLattices.Ext.PrimesInProgressions

end RHLean.Analysis.AlpogeThin
