import Mathlib

/-!
# Reconstructed same-host thin-source dependency

Mathematical source: Levent Alpöge (with Claude).
Source: src/Formalism/LandauZeroFreeBounds/Statement.lean.
Pinned source: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/LandauZeroFreeBounds/Statement.lean

This local proof reconstruction adapts the module/namespace boundary to native
RH_Lean. No upstream compiled artifact or terminal RH theorem is imported.
The source archive/mirror states no license; this notice preserves attribution
without assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace RHLean.Analysis.AlpogeThin

open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

def InRegion (c : ℝ) (q : ℕ) (s : ℂ) : Prop :=
  1 - c / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ s.re

def IsLZero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) : Prop :=
  (χ ≠ 1 ∨ s ≠ 1) ∧ DirichletCharacter.LFunction χ s = 0

def ZFRDirichlet : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
    InRegion c q s → IsLZero χ s →
      χ ^ 2 = 1 ∧ χ ≠ 1 ∧ s.im = 0 ∧ deriv (DirichletCharacter.LFunction χ) s ≠ 0 ∧
      ∀ (χ' : DirichletCharacter ℂ q) (s' : ℂ), InRegion c q s' → IsLZero χ' s' → χ' = χ ∧ s' = s

end Formalism.ZeroFreeDirichlet

end

end RHLean.Analysis.AlpogeThin
