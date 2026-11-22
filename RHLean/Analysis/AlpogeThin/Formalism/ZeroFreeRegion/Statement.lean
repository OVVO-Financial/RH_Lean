import RHLean.Analysis.AlpogeThin.Formalism.StatementOC

/-!
# Reconstructed same-host thin-source dependency

Mathematical source: Levent Alpöge (with Claude).
Source: src/Formalism/ZeroFreeRegion/Statement.lean.
Pinned source: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/ZeroFreeRegion/Statement.lean

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

namespace Formalism.ZF

def ZeroFreeRegion : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ s : ℂ, s ≠ 1 → 1 - c / Real.log (|s.im| + 2) ≤ s.re → riemannZeta s ≠ 0

def LogDerivRegion : Prop :=
  ∃ c C : ℝ, 0 < c ∧ ∀ s : ℂ, s ≠ 1 → 1 - c / Real.log (|s.im| + 2) ≤ s.re →
    ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1)‖ ≤ C * Real.log (|s.im| + 2) ^ 2

def GzPNT : Prop :=
  ∃ c K : ℝ, 0 < c ∧ ∀ y : ℝ, 2 ≤ y →
    |Formalism.Gz y| ≤ K * y * Real.exp (-c * Real.sqrt (Real.log y))

end Formalism.ZF

end RHLean.Analysis.AlpogeThin
