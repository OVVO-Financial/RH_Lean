import Mathlib

/-!
# Reconstructed same-host thin-source dependency

Mathematical source: Levent Alpöge (with Claude).
Source: src/Formalism/PeriodIntegrals/ZerosWindowIn.lean.
Pinned source: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/PeriodIntegrals/ZerosWindowIn.lean

This local proof reconstruction adapts the module/namespace boundary to native
RH_Lean. No upstream compiled artifact or terminal RH theorem is imported.
The source archive/mirror states no license; this notice preserves attribution
without assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace RHLean.Analysis.AlpogeThin

namespace PI

def LBoundRight : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ s : ℂ, 0 < s.re →
    ‖DirichletCharacter.LFunction χ s‖ ≤ 1 + 2 * ((q : ℝ) + 1) * (1 + ‖s‖ / s.re)

def ZetaBoundRight : Prop :=
  ∀ s : ℂ, 0 < s.re → s ≠ 1 → ‖riemannZeta s‖ ≤ 1 + 1 / ‖s - 1‖ + ‖s‖ * (1 + 1 / s.re)

def LInvRight : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ), 1 < s.re →
    ‖DirichletCharacter.LFunction χ s‖⁻¹ ≤ s.re / (s.re - 1)

end PI

end RHLean.Analysis.AlpogeThin
