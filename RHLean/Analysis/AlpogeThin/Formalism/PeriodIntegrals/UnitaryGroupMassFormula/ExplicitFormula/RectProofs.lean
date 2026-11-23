import RHLean.Analysis.AlpogeThin.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.GoodHeightExists
import RHLean.Analysis.AlpogeThin.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.RectIntEqZeroOfDifferentiableOn

/-!
# Reconstructed same-host thin-source dependency

Mathematical source: Levent Alpöge (with Claude).
Source: src/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectProofs.lean.
Pinned source: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectProofs.lean

This local proof reconstruction adapts the module/namespace boundary to native
RH_Lean. No upstream compiled artifact or terminal RH theorem is imported.
The source archive/mirror states no license; this notice preserves attribution
without assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace RHLean.Analysis.AlpogeThin

namespace PI.EF

open Complex

theorem rectCauchy : RectCauchy := by
  intro x₀ x₁ y₀ y₁ h w h1 h2 h3 h4 hh
  exact Rect.rectInt_div_sub (z := ⟨x₀, y₀⟩) (w := ⟨x₁, y₁⟩) (p := w) ⟨h1, h2, h3, h4⟩ hh

theorem rectResidue : RectResidue := by
  intro x₀ x₁ y₀ y₁ H Z wt e u hu h1 h2 h3 h4 hH hZ
  exact Rect.rect_residue (z := ⟨x₀, y₀⟩) (w := ⟨x₁, y₁⟩) Z wt e hu
    ⟨by simpa using h1, by simpa using h2, by simpa using h3, by simpa using h4⟩ hH
    (fun ρ hρ => ⟨(hZ ρ hρ).1, (hZ ρ hρ).2⟩)

end PI.EF

end RHLean.Analysis.AlpogeThin
