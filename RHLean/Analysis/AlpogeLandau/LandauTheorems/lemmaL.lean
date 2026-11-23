import RHLean.Analysis.AlpogeLandau.LandauZeroFreeCriterion
import RHLean.Analysis.AlpogeLandau.LandauTheorems.poleData
import RHLean.Analysis.AlpogeLandau.LandauTheorems.landauWindow
import RHLean.Analysis.AlpogeLandau.LandauTheorems.WindowHypUOfWindowHyp
import RHLean.Analysis.AlpogeLandau.LandauTheorems.CharFamilyLFunctionNeZeroOfOneLeRe

/-!
# Reconstructed analytic window dependency

Mathematical source: Levent Alpöge (with Claude), src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/lemmaL.lean.
Pinned source: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/lemmaL.lean

This local proof reconstruction changes the module/namespace boundary and is
checked against RH_Lean's Lean/Mathlib versions. It imports no upstream compiled
artifact or terminal RH theorem. The source archive/mirror states no license;
this provenance notice does not assign a new license to that source material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000


open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace RHLean.Analysis.AlpogeLandau

theorem lemmaL (F : CharFamily) {θ δ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hδ : 0 < δ) (h : WindowHyp F θ δ) :
    ZeroFree F θ := by
  intro i s hs hzero
  obtain ⟨Φ, hP⟩ := poleData F
  have hZ := landau_window hP hθ hθ1 hδ (windowHypU_of_windowHyp F hδ h)
  by_cases h1 : 1 ≤ s.re
  · exact charFamily_LFunction_ne_zero_of_one_le_re F i s h1 hzero
  · have hmem : s ∈ zeroSet F := ⟨by linarith, i, Or.inl hzero⟩
    have := hZ s hmem
    linarith

end RHLean.Analysis.AlpogeLandau

end

