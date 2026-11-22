import RHLean.Analysis.AlpogeLandau.LandauZeroFreeCriterion

/-!
# Reconstructed analytic window dependency

Mathematical source: Levent Alpöge (with Claude), src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/CharFamilyLFunctionNeZeroOfOneLeRe.lean.
Pinned source: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/CharFamilyLFunctionNeZeroOfOneLeRe.lean

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

theorem charFamily_LFunction_ne_zero_of_one_le_re (F : CharFamily) (i : F.ι) (s : ℂ) (hs : 1 ≤ s.re) :
    DirichletCharacter.LFunction (F.χ i) s ≠ 0 := by
  have := F.nz i
  rcases F.adm i with h | h
  · have key : ∀ (M : ℕ) [NeZero M] (ψ : DirichletCharacter ℂ M), M = 1 →
        DirichletCharacter.LFunction ψ s ≠ 0 := by
      intro M _ ψ hM
      subst hM
      rw [DirichletCharacter.LFunction_modOne_eq]
      exact riemannZeta_ne_zero_of_one_le_re hs
    exact key _ (F.χ i) h
  · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re _ (Or.inl h) hs

end RHLean.Analysis.AlpogeLandau

end

