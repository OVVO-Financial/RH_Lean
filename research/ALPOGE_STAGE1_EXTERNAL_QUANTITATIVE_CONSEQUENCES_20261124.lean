import RHLean.Analysis.AlpogeNativeBoundConsequences

/-!
# Stage 1: external quantitative theorem, native consequences

The pinned upstream quantitative window conclusion is accepted as an
explicit external mathematical premise in this stage. This file does
not assert that premise as an axiom, import the upstream supplier proof,
or depend on PR #1201. The same cofinal windows and constant give the
native signed NNS estimate. The existing native Landau argument gives RH
relative to that premise. No eventual all-N bound is inferred from
window coverage alone.
-/

noncomputable section

namespace RHLean.Analysis.AlpogeStage1

open AlpogeNativeBoundHandoff

/-- The external theorem is the sole mathematical input. The native
NNS bound uses the very same complete windows as the native Gz bound. -/
theorem externalQuantitative_consequences
    (hExternal : ∃ K ε₁ : ℝ, 0 < ε₁ ∧ SmallEpsilonWindowBound K ε₁) :
    RiemannHypothesis ∧
      (∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧
        (∀ y ∈ Set.Icc Y (Y ^ (1 + (1 / 2 : ℝ))),
          alpogeNativeGzArithmetic y ≤ C * y ^ (1 / 2 + η)) ∧
        (∀ N : ℕ, 1 ≤ N → (N : ℝ) ∈ Set.Icc Y (Y ^ (1 + (1 / 2 : ℝ))) →
          alpogeGzNNSHistory N ≤ C * (N : ℝ) ^ (-(1 : ℝ) / 2 + η))) := by
  obtain ⟨K, ε₁, hε₁, hbound⟩ := hExternal
  refine ⟨riemannHypothesis_of_smallEpsilonWindowBound hε₁ hbound, ?_⟩
  have hw := realWindowBound_of_smallEpsilonWindowBound hε₁ hbound
  intro η hη
  obtain ⟨C, hC⟩ := hw η hη
  refine ⟨C, fun Y₀ => ?_⟩
  obtain ⟨Y, hY, hwin⟩ := hC Y₀
  refine ⟨Y, hY, hwin, fun N hN hmem => ?_⟩
  apply (nativeAlpogeGz_rpow_le_iff_NNSHistory N hN C η).mp
  rw [← alpogeNativeGzArithmetic_natCast N]
  exact hwin (N : ℝ) hmem

#print axioms externalQuantitative_consequences

end RHLean.Analysis.AlpogeStage1
