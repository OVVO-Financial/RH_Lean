import RHLean.Analysis.NNSCoDivDeterminant
import «research.NativeWheelNNSComparison»

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis.AlpogeThin.SlotProjector.WheelNNS
open RHLean.Analysis.NNSCoDiv

/-- Lossless two-matrix synthesis on the actual original counting measure. -/
theorem coDiv_two_matrix {J I : Type*} [Fintype J] (X : Matrix J I ℝ) :
    coDiv X = finiteCo Finset.univ (fun _ => 1) X 0 -
      finiteDiv Finset.univ (fun _ => 1) X 0 := by
  unfold coDiv finiteCo finiteDiv
  abel

/-- The normalized spectral correction of the actual physical wheel Gram. -/
theorem coDiv_spectral {J I : Type*} [Fintype J] [Fintype I] [DecidableEq I]
    (X : Matrix J I ℝ)
    (hc : (finiteCo Finset.univ (fun _ => 1) X 0).PosDef) :
    ∃ hK : (normalized (finiteCo Finset.univ (fun _ => 1) X 0)
      (finiteDiv Finset.univ (fun _ => 1) X 0)).IsHermitian,
      (∀ i, -1 ≤ hK.eigenvalues i ∧ hK.eigenvalues i ≤ 1) ∧
      (coDiv X).det = (finiteCo Finset.univ (fun _ => 1) X 0).det *
        ∏ i, (1-hK.eigenvalues i) := by
  obtain ⟨hk,he,hf⟩ := finite_spectral_synthesis Finset.univ (fun _ => 1) X 0
    (fun _ _ => zero_le_one) hc
  rw [two_matrix, ← coDiv_two_matrix] at hf
  exact ⟨hk,he,hf⟩

end RHLean.Analysis.AlpogeThin.SlotProjector.WheelNNS
