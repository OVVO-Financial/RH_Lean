import «research.oai_434.VF919OriginalGaussianIntegratedNNS»
import «research.VF_919_RESONANT_FIBER_NNS_RECOMBINATION_20261022»

/-!
# Original OAI GaussianSubset normalized probe, grouped before energy

Directly applies the ORIGINAL-OAI compiled
  compensatedPhysicalProbe_common_gaussian
through originalOAI_probe_eq_integrated_subsets and obtains the exact
resonant-fiber decomposition, AFTER dyadic summation and Mellin height
integration. The original scalar normer is independent of internal u.

The negative principal signal is a DISTINCT None source atom.
No phase classes are invented: classOf is a proposed grouping and its
identification with actual ideal phase-locking must be proved separately.

This is the exact finite algebra, not the power-saving estimates.
-/

noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths.ProbePhysical
open MeasureTheory

namespace RHLean.Analysis
local notation "O" => OAI.ActualEisensteinCubic.O

/-- For each original completed OAI Gaussian window, all physical
    coefficients and principal correction recombine BEFORE squaring.
    The original high-row normer is a ROW-CONSTANT scalar. -/
theorem originalOAI_gaussian_resonant_fiber_recombination
    {K : ℕ} {ι κ : Type*}
    (W : Fin K → ℝ → ℂ) (M : Fin K → ℝ)
    (hM : ∀i, 0 ≤ M i)
    (hwindow : ∀i y, W i (Real.exp y) ≠ 0 → |y| ≤ M i)
    (rows : Finset ι)
    (classOf : Option (Finset (Fin K)) → κ)
    (eta : ι → OAI.SevenEighths.HeckeFamily.Character)
    (cal : ι → CalibrationData)
    (W0 W1 : ι → ℝ → ℂ)
    (slots : ι → Fin K → Finset O)
    (P : ι → Fin K → ℝ)
    (X Y Z : ι → ℝ)
    (normer : ℂ) (principal : ι → ℂ)
    (omega : ι → ℝ)
    (hW0 : ∀u ∈ rows, HasCompactSupport (W0 u))
    (hW1 : ∀u ∈ rows, HasCompactSupport (W1 u))
    (hslots : ∀u ∈ rows, ∀i a, a ∈ slots u i → a ≠ 0)
    (hP : ∀u ∈ rows, ∀i, 0 < P u i)
    (hX : ∀u ∈ rows, 0 < X u)
    (hY : ∀u ∈ rows, 0 < Y u)
    (hZ : ∀u ∈ rows, 0 < Z u) :
    ∃ V : Finset (Fin K) → SchwartzMap ℝ ℂ,
      ∃ hV : ∀ J, HasCompactSupport (V J : ℝ → ℂ),
      let A := fun u J => originalOAIGaussianSubsetIntegral V hV eta cal
        W0 W1 slots W P X Y Z u J / normer
      let atom := gaussianIntegratedSignalAtom A principal
      (∑ u ∈ rows, omega u *
        ‖originalOAIGaussianProbe eta cal W0 W1 slots W P X Y Z u /
            normer - principal u‖ ^ 2) =
        resonantFiberEnergy rows (gaussianIntegratedSignalCarrier K)
          classOf atom omega +
        nonresonantInterfiberGram rows (gaussianIntegratedSignalCarrier K)
          classOf atom omega := by
  obtain ⟨V, hV, hSource⟩ :=
    originalOAI_probe_eq_integrated_subsets (ι := ι) W M hM hwindow
  refine ⟨V, hV, ?_⟩
  dsimp only
  let A := fun u J => originalOAIGaussianSubsetIntegral V hV eta cal
    W0 W1 slots W P X Y Z u J / normer
  let atom := gaussianIntegratedSignalAtom A principal
  have hrow (u : ι) (hu : u ∈ rows) :
      originalOAIGaussianProbe eta cal W0 W1 slots W P X Y Z u /
          normer - principal u =
        ∑ l ∈ gaussianIntegratedSignalCarrier K, atom u l := by
    have hs := hSource eta cal W0 W1 slots P X Y Z u
      (hW0 u hu) (hW1 u hu) (hslots u hu)
      (hP u hu) (hX u hu) (hY u hu) (hZ u hu)
    calc
      originalOAIGaussianProbe eta cal W0 W1 slots W P X Y Z u /
          normer - principal u =
          (∑ J ∈ (Finset.univ : Finset (Fin K)).powerset,
            originalOAIGaussianSubsetIntegral V hV eta cal
              W0 W1 slots W P X Y Z u J) / normer - principal u := by
            rw [hs]
      _ = (∑ J ∈ (Finset.univ : Finset (Fin K)).powerset,
           A u J) - principal u := by
            simp only [A, Finset.sum_div]
      _ = ∑ l ∈ gaussianIntegratedSignalCarrier K, atom u l := by
          exact (gaussianIntegrated_source_minus_principal_exact
            A principal u).symm
  have henergy :
      (∑ u ∈ rows, omega u *
        ‖originalOAIGaussianProbe eta cal W0 W1 slots W P X Y Z u /
          normer - principal u‖ ^ 2) =
      ∑ u ∈ rows, omega u *
        ‖∑ l ∈ gaussianIntegratedSignalCarrier K, atom u l‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro u hu
    rw [hrow u hu]
  rw [henergy]
  exact resonant_fiber_recombination_eq rows
    (gaussianIntegratedSignalCarrier K) classOf atom omega

end RHLean.Analysis

#print axioms RHLean.Analysis.originalOAI_gaussian_resonant_fiber_recombination
