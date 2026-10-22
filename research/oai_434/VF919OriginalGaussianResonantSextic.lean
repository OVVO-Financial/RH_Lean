import «research.oai_434.VF919OriginalGaussianResonantFibers»

/-!
# Exact ORIGINAL-OAI integrated source = grouped resonant + sextic defect

The completed GaussianSubset Mellin integrals, physical Hecke phases,
the original ROW-CONSTANT normer, and minus-principal atom are directly
imported from the pinned original OAI-typed theorem, not rebuilt.

The only additional premise is the specific Hecke phase-factorization
hPhase on each different-fiber completed source pair. The statement
does not assume that any arbitrary character admits such a factorization,
nor a quantitative bound or a favorable sign for its sector defect.

This is the exact source-specific composition of the algebra the user
requested, BEFORE any independent 7/8 analytic saving.
-/

noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths.ProbePhysical
open MeasureTheory

namespace RHLean.Analysis
local notation "O" => OAI.ActualEisensteinCubic.O

theorem originalOAI_gaussian_fiber_equals_sextic_defect
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
      ∀ (phase : κ → κ → ι → Option (Fin 6))
        (coefficient : κ → κ → ι → ℂ)
        (ζ : ℂ) (hpow : ζ ^ 6 = 1) (hne : ζ ≠ 1),
        (∀ c ∈ resonantFiberClasses (gaussianIntegratedSignalCarrier K) classOf,
          ∀ d ∈ (resonantFiberClasses
              (gaussianIntegratedSignalCarrier K) classOf).erase c,
          ∀ u ∈ rows,
            resonantFiberSum (gaussianIntegratedSignalCarrier K)
                classOf atom u c *
              star (resonantFiberSum (gaussianIntegratedSignalCarrier K)
                classOf atom u d) =
              coefficient c d u *
                sexticPhaseWithZero ζ (phase c d u)) →
        (∑ u ∈ rows, omega u *
          ‖originalOAIGaussianProbe eta cal W0 W1 slots W P X Y Z u /
              normer - principal u‖ ^ 2) =
          resonantFiberEnergy rows (gaussianIntegratedSignalCarrier K)
            classOf atom omega +
          ∑ c ∈ resonantFiberClasses (gaussianIntegratedSignalCarrier K) classOf,
            ∑ d ∈ (resonantFiberClasses
                (gaussianIntegratedSignalCarrier K) classOf).erase c,
              (sexticSectorDefect ζ
                (sexticWeightedSectorMass rows (phase c d) omega
                  (coefficient c d))).re := by
  obtain ⟨V, hV, hgroup⟩ :=
    originalOAI_gaussian_resonant_fiber_recombination W M hM hwindow
      rows classOf eta cal W0 W1 slots P X Y Z normer principal
      omega hW0 hW1 hslots hP hX hY hZ
  refine ⟨V, hV, ?_⟩
  intro phase coefficient ζ hpow hne hPhase
  dsimp only
  let A := fun u J => originalOAIGaussianSubsetIntegral V hV eta cal
    W0 W1 slots W P X Y Z u J / normer
  let atom := gaussianIntegratedSignalAtom A principal
  have hOriginal :
      (∑ u ∈ rows, omega u *
        ‖originalOAIGaussianProbe eta cal W0 W1 slots W P X Y Z u /
            normer - principal u‖ ^ 2) =
          resonantFiberEnergy rows (gaussianIntegratedSignalCarrier K)
            classOf atom omega +
          nonresonantInterfiberGram rows (gaussianIntegratedSignalCarrier K)
            classOf atom omega := by
    simpa only [A, atom] using hgroup
  have hSector :
      nonresonantInterfiberGram rows (gaussianIntegratedSignalCarrier K)
        classOf atom omega =
          ∑ c ∈ resonantFiberClasses (gaussianIntegratedSignalCarrier K) classOf,
            ∑ d ∈ (resonantFiberClasses
                (gaussianIntegratedSignalCarrier K) classOf).erase c,
              (sexticSectorDefect ζ
                (sexticWeightedSectorMass rows (phase c d) omega
                  (coefficient c d))).re :=
    resonant_interfiber_Gram_eq_sextic_defects
      rows (gaussianIntegratedSignalCarrier K) classOf atom
      omega phase coefficient ζ hpow hne hPhase
  exact hOriginal.trans (congrArg
    (fun x : ℝ => resonantFiberEnergy rows (gaussianIntegratedSignalCarrier K)
      classOf atom omega + x) hSector)

end RHLean.Analysis

#print axioms RHLean.Analysis.originalOAI_gaussian_fiber_equals_sextic_defect
