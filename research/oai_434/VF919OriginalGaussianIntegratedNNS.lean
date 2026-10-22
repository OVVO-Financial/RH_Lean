import OAI.NumberTheory.DirichletL.Detector.GaussianCommon
import «research.VF_919_OAI_GAUSSIAN_SUBSET_EXACT_COEFFICIENT_NNS_20261021»

/-!
# OAI-typed, proof-authoritative Gaussian subset -> signed NNS

Unlike the abstract coefficient interface, THIS FILE DIRECTLY USES the
original upstream OAI.SevenEighths.HeckeFamily.Character, CalibrationData, OAI
compensatedPhysicalProbe, compensationSubsetWeight, compensationRowTest,
selectedSlotFactor, gaussianJointDensity and the kernel-proved theorem
compensatedPhysicalProbe_common_gaussian.

The upsteam equality is the FULL convergent sum over dyadic indices and
Mellin height integrals. NNS is formed only AFTER those operations. The
principal signal is kept as an additional negative complex source atom.

The weighted Co/Div bound consumes a pointwise ORIGINAL-OAI probe bound
as an explicitly visible hypothesis, which in the high-row application
is supplied by actual_high_probe_from_raw_moments with its original
SourceMomentsAt assumptions. No new large-sieve inequality is claimed.

This source is checked in the original OAI 4.34.1 + RH_Lean combined
LEAN_PATH environment, not the RH_Lean-only research closure.
-/

noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths.ProbePhysical
open MeasureTheory

namespace RHLean.Analysis

local notation "O" => OAI.ActualEisensteinCubic.O

/-- Every parameter below is an ORIGINAL OAI declaration or source label.
    No norm-only coefficient replacement, bounded quadrature, or invented
    Hecke phase is present. -/
def originalOAIGaussianSubsetIntegral {K : ℕ} {ι : Type*}
    (V : Finset (Fin K) → SchwartzMap ℝ ℂ)
    (hV : ∀J, HasCompactSupport (V J : ℝ → ℂ))
    (eta : ι → OAI.SevenEighths.HeckeFamily.Character)
    (cal : ι → CalibrationData)
    (W0 W1 : ι → ℝ → ℂ) (slots : ι → Fin K → Finset O)
    (W : Fin K → ℝ → ℂ) (P : ι → Fin K → ℝ)
    (X Y Z : ι → ℝ) (u : ι) (J : Finset (Fin K)) : ℂ :=
  ∑' j : ℕ, ∫ t : ℝ,
    (∑ p : ((i : Fin K) → {a : O // a ∈ slots u i}),
      compensationSubsetWeight (eta u) W (P u)
        (fun i => (p i).val) J *
      compensationRowTest (eta u) (cal u) (W0 u) (W1 u)
        (fun i => (p i).val) J (X u) (Y u) ((2 : ℝ) ^ j) t *
      selectedSlotFactor W (P u) (fun i => (p i).val) J t) *
      gaussianJointDensity (V J) (hV J)
        ((2 : ℝ) ^ j / (Z u * ∏ i ∈ Finset.univ \ J, P u i)) t

/-- Original probe, with EXACT row-labelled original OAI types. -/
def originalOAIGaussianProbe {K : ℕ} {ι : Type*}
    (eta : ι → OAI.SevenEighths.HeckeFamily.Character)
    (cal : ι → CalibrationData)
    (W0 W1 : ι → ℝ → ℂ) (slots : ι → Fin K → Finset O)
    (W : Fin K → ℝ → ℂ) (P : ι → Fin K → ℝ)
    (X Y Z : ι → ℝ) (u : ι) : ℂ :=
  compensatedPhysicalProbe (eta u) (cal u)
    (W0 u) (W1 u) (slots u) W (P u) (X u) (Y u) (Z u)

/-- Kernel-proof direct instantiation with the original GaussianCommon
    hypotheses; the OAI row data and test weights are fully preserved.
    This is the source-correspondence half of the bridge. -/
theorem originalOAI_probe_eq_integrated_subsets
    {K : ℕ} {ι : Type*}
    (W : Fin K → ℝ → ℂ) (M : Fin K → ℝ)
    (hM : ∀i, 0 ≤ M i)
    (hwindow : ∀i y, W i (Real.exp y) ≠ 0 → |y| ≤ M i) :
    ∃ V : Finset (Fin K) → SchwartzMap ℝ ℂ,
      ∃ hV : ∀ J, HasCompactSupport (V J : ℝ → ℂ),
      ∀ (eta : ι → OAI.SevenEighths.HeckeFamily.Character)
        (cal : ι → CalibrationData)
        (W0 W1 : ι → ℝ → ℂ)
        (slots : ι → Fin K → Finset O)
        (P : ι → Fin K → ℝ) (X Y Z : ι → ℝ)
        (u : ι),
        HasCompactSupport (W0 u) →
        HasCompactSupport (W1 u) →
        (∀i a, a ∈ slots u i → a ≠ 0) →
        (∀i, 0 < P u i) →
        0 < X u → 0 < Y u → 0 < Z u →
        originalOAIGaussianProbe eta cal W0 W1 slots W P X Y Z u =
          ∑ J ∈ (Finset.univ : Finset (Fin K)).powerset,
            originalOAIGaussianSubsetIntegral V hV eta cal
              W0 W1 slots W P X Y Z u J := by
  obtain ⟨V, hV, _hMoments, hSource⟩ :=
    compensatedPhysicalProbe_common_gaussian W M hM hwindow
  refine ⟨V, hV, ?_⟩
  intro eta cal W0 W1 slots P X Y Z u hW0 hW1 hp hP hX hY hZ
  unfold originalOAIGaussianProbe
  simpa only [originalOAIGaussianSubsetIntegral] using
    (hSource (eta u) (cal u) (W0 u) (W1 u)
      hW0 hW1 (slots u) hp (P u) hP
      (X u) (Y u) (Z u) hX hY hZ)

/-- Original OAI Gaussian integral AFTER completion, with all marked masks,
    original Hecke factors, row weights and Gaussian densities. The NNS
    Co/Div (including the negative principal signal) is the exact same
    complex moment with no omitted cross-subset/cross-height terms.

    The second conclusion transfers any genuine OAI pointwise high-row
    norm estimate to uniform weighted signed NNS, keeping its same bound;
    no new exponent is assumed or fabricated here. -/
theorem originalOAI_gaussian_normalized_NNS_full_weighted_moment
    {K : ℕ} {ι : Type*}
    (W : Fin K → ℝ → ℂ) (M : Fin K → ℝ)
    (hM : ∀i, 0 ≤ M i)
    (hwindow : ∀i y, W i (Real.exp y) ≠ 0 → |y| ≤ M i) :
    ∃ V : Finset (Fin K) → SchwartzMap ℝ ℂ,
      ∃ hV : ∀ J, HasCompactSupport (V J : ℝ → ℂ),
      ∀ (rows : Finset ι)
        (eta : ι → OAI.SevenEighths.HeckeFamily.Character)
        (cal : ι → CalibrationData)
        (W0 W1 : ι → ℝ → ℂ)
        (slots : ι → Fin K → Finset O)
        (P : ι → Fin K → ℝ)
        (X Y Z : ι → ℝ) (normer : ι → ℂ) (principal : ι → ℂ)
        (weight B : ι → ℝ),
        (∀u ∈ rows, HasCompactSupport (W0 u)) →
        (∀u ∈ rows, HasCompactSupport (W1 u)) →
        (∀u ∈ rows, ∀i a, a ∈ slots u i → a ≠ 0) →
        (∀u ∈ rows, ∀i, 0 < P u i) →
        (∀u ∈ rows, 0 < X u) →
        (∀u ∈ rows, 0 < Y u) →
        (∀u ∈ rows, 0 < Z u) →
        (∀u ∈ rows, 0 ≤ weight u) →
        (∀u ∈ rows,
          ‖originalOAIGaussianProbe eta cal W0 W1 slots W P X Y Z u /
              normer u - principal u‖ ≤ B u) →
        let A := fun u J => originalOAIGaussianSubsetIntegral V hV eta cal
            W0 W1 slots W P X Y Z u J / normer u
        let co := vf919WeightedPhiCoMass rows
          (gaussianIntegratedSignalCarrier K) weight
          (fun u l =>
            (RHLean.Proof.stableFarComplexToRealPair
              (gaussianIntegratedSignalAtom A principal u l)).1)
          (fun u l =>
            (RHLean.Proof.stableFarComplexToRealPair
              (gaussianIntegratedSignalAtom A principal u l)).2)
        let div := vf919WeightedPhiDivMass rows
          (gaussianIntegratedSignalCarrier K) weight
          (fun u l =>
            (RHLean.Proof.stableFarComplexToRealPair
              (gaussianIntegratedSignalAtom A principal u l)).1)
          (fun u l =>
            (RHLean.Proof.stableFarComplexToRealPair
              (gaussianIntegratedSignalAtom A principal u l)).2)
        (∑ u ∈ rows, weight u *
          ‖originalOAIGaussianProbe eta cal W0 W1 slots W P X Y Z u /
              normer u - principal u‖ ^ 2 = co - div) ∧
        (co - div ≤ ∑ u ∈ rows, weight u * (B u) ^ 2) := by
  obtain ⟨V, hV, hSource⟩ :=
    originalOAI_probe_eq_integrated_subsets (ι := ι) W M hM hwindow
  refine ⟨V, hV, ?_⟩
  intro rows eta cal W0 W1 slots P X Y Z normer principal weight B
    hW0 hW1 hslots hP hX hY hZ hweight hHigh
  dsimp only
  let A := fun u J => originalOAIGaussianSubsetIntegral V hV eta cal
    W0 W1 slots W P X Y Z u J / normer u
  have hA (u : ι) (hu : u ∈ rows) :
      originalOAIGaussianProbe eta cal W0 W1 slots W P X Y Z u / normer u =
        ∑ J ∈ (Finset.univ : Finset (Fin K)).powerset, A u J := by
    dsimp only [A]
    rw [Finset.sum_div]
    rw [hSource eta cal W0 W1 slots P X Y Z u
      (hW0 u hu) (hW1 u hu) (hslots u hu) (hP u hu)
      (hX u hu) (hY u hu) (hZ u hu)]
  have hEnergy :
      (∑ u ∈ rows, weight u *
        ‖originalOAIGaussianProbe eta cal W0 W1 slots W P X Y Z u /
          normer u - principal u‖ ^ 2) =
        ∑ u ∈ rows, weight u *
          ‖(∑ J ∈ (Finset.univ : Finset (Fin K)).powerset,
              A u J) - principal u‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro u hu
    rw [hA u hu]
  have hBound (u : ι) (hu : u ∈ rows) :
      ‖(∑ J ∈ (Finset.univ : Finset (Fin K)).powerset,
          A u J) - principal u‖ ≤ B u := by
    rw [← hA u hu]
    exact hHigh u hu
  constructor
  · rw [hEnergy]
    exact gaussianIntegrated_principal_signed_NNS_moment_exact
      rows weight A principal
  · exact gaussianIntegrated_uniform_signed_NNS_of_original_bound
      rows weight hweight A principal B hBound


/-- Discharges the GaussianCommon logarithmic slot-window condition
    from the ORIGINAL high-row annular support, rather than postulating
    a synthetic bounded Mellin weight. -/
theorem originalOAI_gaussian_log_window_from_annular_support
    {K : ℕ} (W : Fin K → ℝ → ℂ) (a b : ℝ)
    (ha : 0 < a)
    (hSupport : ∀i, Function.support (W i) ⊆ Set.Ioo a b) :
    ∃ M : Fin K → ℝ, (∀i, 0 ≤ M i) ∧
      (∀i y, W i (Real.exp y) ≠ 0 → |y| ≤ M i) := by
  refine ⟨fun _ => |Real.log a| + |Real.log b| + 1, ?_, ?_⟩
  · intro i
    positivity
  · intro i y hy
    have hmem : Real.exp y ∈ Function.support (W i) := hy
    obtain ⟨hlo, hhi⟩ := hSupport i hmem
    have hl : Real.log a ≤ y := by
      have hh := Real.log_le_log ha hlo.le
      simpa only [Real.log_exp] using hh
    have hh : y ≤ Real.log b := by
      have hh' := Real.log_le_log (Real.exp_pos y) hhi.le
      simpa only [Real.log_exp] using hh'
    apply abs_le.mpr
    constructor
    · have hleft := neg_abs_le (Real.log a)
      have hright := abs_nonneg (Real.log b)
      dsimp
      linarith
    · have hright := le_abs_self (Real.log b)
      have hleft := abs_nonneg (Real.log a)
      dsimp
      linarith

/-- Precisely the REAL-valued slot-window profile used in the original
    HighFromMoments theorem; all three OAI Gaussian hypotheses are
    derived from hSupport and the positive lower annular edge. -/
theorem originalOAI_real_slot_window_from_annular_support
    {K : ℕ} (W : Fin K → ℝ → ℝ) (a b : ℝ)
    (ha : 0 < a)
    (hSupport : ∀i, Function.support (W i) ⊆ Set.Ioo a b) :
    ∃ M : Fin K → ℝ, (∀i, 0 ≤ M i) ∧
      (∀i y, ((W i (Real.exp y) : ℝ) : ℂ) ≠ 0 → |y| ≤ M i) := by
  apply originalOAI_gaussian_log_window_from_annular_support
    (fun i x => (W i x : ℂ)) a b ha
  intro i x hx
  apply hSupport i
  change (W i x : ℂ) ≠ 0 at hx
  change W i x ≠ 0
  exact_mod_cast hx

end RHLean.Analysis

#print axioms RHLean.Analysis.originalOAI_probe_eq_integrated_subsets
#print axioms RHLean.Analysis.originalOAI_gaussian_normalized_NNS_full_weighted_moment

#print axioms RHLean.Analysis.originalOAI_gaussian_log_window_from_annular_support
#print axioms RHLean.Analysis.originalOAI_real_slot_window_from_annular_support
