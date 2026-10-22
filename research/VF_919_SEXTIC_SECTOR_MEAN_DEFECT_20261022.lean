import Mathlib
import «research.VF_919_OAI_NNS_INDEPENDENT_SIGNED_SAVING_20261022»

/-!
# Sextic sector-mean subtraction with zero values and resonances

The ORIGINAL OAI high-row normalizer is a row-constant complex scalar:
sourceResidueConstant times Probe.principalScalar. It is NOT a
row-dependent product of sextic Stage-II local factors.

This module proves exact sector projection for arbitrary NONUNIFORM
weights and complex row-dependent coefficients. No equal sector masses,
conductor completion, or independence hypothesis is assumed.
Option (Fin 6): none records a genuinely zero character value.
Degenerate relative character phases are not discarded.

The exact scalar reciprocal split has no assumed small remainder.
A uniform analytic bound for ACTUAL OAI sector defects is still open.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

/-- Cancellation of the geometric sum for any nontrivial sixth root.
    Distinct six-sector phase labelling itself requires primitivity. -/
theorem sextic_nontrivial_root_geometric_sum_zero
    (ζ : ℂ) (hpow : ζ ^ 6 = 1) (hne : ζ ≠ 1) :
    (∑ k : Fin 6, ζ ^ k.val) = 0 := by
  have hfactor :
      (ζ - 1) * (1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 + ζ ^ 5) =
        ζ ^ 6 - 1 := by ring
  have hm : (ζ - 1) * (1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 + ζ ^ 5) = 0 := by
    rw [hfactor, hpow]
    ring
  have hdiff : ζ - 1 ≠ 0 := sub_ne_zero.mpr hne
  have hgeom : 1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 + ζ ^ 5 = 0 :=
    (mul_eq_zero.mp hm).resolve_left hdiff
  rw [Fin.sum_univ_eq_sum_range]
  have hsum :
      (∑ k ∈ Finset.range 6, ζ ^ k) =
        1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 + ζ ^ 5 := by
    simp [Finset.sum_range_succ]
    ring
  rw [hsum]
  exact hgeom

/-- The sector mean may be complex: source coefficients carry phases. -/
def sexticSectorMean (W : Fin 6 → ℂ) : ℂ :=
  (∑ k : Fin 6, W k) / 6

def sexticSectorDefect (ζ : ℂ) (W : Fin 6 → ℂ) : ℂ :=
  ∑ k : Fin 6, (W k - sexticSectorMean W) * ζ ^ k.val

/-- Exact subtraction of the uniform six-sector mean.
    This identity does NOT estimate its nonuniform defect. -/
theorem sextic_sector_mean_subtraction
    (ζ : ℂ) (hpow : ζ ^ 6 = 1) (hne : ζ ≠ 1)
    (W : Fin 6 → ℂ) :
    (∑ k : Fin 6, W k * ζ ^ k.val) =
      sexticSectorDefect ζ W := by
  have hz := sextic_nontrivial_root_geometric_sum_zero ζ hpow hne
  unfold sexticSectorDefect
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hz]
  ring

/-- none is a zero-valued character, NOT a root-of-unity orbit. -/
def sexticPhaseWithZero (ζ : ℂ) : Option (Fin 6) → ℂ
  | none => 0
  | some k => ζ ^ k.val

/-- Fully nonuniform row masses, preserving complex coefficients. -/
def sexticWeightedSectorMass {ι : Type*}
    (rows : Finset ι) (phase : ι → Option (Fin 6))
    (omega : ι → ℝ) (coefficient : ι → ℂ)
    (k : Fin 6) : ℂ :=
  ∑ u ∈ rows,
    if phase u = some k then (omega u : ℂ) * coefficient u else 0

/-- Exact sector reassembly with zeros, masks and arbitrary row weights. -/
theorem sextic_weighted_sector_reassembly {ι : Type*}
    (rows : Finset ι) (phase : ι → Option (Fin 6))
    (omega : ι → ℝ) (coefficient : ι → ℂ) (ζ : ℂ) :
    (∑ u ∈ rows, (omega u : ℂ) * coefficient u *
      sexticPhaseWithZero ζ (phase u)) =
    ∑ k : Fin 6,
      sexticWeightedSectorMass rows phase omega coefficient k *
        ζ ^ k.val := by
  classical
  unfold sexticWeightedSectorMass
  calc
    (∑ u ∈ rows, (omega u : ℂ) * coefficient u *
        sexticPhaseWithZero ζ (phase u)) =
      ∑ u ∈ rows, ∑ k : Fin 6,
        (if phase u = some k then
          (omega u : ℂ) * coefficient u else 0) * ζ ^ k.val := by
        apply Finset.sum_congr rfl
        intro u hu
        cases h : phase u with
        | none =>
            simp [sexticPhaseWithZero, h]
        | some k =>
            simp [sexticPhaseWithZero, h, Finset.sum_ite_eq', mul_assoc]
    _ = ∑ k : Fin 6, ∑ u ∈ rows,
        (if phase u = some k then
          (omega u : ℂ) * coefficient u else 0) * ζ ^ k.val := by
        rw [Finset.sum_comm]
    _ = ∑ k : Fin 6,
        (∑ u ∈ rows,
          if phase u = some k then
            (omega u : ℂ) * coefficient u else 0) * ζ ^ k.val := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.sum_mul]

/-- Weighted nonuniform sextic sum is exactly its sector defect. -/
theorem sextic_weighted_nonuniform_defect_exact {ι : Type*}
    (rows : Finset ι) (phase : ι → Option (Fin 6))
    (omega : ι → ℝ) (coefficient : ι → ℂ)
    (ζ : ℂ) (hpow : ζ ^ 6 = 1) (hne : ζ ≠ 1) :
    (∑ u ∈ rows, (omega u : ℂ) * coefficient u *
       sexticPhaseWithZero ζ (phase u)) =
      sexticSectorDefect ζ
        (sexticWeightedSectorMass rows phase omega coefficient) := by
  rw [sextic_weighted_sector_reassembly]
  exact sextic_sector_mean_subtraction ζ hpow hne
    (sexticWeightedSectorMass rows phase omega coefficient)

/-- Degenerate relative characters remain fully resonant. -/
theorem sextic_trivial_character_retains_full_weight {ι : Type*}
    (rows : Finset ι) (phase : ι → Option (Fin 6))
    (omega : ι → ℝ) (coefficient : ι → ℂ) (ζ : ℂ)
    (htrivial : ∀ u ∈ rows, phase u = some (0 : Fin 6)) :
    (∑ u ∈ rows, (omega u : ℂ) * coefficient u *
        sexticPhaseWithZero ζ (phase u)) =
      ∑ u ∈ rows, (omega u : ℂ) * coefficient u := by
  apply Finset.sum_congr rfl
  intro u hu
  rw [htrivial u hu]
  simp [sexticPhaseWithZero]

/-- Character zeros contribute exactly zero; not phase cancellation. -/
theorem sextic_zero_characters_contribute_zero {ι : Type*}
    (rows : Finset ι) (phase : ι → Option (Fin 6))
    (omega : ι → ℝ) (coefficient : ι → ℂ) (ζ : ℂ)
    (hzero : ∀ u ∈ rows, phase u = none) :
    (∑ u ∈ rows, (omega u : ℂ) * coefficient u *
        sexticPhaseWithZero ζ (phase u)) = 0 := by
  apply Finset.sum_eq_zero
  intro u hu
  rw [hzero u hu]
  simp [sexticPhaseWithZero]

/-- Exact scalar normalizer split; no small remainder is assumed. -/
theorem sextic_scalar_normalizer_split
    (source principal normer : ℂ) :
    source / normer - principal =
      (source - principal) + (normer⁻¹ - 1) * source := by
  rw [div_eq_mul_inv]
  ring

/-- A quantitative error requires the EXPLICIT bound on the scalar. -/
theorem sextic_scalar_normalizer_error_le
    (source normer : ℂ) (bound : ℝ)
    (hbound : ‖normer⁻¹ - 1‖ ≤ bound) :
    ‖source / normer - source‖ ≤ bound * ‖source‖ := by
  have heq : source / normer - source =
      (normer⁻¹ - 1) * source := by
    rw [div_eq_mul_inv]
    ring
  rw [heq, norm_mul]
  exact mul_le_mul_of_nonneg_right hbound (norm_nonneg source)

/-- A row-constant normalizer factors OUTSIDE every sector and defect. -/
theorem sextic_constant_normalizer_defect_exact {ι : Type*}
    (rows : Finset ι) (phase : ι → Option (Fin 6))
    (omega : ι → ℝ) (coefficient : ι → ℂ)
    (normer ζ : ℂ) (hpow : ζ ^ 6 = 1) (hne : ζ ≠ 1) :
    (∑ u ∈ rows, (omega u : ℂ) * (coefficient u / normer) *
      sexticPhaseWithZero ζ (phase u)) =
    sexticSectorDefect ζ
        (sexticWeightedSectorMass rows phase omega coefficient) / normer := by
  calc
    _ = ∑ u ∈ rows,
        ((omega u : ℂ) * coefficient u *
          sexticPhaseWithZero ζ (phase u)) / normer := by
          apply Finset.sum_congr rfl
          intro u hu
          ring
    _ = (∑ u ∈ rows, (omega u : ℂ) * coefficient u *
        sexticPhaseWithZero ζ (phase u)) / normer := by
          rw [Finset.sum_div]
    _ = _ := by
      rw [sextic_weighted_nonuniform_defect_exact rows phase omega coefficient
        ζ hpow hne]


/-- EXACT NNS-to-Hecke cross-term: concordant minus discordant
    zero-target partial covariance is the Hermitian real part.
    The preceding sector defect is therefore the precise offdiagonal
    term in the original (fully integrated) Co-Div ledger. -/
theorem sextic_NNS_cross_pair_eq_real_Hecke_Gram (a b : ℂ) :
    let xa := (stableFarComplexToRealPair a).1
    let ya := (stableFarComplexToRealPair a).2
    let xb := (stableFarComplexToRealPair b).1
    let yb := (stableFarComplexToRealPair b).2
    ((zeroTargetCoPartialPair xa xb + zeroTargetCoPartialPair ya yb) -
      (zeroTargetDivergentPair xa xb + zeroTargetDivergentPair ya yb)) / 2 =
        (a * star b).re := by
  dsimp only
  have hX := zeroTargetCoPartial_sub_divergent_eq_mul
    (stableFarComplexToRealPair a).1 (stableFarComplexToRealPair b).1
  have hY := zeroTargetCoPartial_sub_divergent_eq_mul
    (stableFarComplexToRealPair a).2 (stableFarComplexToRealPair b).2
  have hPhi := stableFarRealPairNormalizedDot_complexToRealPair a b
  dsimp [stableFarRealPairNormalizedDot, stableFarRealPairDot] at hPhi
  linarith


/-- Extend the exact sector decomposition to ALL labelled offdiagonal
    ideal pairs, with pair-dependent weights, phases and coefficients.
    Duplicate rational norms are NOT merged: each pair is a distinct
    element of the original pair carrier. -/
theorem sextic_all_labelled_pairs_defect_exact
    {ι α : Type*} (rows : Finset ι) (pairs : Finset α)
    (phase : α → ι → Option (Fin 6))
    (omega : ι → ℝ) (coefficient : α → ι → ℂ)
    (ζ : ℂ) (hpow : ζ ^ 6 = 1) (hne : ζ ≠ 1) :
    (∑ pair ∈ pairs, ∑ u ∈ rows,
      (omega u : ℂ) * coefficient pair u *
        sexticPhaseWithZero ζ (phase pair u)) =
      ∑ pair ∈ pairs,
        sexticSectorDefect ζ
          (sexticWeightedSectorMass rows (phase pair) omega
            (coefficient pair)) := by
  apply Finset.sum_congr rfl
  intro pair hpair
  exact sextic_weighted_nonuniform_defect_exact rows
    (phase pair) omega (coefficient pair) ζ hpow hne

/-- This is the required *explicit phase admission* interface for the
    ACTUAL OAI marked ideal coefficients. A genuine Hecke sextic-source
    identification must prove hPhase from the ORIGINAL declarations;
    it is NOT inferred from a rational norm or arbitrary coefficient.

    The conclusion is an exact full-pair offdiagonal sector defect.
    There is still no bound on the defect and no imported hHigh. -/
theorem sextic_admitted_offdiagonal_Hecke_pair_defect
    {ι α : Type*} (rows : Finset ι) (pairs : Finset α)
    (a b : α → ι → ℂ)
    (phase : α → ι → Option (Fin 6))
    (omega : ι → ℝ) (coefficient : α → ι → ℂ)
    (ζ : ℂ) (hpow : ζ ^ 6 = 1) (hne : ζ ≠ 1)
    (hPhase : ∀ pair ∈ pairs, ∀ u ∈ rows,
      a pair u * star (b pair u) =
        coefficient pair u *
          sexticPhaseWithZero ζ (phase pair u)) :
    (∑ pair ∈ pairs, ∑ u ∈ rows,
       (omega u : ℂ) * (a pair u * star (b pair u))) =
      ∑ pair ∈ pairs,
        sexticSectorDefect ζ
          (sexticWeightedSectorMass rows (phase pair) omega
            (coefficient pair)) := by
  calc
    _ = (∑ pair ∈ pairs, ∑ u ∈ rows,
      (omega u : ℂ) * coefficient pair u *
        sexticPhaseWithZero ζ (phase pair u)) := by
        apply Finset.sum_congr rfl
        intro pair hpair
        apply Finset.sum_congr rfl
        intro u hu
        rw [hPhase pair hpair u hu]
    _ = _ := sextic_all_labelled_pairs_defect_exact rows pairs
      phase omega coefficient ζ hpow hne

end RHLean.Analysis

#print axioms RHLean.Analysis.sextic_nontrivial_root_geometric_sum_zero
#print axioms RHLean.Analysis.sextic_NNS_cross_pair_eq_real_Hecke_Gram
#print axioms RHLean.Analysis.sextic_sector_mean_subtraction
#print axioms RHLean.Analysis.sextic_weighted_sector_reassembly
#print axioms RHLean.Analysis.sextic_weighted_nonuniform_defect_exact
#print axioms RHLean.Analysis.sextic_trivial_character_retains_full_weight
#print axioms RHLean.Analysis.sextic_zero_characters_contribute_zero
#print axioms RHLean.Analysis.sextic_scalar_normalizer_split
#print axioms RHLean.Analysis.sextic_scalar_normalizer_error_le
#print axioms RHLean.Analysis.sextic_constant_normalizer_defect_exact

#print axioms RHLean.Analysis.sextic_all_labelled_pairs_defect_exact
#print axioms RHLean.Analysis.sextic_admitted_offdiagonal_Hecke_pair_defect
