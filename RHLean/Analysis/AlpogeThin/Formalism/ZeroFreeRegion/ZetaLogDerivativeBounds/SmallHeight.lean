import RHLean.Analysis.AlpogeThin.Formalism.ZeroFreeRegion.SmallHeightLogDeriv

/-!
# Reconstructed same-host thin-source dependency

Mathematical source: Levent Alpöge (with Claude).
Source: src/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/SmallHeight.lean.
Pinned source: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/SmallHeight.lean

This local proof reconstruction adapts the module/namespace boundary to native
RH_Lean. No upstream compiled artifact or terminal RH theorem is imported.
The source archive/mirror states no license; this notice preserves attribution
without assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace RHLean.Analysis.AlpogeThin

open Complex Set Filter Topology

noncomputable section

namespace Formalism.ZF

theorem zeroFreeBoundedHeight : SmallHeight := by
  unfold SmallHeight
  intro T
  have hopen : IsOpen {s : ℂ | s ≠ 1 → riemannZeta s ≠ 0} := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    by_cases hz1 : z = 1
    · subst hz1
      have h := riemannZeta_residue_one.eventually_ne one_ne_zero
      rw [eventually_nhdsWithin_iff] at h
      filter_upwards [h] with x hx hx1
      exact right_ne_zero_of_mul (hx hx1)
    · have hc : ContinuousAt riemannZeta z := (differentiableAt_riemannZeta hz1).continuousAt
      filter_upwards [hc.eventually_ne (hz hz1)] with x hx _
      exact hx
  set K : Set ℂ := (fun y : ℝ => (1 : ℂ) + (y : ℂ) * I) '' Icc (-T) T
  have hKc : IsCompact K :=
    isCompact_Icc.image (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
  have hKsub : K ⊆ {s : ℂ | s ≠ 1 → riemannZeta s ≠ 0} := by
    rintro _ ⟨y, -, rfl⟩ _
    apply riemannZeta_ne_zero_of_one_le_re
    simp
  obtain ⟨δ, hδ, hsub⟩ := hKc.exists_cthickening_subset_open hopen hKsub
  refine ⟨δ, hδ, fun s hs hre hs1 => ?_⟩
  by_cases hle : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re hle
  · push Not at hle
    have hp : (1 : ℂ) + (s.im : ℂ) * I ∈ K := ⟨s.im, abs_le.mp hs, rfl⟩
    have hre1 : ((1 : ℂ) + (s.im : ℂ) * I).re = 1 := by simp
    have him1 : s.im = ((1 : ℂ) + (s.im : ℂ) * I).im := by simp
    have hd : dist s ((1 : ℂ) + (s.im : ℂ) * I) ≤ δ := by
      rw [Complex.dist_of_im_eq him1, Real.dist_eq, hre1, abs_le]
      constructor <;> linarith
    exact hsub (Metric.mem_cthickening_of_dist_le _ _ _ _ hp hd) hs1

end Formalism.ZF

end

end RHLean.Analysis.AlpogeThin
