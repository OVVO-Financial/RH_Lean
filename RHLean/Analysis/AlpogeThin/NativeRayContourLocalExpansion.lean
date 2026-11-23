import Mathlib

/-!
# Local pole expansions for the native ray contour

Only the generic analytic prefix is reconstructed: analytic divided differences,
the logarithmic derivative at a zero, and the expansion of the Perron weight.
No Dirichlet L-function or completed-function argument is imported.

Source guide: Levent Alpöge's archive, inspected pin
7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
`src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/AnalyticAtDslope.lean`.
No source compiled artifact or terminal RH theorem is imported.
The archive states no license; attribution assigns none.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Complex MeasureTheory Filter Topology

namespace RHLean.Analysis.AlpogeThin.NativeRay.ExplicitRect

theorem analyticAt_dslope {f : ℂ → ℂ} {p : ℂ} (hf : AnalyticAt ℂ f p) :
    AnalyticAt ℂ (dslope f p) p := by
  obtain ⟨q, hq⟩ := hf
  exact ⟨_, hq.has_fpower_series_dslope_fslope⟩

theorem eq_add_dslope (f : ℂ → ℂ) (p s : ℂ) : f s = f p + (s - p) * dslope f p s := by
  have h := sub_smul_dslope f p s
  rw [smul_eq_mul] at h
  linear_combination -h

theorem logDeriv_pole {f : ℂ → ℂ} {p : ℂ} (hf : AnalyticAt ℂ f p)
    (hn : analyticOrderAt f p ≠ ⊤) : ∃ g : ℂ → ℂ, AnalyticAt ℂ g p ∧ ∀ᶠ s in 𝓝[≠] p,
      deriv f s / f s = ((analyticOrderNatAt f p : ℕ) : ℂ) / (s - p) + g s := by
  obtain ⟨g0, hg0, hg0p, hfg⟩ :=
    (hf.analyticOrderAt_eq_natCast (n := analyticOrderNatAt f p)).mp (Nat.cast_analyticOrderNatAt hn).symm
  generalize analyticOrderNatAt f p = n at hfg ⊢
  refine ⟨fun s => deriv g0 s / g0 s, hg0.deriv.div hg0 hg0p, ?_⟩
  have hne : ∀ᶠ s in 𝓝 p, g0 s ≠ 0 := hg0.continuousAt.eventually_ne hg0p
  have hdiff : ∀ᶠ s in 𝓝 p, DifferentiableAt ℂ g0 s :=
    hg0.eventually_analyticAt.mono fun s hs => hs.differentiableAt
  filter_upwards [nhdsWithin_le_nhds hne, nhdsWithin_le_nhds hfg.eventually_nhds,
    nhdsWithin_le_nhds hdiff, nhdsWithin_le_nhds hfg, self_mem_nhdsWithin] with s h1 h2 h3 h4 h5
  have hsp : s - p ≠ 0 := sub_ne_zero.mpr h5
  have hd : HasDerivAt (fun z => (z - p) ^ n • g0 z)
      ((n : ℂ) * (s - p) ^ (n - 1) * 1 * g0 s + (s - p) ^ n * deriv g0 s) s := by
    have := (((hasDerivAt_id' s).sub_const p).pow n).mul h3.hasDerivAt
    convert this using 1
    all_goals rfl
  have h2' : f =ᶠ[𝓝 s] fun z => (z - p) ^ n • g0 z := h2
  rw [h2'.deriv_eq, h4, hd.deriv, smul_eq_mul]
  rcases n with _ | k
  · simp
  · rw [Nat.add_sub_cancel, pow_succ]
    field_simp

theorem analyticAt_cpow {u : ℝ} (hu : 0 < u) (p : ℂ) :
    AnalyticAt ℂ (fun s : ℂ => (u : ℂ) ^ s) p := analyticAt_const.cpow analyticAt_id (Complex.ofReal_mem_slitPlane.2 hu)

theorem expand_simple {φ g : ℂ → ℂ} {p k : ℂ} {u : ℝ} (hu : 0 < u) (hp : p ≠ 0)
    (hg : AnalyticAt ℂ g p) (hφ : ∀ᶠ s in 𝓝[≠] p, φ s = k / (s - p) + g s) :
    ∃ (a : ℂ) (G : ℂ → ℂ), AnalyticAt ℂ G p ∧ ∀ᶠ s in 𝓝[≠] p,
      -(φ s) * (u : ℂ) ^ s / s = a / (s - p) ^ 2 + (-(k * ((u : ℂ) ^ p / p))) / (s - p) + G s := by
  have hW : AnalyticAt ℂ (fun s : ℂ => (u : ℂ) ^ s / s) p :=
    (analyticAt_cpow hu p).div analyticAt_id hp
  refine ⟨0, fun s => -(k * dslope (fun s : ℂ => (u : ℂ) ^ s / s) p s) - g s * ((u : ℂ) ^ s / s),
    ((analyticAt_const.mul (analyticAt_dslope hW)).neg).sub (hg.mul hW), ?_⟩
  filter_upwards [hφ, self_mem_nhdsWithin] with s hs hsp
  have hsp' : s - p ≠ 0 := sub_ne_zero.mpr hsp
  have hexp : (u : ℂ) ^ s / s = (u : ℂ) ^ p / p + (s - p) * dslope (fun s : ℂ => (u : ℂ) ^ s / s) p s :=
    eq_add_dslope (fun s : ℂ => (u : ℂ) ^ s / s) p s
  rw [hs, mul_div_assoc, hexp]
  field_simp; ring

end RHLean.Analysis.AlpogeThin.NativeRay.ExplicitRect
