import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import RHLean.Analysis.StrongMertensRecipMomentTransfer

/-!
# Analytic closure of the reciprocal Mobius moments for centered K2

This module is the analytic side of the centered K2 closure.  The finite K2
algebra remains in `K2CenteredFinite` and `K2CenteredClassicalInterface`.

The first step removes the pole of the Riemann zeta function at `1` using
Mathlib's proved limit

`zeta(s) - 1 / (s - 1) -> gamma`.

The resulting regular part is analytic at `1`.  This is the local germ from
which the reciprocal-zeta Taylor coefficients needed by K2 are read.
-/

noncomputable section

open Filter Set Topology
open scoped ArithmeticFunction.Moebius LSeries.notation

namespace RHLean.Analysis

local notation "gammaE" => Real.eulerMascheroniConstant

/-- Zeta with its simple pole at `1` removed and the removable value filled by
Euler's constant. -/
def k2ZetaRegularPart : ℂ → ℂ :=
  Function.update
    (fun s : ℂ => riemannZeta s - 1 / (s - 1))
    (1 : ℂ) (gammaE : ℂ)

@[simp]
theorem k2ZetaRegularPart_one :
    k2ZetaRegularPart 1 = (gammaE : ℂ) := by
  simp [k2ZetaRegularPart]

theorem k2ZetaRegularPart_eq {s : ℂ} (hs : s ≠ 1) :
    k2ZetaRegularPart s = riemannZeta s - 1 / (s - 1) := by
  simp [k2ZetaRegularPart, hs]

/-- The filled regular part is continuous at the removed pole. -/
theorem k2ZetaRegularPart_continuousAt_one :
    ContinuousAt k2ZetaRegularPart (1 : ℂ) := by
  rw [k2ZetaRegularPart]
  exact continuousAt_update_same.mpr tendsto_riemannZeta_sub_one_div

/-- Away from the filled point the regular part is the ordinary differentiable
zeta-minus-pole function. -/
theorem k2ZetaRegularPart_differentiable_punctured :
    ∀ᶠ s : ℂ in 𝓝[≠] (1 : ℂ), DifferentiableAt ℂ k2ZetaRegularPart s := by
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs1 : s ≠ (1 : ℂ) := by
    simpa only [mem_compl_singleton_iff] using hs
  have hbase : DifferentiableAt ℂ
      (fun z : ℂ => riemannZeta z - 1 / (z - 1)) s := by
    refine (differentiableAt_riemannZeta hs1).sub ((differentiableAt_const _).div ?_ ?_)
    · fun_prop
    · exact sub_ne_zero.mpr hs1
  have hne : ({(1 : ℂ)}ᶜ : Set ℂ) ∈ 𝓝 s :=
    isOpen_compl_singleton.mem_nhds hs
  have heq : k2ZetaRegularPart =ᶠ[𝓝 s]
      (fun z : ℂ => riemannZeta z - 1 / (z - 1)) := by
    filter_upwards [hne] with z hz
    exact k2ZetaRegularPart_eq (by
      simpa only [mem_compl_singleton_iff] using hz)
  exact hbase.congr_of_eventuallyEq heq

/-- The pole-removed zeta germ is analytic at `1`. -/
theorem k2ZetaRegularPart_analyticAt_one :
    AnalyticAt ℂ k2ZetaRegularPart (1 : ℂ) :=
  Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    k2ZetaRegularPart_differentiable_punctured
    k2ZetaRegularPart_continuousAt_one

/-- The analytic reciprocal-zeta germ written in terms of the regular part.
At `s = 1` the numerator vanishes and the denominator is `1`. -/
def k2InvZetaRegular (s : ℂ) : ℂ :=
  (s - 1) / (1 + (s - 1) * k2ZetaRegularPart s)

@[simp]
theorem k2InvZetaRegular_one : k2InvZetaRegular 1 = 0 := by
  simp [k2InvZetaRegular]

/-- The regular reciprocal is analytic at the filled point. -/
theorem k2InvZetaRegular_analyticAt_one :
    AnalyticAt ℂ k2InvZetaRegular (1 : ℂ) := by
  have hlin : AnalyticAt ℂ (fun s : ℂ => s - 1) (1 : ℂ) :=
    analyticAt_id.sub analyticAt_const
  have hden : AnalyticAt ℂ
      (fun s : ℂ => 1 + (s - 1) * k2ZetaRegularPart s) (1 : ℂ) :=
    analyticAt_const.add (hlin.mul k2ZetaRegularPart_analyticAt_one)
  unfold k2InvZetaRegular
  exact hlin.fun_div hden (by simp)

/-- On the absolutely convergent half-plane the regular reciprocal is the
ordinary reciprocal of the Riemann zeta function. -/
theorem k2InvZetaRegular_eq_inv_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    k2InvZetaRegular s = (riemannZeta s)⁻¹ := by
  have hs1 : s ≠ (1 : ℂ) := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hz0 : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hden :
      1 + (s - 1) * (riemannZeta s - 1 / (s - 1)) =
        (s - 1) * riemannZeta s := by
    field_simp [hsub]
    ring
  rw [k2InvZetaRegular, k2ZetaRegularPart_eq hs1, hden]
  field_simp [hsub, hz0]

/-- On `re s > 1`, the regular reciprocal is exactly the Mobius L-series. -/
theorem k2InvZetaRegular_eq_moebiusLSeries {s : ℂ} (hs : 1 < s.re) :
    k2InvZetaRegular s = L ↗μ s := by
  rw [k2InvZetaRegular_eq_inv_riemannZeta hs]
  have hprod := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs] at hprod
  have hz0 : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  calc
    (riemannZeta s)⁻¹ = (riemannZeta s)⁻¹ * 1 := by simp
    _ = (riemannZeta s)⁻¹ * (riemannZeta s * L ↗μ s) := by rw [hprod]
    _ = L ↗μ s := by simp [hz0, mul_assoc]

end RHLean.Analysis
