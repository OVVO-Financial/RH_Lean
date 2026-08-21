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

end RHLean.Analysis
