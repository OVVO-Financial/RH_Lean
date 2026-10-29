import Mathlib
import «research.OFF_CRITICAL_ZERO_REALIFIED_SCALE_20261029»
import «research.OFF_CRITICAL_ZERO_HIGH_VF_BRIDGE_20261029»

/-!
# Off-critical Mellin residue transport: rigorous pole-limit algebra

A log derivative at ANY zero of finite multiplicity has a first-order pole
with nonzero residue, even when the original zero is multiple. We formalize
this as the punctured-neighborhood limit of (s-rho)*F(s), which is sufficient
for coarsening residue transport without a contour-integration API.

We PROVE the general holomorphic-defect elimination lemma and the q-scale
eigenresidue conclusion under an explicitly stated coarsening relation.
The nontrivial theta Mellin continuation and correction holomorphy
are separate source obligations: no fake assumption-free zeta residue
theorem is claimed in this file.
-/

noncomputable section

open Filter
open scoped Topology

namespace RHLean.Analysis

/-- The coefficient of (s-rho)^(-1), expressed as a precise punctured-limit
statement. This works for the LOG DERIVATIVE even when zeta has a
multiple zero (the log derivative still has a simple pole). -/
def OffcriticalHasSimplePoleResidue (f : ℂ → ℂ)
    (rho residue : ℂ) : Prop :=
  Tendsto (fun s : ℂ => (s - rho) * f s)
    (𝓝[≠] rho) (𝓝 residue)

/-- The subtraction coordinate converges to zero on a punctured
neighborhood of its center. -/
theorem offcritical_sub_center_tendsto_zero (rho : ℂ) :
    Tendsto (fun s : ℂ => s - rho) (𝓝[≠] rho) (𝓝 0) := by
  have hc : ContinuousAt (fun s : ℂ => s - rho) rho :=
    continuousAt_id.sub continuousAt_const
  have ht : Tendsto (fun s : ℂ => s - rho) (𝓝[≠] rho)
      (𝓝 (rho - rho)) :=
    hc.tendsto.mono_left nhdsWithin_le_nhds
  simpa using ht

/-- Holomorphic (indeed merely continuous) arithmetic corrections contribute
ZERO Laurent residue. This is the exact tool needed for the infinite
within-square-block discretization correction. -/
theorem offcritical_simplePoleResidue_add_regular
    (rho residue : ℂ) (f h : ℂ → ℂ)
    (hf : OffcriticalHasSimplePoleResidue f rho residue)
    (hh : ContinuousAt h rho) :
    OffcriticalHasSimplePoleResidue (fun s => f s + h s) rho
      residue := by
  unfold OffcriticalHasSimplePoleResidue at hf ⊢
  have h0 := offcritical_sub_center_tendsto_zero rho
  have hhlim : Tendsto h (𝓝[≠] rho) (𝓝 (h rho)) :=
    hh.tendsto.mono_left nhdsWithin_le_nhds
  have hcorr : Tendsto (fun s => (s - rho) * h s)
      (𝓝[≠] rho) (𝓝 0) := by
    simpa using h0.mul hhlim
  have hsum := hf.add hcorr
  convert hsum using 1 <;> simp only [zero_add]
  · funext s
    ring

/-- A continuous scaling multiplier evaluates at the pole exactly:
the coefficient scales by multiplier(rho), independently of all
holomorphic error terms. -/
theorem offcritical_simplePoleResidue_scale
    (rho residue : ℂ) (f multiplier : ℂ → ℂ)
    (hf : OffcriticalHasSimplePoleResidue f rho residue)
    (hm : ContinuousAt multiplier rho) :
    OffcriticalHasSimplePoleResidue
      (fun s => multiplier s * f s) rho
      (multiplier rho * residue) := by
  unfold OffcriticalHasSimplePoleResidue at hf ⊢
  have hmlim : Tendsto multiplier (𝓝[≠] rho)
      (𝓝 (multiplier rho)) :=
    hm.tendsto.mono_left nhdsWithin_le_nhds
  have hmul := hmlim.mul hf
  convert hmul using 1
  funext s
  ring

/-- For every positive integer q, this is q^(2s-1), written with the
positive real logarithm to eliminate ambiguous complex-power branches. -/
def offcriticalMellinScale (q : ℕ) (s : ℂ) : ℂ :=
  Complex.exp ((2 * s - 1) * ((Real.log (q : ℝ) : ℝ) : ℂ))

theorem offcriticalMellinScale_continuousAt
    (q : ℕ) (rho : ℂ) :
    ContinuousAt (offcriticalMellinScale q) rho := by
  unfold offcriticalMellinScale
  fun_prop

/-- TRUE algebraic residue transport, for any pair of meromorphic
functions whose difference is a regular within-block correction.
The arithmetic relation itself MUST be proved for the genuine theta
Mellin series before this theorem can be instantiated unconditionally. -/
theorem offcritical_MellinCoarsen_residue_of_regularDefect
    (q : ℕ) (rho residue : ℂ) (f coarse defect : ℂ → ℂ)
    (hres : OffcriticalHasSimplePoleResidue f rho residue)
    (hregular : ContinuousAt defect rho)
    (hcoarse : ∀ s : ℂ,
      coarse s = offcriticalMellinScale q s * f s + defect s) :
    OffcriticalHasSimplePoleResidue coarse rho
      (offcriticalMellinScale q rho * residue) := by
  have hscaled :=
    offcritical_simplePoleResidue_scale rho residue f
      (offcriticalMellinScale q) hres
      (offcriticalMellinScale_continuousAt q rho)
  have hsum :=
    offcritical_simplePoleResidue_add_regular rho
      (offcriticalMellinScale q rho * residue)
      (fun s => offcriticalMellinScale q s * f s)
      defect hscaled hregular
  simpa only [hcoarse] using hsum

end RHLean.Analysis
