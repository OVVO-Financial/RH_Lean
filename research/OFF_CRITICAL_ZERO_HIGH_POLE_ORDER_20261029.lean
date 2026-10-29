import Mathlib.Analysis.Meromorphic.Order
import «research.OFF_CRITICAL_ZERO_EULER_LOGDERIV_20261029»

/-!
# Canonical HIGH carries the zeta reciprocal's meromorphic pole ORDER

The genuine fixed-height LOW Dirichlet series has already been proved
analytic on Re(s)>1/2. This module proves that subtracting it cannot
cancel ANY negative-order pole of the true reciprocal 1/zeta.

The pole premise below is deliberately local and structural: it can be
fed by the standard meromorphic-order theorem for a genuine nontrivial
zeta zero. This file does not assert zero existence or an RH-level bound.
-/

noncomputable section

namespace RHLean.Proof

/-- A genuine negative-order zeta reciprocal pole is preserved, with its
EXACT multiplicity, by subtracting the actual analytic canonical LOW series.
This is the correct pole-order theorem for HIGH's continuation, not a
claim that the HIGH Dirichlet series converges at a zero. -/
theorem offcriticalHighReciprocal_preserves_pole_order
    (Lambda : ℝ) (rho : ℂ)
    (hrho : (1 : ℝ) / 2 < rho.re)
    (hpole : meromorphicOrderAt
        (fun s : ℂ => (riemannZeta s)⁻¹) rho < 0) :
    meromorphicOrderAt (offcriticalHighReciprocal Lambda) rho =
      meromorphicOrderAt
        (fun s : ℂ => (riemannZeta s)⁻¹) rho := by
  have hLow : AnalyticAt ℂ
      (LSeries (offcriticalLowCoefficient Lambda)) rho :=
    offcriticalLow_LSeries_analyticAt Lambda hrho
  have hNeg : AnalyticAt ℂ
      (fun s : ℂ => -LSeries (offcriticalLowCoefficient Lambda) s)
      rho := hLow.neg
  have hRegular :
      0 ≤ meromorphicOrderAt
        (fun s : ℂ => -LSeries (offcriticalLowCoefficient Lambda) s)
        rho :=
    hNeg.meromorphicOrderAt_nonneg
  have hlt :
      meromorphicOrderAt (fun s : ℂ => (riemannZeta s)⁻¹)
        rho <
      meromorphicOrderAt
        (fun s : ℂ => -LSeries (offcriticalLowCoefficient Lambda) s)
        rho :=
    lt_of_lt_of_le hpole hRegular
  have hPreserve :=
    meromorphicOrderAt_add_eq_left_of_lt
      (f₁ := fun s : ℂ => (riemannZeta s)⁻¹)
      (f₂ := fun s : ℂ =>
        -LSeries (offcriticalLowCoefficient Lambda) s)
      hNeg.meromorphicAt hlt
  simpa only [offcriticalHighReciprocal, sub_eq_add_neg] using hPreserve

/-- The reciprocal pole order equals the NEGATIVE of the actual zeta order,
provided it is a pole rather than a removable singularity. -/
theorem offcriticalHighReciprocal_order_eq_neg_zeta_order
    (Lambda : ℝ) (rho : ℂ)
    (hrho : (1 : ℝ) / 2 < rho.re)
    (hpole : meromorphicOrderAt
        (fun s : ℂ => (riemannZeta s)⁻¹) rho < 0) :
    meromorphicOrderAt (offcriticalHighReciprocal Lambda) rho =
      -meromorphicOrderAt riemannZeta rho := by
  rw [offcriticalHighReciprocal_preserves_pole_order
    Lambda rho hrho hpole]
  exact meromorphicOrderAt_inv

end RHLean.Proof
