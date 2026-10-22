import Mathlib
import «research.VF_919_RESONANT_FIBER_NNS_RECOMBINATION_20261022»

/-!
# Original OAI principal source separated from nonprincipal sextic fibers

R_u = principal physical probe / original row-CONSTANT normer
      - HeckeSignal.signal
H_u = sum of all already compensated, nonprincipal ideal fibers.

The finite weighted energy is exactly
  E(R+H) = E_R + E_H + 2 Re(sum omega R * conj H).
The cross term is paid by Cauchy--Schwarz with the ORIGINAL nonnegative
row weights, without opening R as a sextic character or sending it
through the sixth-power moment machine.

The *source-specific* transfer of original actual_ray_principal_comparison
from its complex physical-probe norm into the entire row-weighted E_R
remains an explicit analytic task. Bounds on a single global signal
do not automatically establish a rowwise principal-energy bound.
-/

noncomputable section
open scoped Classical BigOperators

namespace RHLean.Analysis

/-- The weighted source norms; no unproved arithmetic row bound is hidden. -/
def nnsPrincipalWeightedEnergy {ι : Type*}
    (rows : Finset ι) (omega : ι → ℝ) (R : ι → ℂ) : ℝ :=
  ∑ u ∈ rows, omega u * ‖R u‖ ^ 2

def nnsPrincipalNonprincipalCross {ι : Type*}
    (rows : Finset ι) (omega : ι → ℝ)
    (R H : ι → ℂ) : ℝ :=
  ∑ u ∈ rows, omega u * (R u * star (H u)).re

/-- Exact Hermitian polarization of a pair of original complex amplitudes. -/
theorem nns_principal_nonprincipal_norm_polarization (R H : ℂ) :
    ‖R + H‖ ^ 2 =
      ‖R‖ ^ 2 + ‖H‖ ^ 2 + 2 * (R * star H).re := by
  simp only [Complex.sq_norm, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.conj_re, Complex.conj_im]
  ring

/-- Exact weighted energy, retaining the principal/nonprincipal mixed
    covariance explicitly in NNS Co-minus-Div coordinates. -/
theorem nns_energy_principal_nonprincipal_exact {ι : Type*}
    (rows : Finset ι) (omega : ι → ℝ) (R H : ι → ℂ) :
    (∑ u ∈ rows, omega u * ‖R u + H u‖ ^ 2) =
      nnsPrincipalWeightedEnergy rows omega R +
      nnsPrincipalWeightedEnergy rows omega H +
      2 * nnsPrincipalNonprincipalCross rows omega R H := by
  unfold nnsPrincipalWeightedEnergy nnsPrincipalNonprincipalCross
  calc
    _ = ∑ u ∈ rows, omega u *
       (‖R u‖ ^ 2 + ‖H u‖ ^ 2 +
        2 * (R u * star (H u)).re) := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [nns_principal_nonprincipal_norm_polarization]
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
      ring

/-- The nonnegative weighted absolute mixed mass is bounded by the
    geometric mean of the two weighted energies. Uses the full ORIGINAL
    row-weight array, not equality of phase-sector populations. -/
theorem nns_principal_nonprincipal_weighted_abs_cross_le
    {ι : Type*} (rows : Finset ι)
    (omega : ι → ℝ) (homega : ∀ u ∈ rows, 0 ≤ omega u)
    (R H : ι → ℂ) :
    (∑ u ∈ rows, omega u * ‖R u‖ * ‖H u‖) ≤
      Real.sqrt (nnsPrincipalWeightedEnergy rows omega R) *
      Real.sqrt (nnsPrincipalWeightedEnergy rows omega H) := by
  let ER := nnsPrincipalWeightedEnergy rows omega R
  let EH := nnsPrincipalWeightedEnergy rows omega H
  let K := ∑ u ∈ rows, omega u * ‖R u‖ * ‖H u‖
  have hER : 0 ≤ ER := by
    dsimp [ER, nnsPrincipalWeightedEnergy]
    exact Finset.sum_nonneg (fun u hu => mul_nonneg (homega u hu) (sq_nonneg _))
  have hEH : 0 ≤ EH := by
    dsimp [EH, nnsPrincipalWeightedEnergy]
    exact Finset.sum_nonneg (fun u hu => mul_nonneg (homega u hu) (sq_nonneg _))
  have hK : 0 ≤ K := by
    dsimp [K]
    exact Finset.sum_nonneg (fun u hu =>
      mul_nonneg (mul_nonneg (homega u hu) (norm_nonneg _)) (norm_nonneg _))
  have hCS : K ^ 2 ≤ ER * EH := by
    have h0R : ∀ u ∈ rows, 0 ≤ omega u * ‖R u‖ ^ 2 :=
      fun u hu => mul_nonneg (homega u hu) (sq_nonneg _)
    have h0H : ∀ u ∈ rows, 0 ≤ omega u * ‖H u‖ ^ 2 :=
      fun u hu => mul_nonneg (homega u hu) (sq_nonneg _)
    have hs : ∀ u ∈ rows,
        (omega u * ‖R u‖ * ‖H u‖) ^ 2 ≤
          (omega u * ‖R u‖ ^ 2) *
          (omega u * ‖H u‖ ^ 2) := by
      intro u hu
      exact le_of_eq (by ring)
    exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul rows h0R h0H hs
  have hSquare :
      (Real.sqrt ER * Real.sqrt EH) ^ 2 = ER * EH := by
    rw [mul_pow, Real.sq_sqrt hER, Real.sq_sqrt hEH]
  have hRt : 0 ≤ Real.sqrt ER * Real.sqrt EH :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hKLe : K ≤ Real.sqrt ER * Real.sqrt EH := by
    nlinarith
  exact hKLe

/-- The real signed mixed covariance is automatically bounded by
    Cauchy--Schwarz; no sextic classification of R is needed. -/
theorem nns_principal_nonprincipal_cross_le_geometric
    {ι : Type*} (rows : Finset ι)
    (omega : ι → ℝ) (homega : ∀ u ∈ rows, 0 ≤ omega u)
    (R H : ι → ℂ) :
    nnsPrincipalNonprincipalCross rows omega R H ≤
      Real.sqrt (nnsPrincipalWeightedEnergy rows omega R) *
      Real.sqrt (nnsPrincipalWeightedEnergy rows omega H) := by
  unfold nnsPrincipalNonprincipalCross
  calc
    (∑ u ∈ rows, omega u * (R u * star (H u)).re) ≤
      ∑ u ∈ rows, omega u * ‖R u‖ * ‖H u‖ := by
      apply Finset.sum_le_sum
      intro u hu
      have hc : (R u * star (H u)).re ≤ ‖R u‖ * ‖H u‖ := by
        calc
          _ ≤ |(R u * star (H u)).re| := le_abs_self _
          _ ≤ ‖R u * star (H u)‖ := Complex.abs_re_le_norm _
          _ = _ := by simp only [norm_mul, norm_star]
      exact mul_le_mul_of_nonneg_left hc (homega u hu)
    _ ≤ _ := nns_principal_nonprincipal_weighted_abs_cross_le
      rows omega homega R H

/-- Weighted root-energy triangle; this is the EXACT cross-term
    payment and does not expand the principal signal into sextic columns. -/
theorem nns_energy_principal_nonprincipal_root_bound
    {ι : Type*} (rows : Finset ι)
    (omega : ι → ℝ) (homega : ∀ u ∈ rows, 0 ≤ omega u)
    (R H : ι → ℂ) :
    (∑ u ∈ rows, omega u * ‖R u + H u‖ ^ 2) ≤
      (Real.sqrt (nnsPrincipalWeightedEnergy rows omega R) +
       Real.sqrt (nnsPrincipalWeightedEnergy rows omega H)) ^ 2 := by
  let ER := nnsPrincipalWeightedEnergy rows omega R
  let EH := nnsPrincipalWeightedEnergy rows omega H
  have hER : 0 ≤ ER := by
    dsimp [ER, nnsPrincipalWeightedEnergy]
    exact Finset.sum_nonneg (fun u hu => mul_nonneg (homega u hu) (sq_nonneg _))
  have hEH : 0 ≤ EH := by
    dsimp [EH, nnsPrincipalWeightedEnergy]
    exact Finset.sum_nonneg (fun u hu => mul_nonneg (homega u hu) (sq_nonneg _))
  have hCross := nns_principal_nonprincipal_cross_le_geometric
    rows omega homega R H
  rw [nns_energy_principal_nonprincipal_exact]
  change ER + EH + 2 * nnsPrincipalNonprincipalCross rows omega R H ≤ _
  nlinarith [Real.sq_sqrt hER, Real.sq_sqrt hEH]

/-- User's certificate: E_R<=c_R² T, E_H<=c_H² T and c_R+c_H<=1
    pay BOTH the mixed covariance and the source residual in E<=T.
    Note the essential SQUARED constants; E_R<=c_R*T and
    E_H<=c_H*T with c_R+c_H<=1 would NOT generally suffice. -/
theorem nns_energy_principal_nonprincipal_bound
    {ι : Type*} (rows : Finset ι)
    (omega : ι → ℝ) (homega : ∀ u ∈ rows, 0 ≤ omega u)
    (R H : ι → ℂ) (T cR cH : ℝ)
    (hT : 0 ≤ T) (hcR : 0 ≤ cR) (hcH : 0 ≤ cH)
    (hER : nnsPrincipalWeightedEnergy rows omega R ≤ cR ^ 2 * T)
    (hEH : nnsPrincipalWeightedEnergy rows omega H ≤ cH ^ 2 * T)
    (hbudget : cR + cH ≤ 1) :
    (∑ u ∈ rows, omega u * ‖R u + H u‖ ^ 2) ≤ T := by
  have hErNonneg : 0 ≤ nnsPrincipalWeightedEnergy rows omega R := by
    unfold nnsPrincipalWeightedEnergy
    exact Finset.sum_nonneg (fun u hu => mul_nonneg (homega u hu) (sq_nonneg _))
  have hEhNonneg : 0 ≤ nnsPrincipalWeightedEnergy rows omega H := by
    unfold nnsPrincipalWeightedEnergy
    exact Finset.sum_nonneg (fun u hu => mul_nonneg (homega u hu) (sq_nonneg _))
  have hRootR :
      Real.sqrt (nnsPrincipalWeightedEnergy rows omega R) ≤
        cR * Real.sqrt T := by
    have hsq :
        (Real.sqrt (nnsPrincipalWeightedEnergy rows omega R)) ^ 2 ≤
          (cR * Real.sqrt T) ^ 2 := by
      rw [Real.sq_sqrt hErNonneg, mul_pow, Real.sq_sqrt hT]
      exact hER
    nlinarith [Real.sqrt_nonneg (nnsPrincipalWeightedEnergy rows omega R),
      mul_nonneg hcR (Real.sqrt_nonneg T)]
  have hRootH :
      Real.sqrt (nnsPrincipalWeightedEnergy rows omega H) ≤
        cH * Real.sqrt T := by
    have hsq :
        (Real.sqrt (nnsPrincipalWeightedEnergy rows omega H)) ^ 2 ≤
          (cH * Real.sqrt T) ^ 2 := by
      rw [Real.sq_sqrt hEhNonneg, mul_pow, Real.sq_sqrt hT]
      exact hEH
    nlinarith [Real.sqrt_nonneg (nnsPrincipalWeightedEnergy rows omega H),
      mul_nonneg hcH (Real.sqrt_nonneg T)]
  have hRoot :
      Real.sqrt (nnsPrincipalWeightedEnergy rows omega R) +
        Real.sqrt (nnsPrincipalWeightedEnergy rows omega H) ≤
          Real.sqrt T := by
    calc
      _ ≤ (cR + cH) * Real.sqrt T := by
        nlinarith [hRootR, hRootH]
      _ ≤ 1 * Real.sqrt T :=
        mul_le_mul_of_nonneg_right hbudget (Real.sqrt_nonneg T)
      _ = _ := one_mul _
  calc
    _ ≤
      (Real.sqrt (nnsPrincipalWeightedEnergy rows omega R) +
       Real.sqrt (nnsPrincipalWeightedEnergy rows omega H)) ^ 2 :=
        nns_energy_principal_nonprincipal_root_bound rows omega homega R H
    _ ≤ (Real.sqrt T) ^ 2 := by
      nlinarith [add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _),
        Real.sqrt_nonneg T]
    _ = T := Real.sq_sqrt hT

end RHLean.Analysis

#print axioms RHLean.Analysis.nns_principal_nonprincipal_norm_polarization
#print axioms RHLean.Analysis.nns_energy_principal_nonprincipal_exact
#print axioms RHLean.Analysis.nns_principal_nonprincipal_weighted_abs_cross_le
#print axioms RHLean.Analysis.nns_principal_nonprincipal_cross_le_geometric
#print axioms RHLean.Analysis.nns_energy_principal_nonprincipal_root_bound
#print axioms RHLean.Analysis.nns_energy_principal_nonprincipal_bound
