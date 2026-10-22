import Mathlib
import «research.VF_919_OAI_GROUPED_HOLDER_SIXTH_SOURCE_20261022»

/-!
# Nonprincipal energy: sixth-moment duality AFTER compensated grouping

b(C) is the grouped and compensated, ROW-INDEPENDENT fiber coefficient,
not an ungrouped raw Hecke ideal coefficient. psi(C,u) is the actual
relative Hecke phase, which may vanish on ramified/non-coprime rows.
The original OAI source-to-(b,psi) identity and the finite sixth-power
mask expansion must be proved separately.

This file proves, for arbitrary finite arrays and original nonnegative
row weights, the EXACT Hermitian duality and analytic composition:

  E_H = sum_u omega(u) |sum_C b(C) psi(C,u)|^2
      = sum_C b(C) sum_u omega(u) psi(C,u) conj(H_u).

Under a source-proved compensated ell^(6/5) bound A and a UNIFORM
Gauss/Poisson sixth-moment root bound with constant K, it proves
    E_H <= (A*K)^2.
The one-sixth power arises BEFORE squaring; the cube-root sixth moment
is the energy bound. This file does NOT assert or import the missing
source-specific Poisson/Gauss bound, whose uniformity in row test
vectors and original conductor geometry is essential.

No RH, final hHigh, SourceMomentsAt or sorry.
-/

noncomputable section
open scoped Classical BigOperators

namespace RHLean.Analysis

def oaiNonprincipalGroupedH {ι κ : Type*}
    (cols : Finset κ) (b : κ → ℂ) (phase : κ → ι → ℂ)
    (u : ι) : ℂ :=
  ∑ C ∈ cols, b C * phase C u

def oaiNonprincipalGroupedEnergy {ι κ : Type*}
    (rows : Finset ι) (cols : Finset κ) (omega : ι → ℝ)
    (b : κ → ℂ) (phase : κ → ι → ℂ) : ℝ :=
  ∑ u ∈ rows, omega u *
    ‖oaiNonprincipalGroupedH cols b phase u‖ ^ 2

/-- REAL original energy is the Hermitian dual moment of the
    POST-GROUPING coefficient b(C), with true row weights. This is
    the exact identity needed BEFORE applying sixth-power Holder. -/
theorem oai_nonprincipal_energy_eq_grouped_dual
    {ι κ : Type*} (rows : Finset ι) (cols : Finset κ)
    (omega : ι → ℝ) (b : κ → ℂ)
    (phase : κ → ι → ℂ) :
    ((oaiNonprincipalGroupedEnergy rows cols omega b phase : ℝ) : ℂ) =
      ∑ C ∈ cols, b C *
        ∑ u ∈ rows, (omega u : ℂ) * phase C u *
          star (oaiNonprincipalGroupedH cols b phase u) := by
  let H := oaiNonprincipalGroupedH cols b phase
  have hPoint (u : ι) :
      ((omega u * ‖H u‖ ^ 2 : ℝ) : ℂ) =
        (omega u : ℂ) * H u * star (H u) := by
    have hm : H u * star (H u) = ((‖H u‖ ^ 2 : ℝ) : ℂ) := by
      simpa only [Complex.star_def] using (Complex.mul_conj' (H u))
    rw [← mul_assoc, hm]
    norm_cast
  unfold oaiNonprincipalGroupedEnergy
  push_cast
  calc
    (∑ u ∈ rows, ((omega u * ‖H u‖ ^ 2 : ℝ) : ℂ)) =
      ∑ u ∈ rows, (omega u : ℂ) * H u * star (H u) := by
      apply Finset.sum_congr rfl
      intro u hu
      exact hPoint u
    _ = ∑ u ∈ rows, ∑ C ∈ cols,
          b C * ((omega u : ℂ) * phase C u * star (H u)) := by
      apply Finset.sum_congr rfl
      intro u hu
      dsimp [H, oaiNonprincipalGroupedH]
      rw [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro C hC
      ring
    _ = ∑ C ∈ cols, ∑ u ∈ rows,
          b C * ((omega u : ℂ) * phase C u * star (H u)) := by
      rw [Finset.sum_comm]
    _ = ∑ C ∈ cols, b C * ∑ u ∈ rows,
          (omega u : ℂ) * phase C u * star (H u) := by
      apply Finset.sum_congr rfl
      intro C hC
      rw [Finset.mul_sum]

/-- A UNIFORM sixth-moment estimate is required for arbitrary
    complex row tests gamma, not merely the conveniently chosen
    physical residual vector. This is precisely the Gauss/Poisson
    operator-norm obligation that the original OAI analysis must
    establish on the actual compensated character family. -/
def oaiUniformCompensatedSixthMoment {ι κ : Type*}
    (rows : Finset ι) (cols : Finset κ) (omega : ι → ℝ)
    (phase : κ → ι → ℂ) (K : ℝ) : Prop :=
  ∀ gamma : ι → ℂ,
    (∑ C ∈ cols,
      ‖∑ u ∈ rows, (omega u : ℂ) * phase C u * star (gamma u)‖ ^
        (6 : ℝ)) ^ (1 / 6 : ℝ) ≤
      K * Real.sqrt (∑ u ∈ rows, omega u * ‖gamma u‖ ^ 2)

/-- Fully non-circular FINITE analytic assembly. hCoeff must be the
    bound for the grouped physical b(C), not the raw ideal columns;
    hSixth must be established by sixth-power Gauss/Poisson on actual
    incomplete conductor boxes. Squared constants and budgets remain
    explicitly visible. -/
theorem oai_nonprincipal_energy_bound
    {ι κ : Type*} (rows : Finset ι) (cols : Finset κ)
    (omega : ι → ℝ) (homega : ∀ u ∈ rows, 0 ≤ omega u)
    (b : κ → ℂ) (phase : κ → ι → ℂ)
    (A K Target : ℝ) (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hCoeff :
      (∑ C ∈ cols, ‖b C‖ ^ (6 / 5 : ℝ)) ^ (5 / 6 : ℝ) ≤ A)
    (hSixth : oaiUniformCompensatedSixthMoment rows cols omega phase K)
    (hBudget : (A * K) ^ 2 ≤ Target) :
    oaiNonprincipalGroupedEnergy rows cols omega b phase ≤ Target := by
  let H : ι → ℂ := oaiNonprincipalGroupedH cols b phase
  let EH : ℝ := oaiNonprincipalGroupedEnergy rows cols omega b phase
  let test : κ → ℂ := fun C =>
    ∑ u ∈ rows, (omega u : ℂ) * phase C u * star (H u)
  have hEH : 0 ≤ EH := by
    dsimp [EH, oaiNonprincipalGroupedEnergy]
    exact Finset.sum_nonneg
      (fun u hu => mul_nonneg (homega u hu) (sq_nonneg _))
  have hDual : ((EH : ℝ) : ℂ) = ∑ C ∈ cols, b C * test C :=
    oai_nonprincipal_energy_eq_grouped_dual rows cols omega b phase
  have hSixthApplied :
      (∑ C ∈ cols, ‖test C‖ ^ (6 : ℝ)) ^ (1 / 6 : ℝ) ≤
        K * Real.sqrt EH := by
    exact hSixth H
  have hNorm :
      ‖∑ C ∈ cols, b C * test C‖ ≤
        A * (K * Real.sqrt EH) :=
    oai_grouped_sixth_holder_of_two_analytic_bounds
      cols b test A (K * Real.sqrt EH) hA hCoeff hSixthApplied
  have hEBound : EH ≤ (A * K) * Real.sqrt EH := by
    have hAbs : ‖((EH : ℝ) : ℂ)‖ = EH := by
      simp [Real.norm_eq_abs, abs_of_nonneg hEH]
    rw [← hDual, hAbs] at hNorm
    nlinarith [hNorm]
  have hroot : Real.sqrt EH ≤ A * K := by
    by_cases hzero : EH = 0
    · simp [hzero, mul_nonneg hA hK]
    · have hpos : 0 < Real.sqrt EH :=
        Real.sqrt_pos.2 (lt_of_le_of_ne hEH (Ne.symm hzero))
      have hsq : Real.sqrt EH * Real.sqrt EH ≤
          (A * K) * Real.sqrt EH := by
        nlinarith [Real.sq_sqrt hEH]
      exact (mul_le_mul_right hpos).mp hsq
  have henergy : EH ≤ (A * K) ^ 2 := by
    nlinarith [Real.sq_sqrt hEH, mul_nonneg hA hK,
      Real.sqrt_nonneg EH]
  exact henergy.trans hBudget

end RHLean.Analysis

#print axioms RHLean.Analysis.oai_nonprincipal_energy_eq_grouped_dual
#print axioms RHLean.Analysis.oai_nonprincipal_energy_bound
