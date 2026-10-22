import Mathlib
import «research.VF_919_RESONANT_FIBER_NNS_RECOMBINATION_20261022»

/-!
# Hölder (6/5,6) applied ONLY AFTER resonant-fiber compensation

This is the exact finite scalar duality inequality behind a sextic
character-moment argument. The coefficient is the ALREADY-GROUPED
resonantFiberSum, never the original uncompensated column atom.

The factor from a sixth-moment SUM takes the SIXTH ROOT in a linear
estimate. Squaring the linear estimate produces a THIRD ROOT in energy.
No source-specific bound D^(5/3) Z^(-2 sigma), Poisson/Gauss estimate,
or completed OAI equality is assumed/proved in this file.

The genuinely missing arithmetic inputs are separately:
  - a compensated coefficient ell^(6/5) norm bound;
  - a weighted sixth-power Gauss/Poisson/large-sieve bound;
  - actual original Hecke character / phase identification.
-/

noncomputable section
open scoped Classical BigOperators

namespace RHLean.Analysis

private theorem oai_holder_six_fifths_six :
    Real.HolderConjugate (6 / 5 : ℝ) (6 : ℝ) := by
  constructor <;> norm_num

/-- Exact finite sixth-root Hölder bound for arbitrary complex
    coefficients. No phases, signs or source savings are assumed. -/
theorem oai_compensated_fiber_sixth_holder
    {ι : Type*} (s : Finset ι) (b t : ι → ℂ) :
    ‖∑ i ∈ s, b i * t i‖ ≤
      (∑ i ∈ s, ‖b i‖ ^ (6 / 5 : ℝ)) ^ (5 / 6 : ℝ) *
      (∑ i ∈ s, ‖t i‖ ^ (6 : ℝ)) ^ (1 / 6 : ℝ) := by
  calc
    ‖∑ i ∈ s, b i * t i‖ ≤ ∑ i ∈ s, ‖b i * t i‖ := norm_sum_le _ _
    _ = ∑ i ∈ s, ‖b i‖ * ‖t i‖ := by simp only [norm_mul]
    _ ≤ (∑ i ∈ s, ‖b i‖ ^ (6 / 5 : ℝ)) ^ (5 / 6 : ℝ) *
         (∑ i ∈ s, ‖t i‖ ^ (6 : ℝ)) ^ (1 / 6 : ℝ) := by
      have h := Real.inner_le_Lp_mul_Lq_of_nonneg
        (s := s) (f := fun i => ‖b i‖) (g := fun i => ‖t i‖)
        oai_holder_six_fifths_six
        (fun i _ => norm_nonneg (b i))
        (fun i _ => norm_nonneg (t i))
      simpa only [show (1 : ℝ) / (6 / 5) = 5 / 6 by norm_num] using h

/-- THE DESIRED strict order: the ell^(6/5) norm is built out of
    B_(u,C) = sum of ALL parent, marked-child and other C-labelled
    atoms, with compensation already carried out BEFORE taking norms. -/
theorem oai_grouped_resonant_fibers_sixth_holder
    {ι α κ : Type*} (atoms : Finset α) (classOf : α → κ)
    (a : ι → α → ℂ) (u : ι)
    (test : κ → ℂ) :
    ‖∑ C ∈ resonantFiberClasses atoms classOf,
       resonantFiberSum atoms classOf a u C * test C‖ ≤
      (∑ C ∈ resonantFiberClasses atoms classOf,
        ‖resonantFiberSum atoms classOf a u C‖ ^ (6 / 5 : ℝ)) ^
          (5 / 6 : ℝ) *
      (∑ C ∈ resonantFiberClasses atoms classOf,
        ‖test C‖ ^ (6 : ℝ)) ^ (1 / 6 : ℝ) :=
  oai_compensated_fiber_sixth_holder
    (resonantFiberClasses atoms classOf)
    (resonantFiberSum atoms classOf a u) test

/-- The two analytic estimates are explicit, independent and must be
    proved on the ORIGINAL compensated fibers and actual Hecke tests.
    Multiplication does not manufacture an extra exponent saving. -/
theorem oai_grouped_sixth_holder_of_two_analytic_bounds
    {ι : Type*} (s : Finset ι) (b t : ι → ℂ)
    (A K : ℝ) (hA : 0 ≤ A)
    (hCoeff : (∑ i ∈ s, ‖b i‖ ^ (6 / 5 : ℝ)) ^
      (5 / 6 : ℝ) ≤ A)
    (hSixth : (∑ i ∈ s, ‖t i‖ ^ (6 : ℝ)) ^
      (1 / 6 : ℝ) ≤ K) :
    ‖∑ i ∈ s, b i * t i‖ ≤ A * K := by
  calc
    ‖∑ i ∈ s, b i * t i‖ ≤
        (∑ i ∈ s, ‖b i‖ ^ (6 / 5 : ℝ)) ^ (5 / 6 : ℝ) *
        (∑ i ∈ s, ‖t i‖ ^ (6 : ℝ)) ^ (1 / 6 : ℝ) :=
          oai_compensated_fiber_sixth_holder s b t
    _ ≤ A * (∑ i ∈ s, ‖t i‖ ^ (6 : ℝ)) ^ (1 / 6 : ℝ) := by
      apply mul_le_mul_of_nonneg_right hCoeff
      positivity
    _ ≤ A * K := mul_le_mul_of_nonneg_left hSixth hA

/-- Squaring the already compensated Holder estimate (hence the
    sixth-moment-root contributes ONE THIRD in the energy ledger)
    gives the exact energy acceptance contract. The inequality
    (A*K)^2 <= Target is a VISIBLE analytic exponent budget, not
    something supplied by Holder or by the NNS change of coordinates. -/
theorem oai_compensated_sixth_energy_with_explicit_budget
    {ι : Type*} (s : Finset ι) (b t : ι → ℂ)
    (A K Target : ℝ) (hA : 0 ≤ A)
    (hCoeff : (∑ i ∈ s, ‖b i‖ ^ (6 / 5 : ℝ)) ^
      (5 / 6 : ℝ) ≤ A)
    (hSixth : (∑ i ∈ s, ‖t i‖ ^ (6 : ℝ)) ^
      (1 / 6 : ℝ) ≤ K)
    (hBudget : (A * K) ^ 2 ≤ Target) :
    ‖∑ i ∈ s, b i * t i‖ ^ 2 ≤ Target := by
  have h :=
    oai_grouped_sixth_holder_of_two_analytic_bounds
      s b t A K hA hCoeff hSixth
  have hlo : 0 ≤ ‖∑ i ∈ s, b i * t i‖ := norm_nonneg _
  have hhi : 0 ≤ A * K := le_trans hlo h
  have hSq : ‖∑ i ∈ s, b i * t i‖ ^ 2 ≤ (A * K) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr h) (add_nonneg hlo hhi)]
  exact hSq.trans hBudget

end RHLean.Analysis

#print axioms RHLean.Analysis.oai_compensated_fiber_sixth_holder
#print axioms RHLean.Analysis.oai_grouped_resonant_fibers_sixth_holder
#print axioms RHLean.Analysis.oai_grouped_sixth_holder_of_two_analytic_bounds
#print axioms RHLean.Analysis.oai_compensated_sixth_energy_with_explicit_budget
