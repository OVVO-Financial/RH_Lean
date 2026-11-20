import Mathlib
import RHLean.Analysis.LogWeightedPrimeExtensionEndpoint
import RHLean.Analysis.RamanujanDivisorBoundary

/-!
# Masullo / RH_Lean: complete finite Euler ghost source

This is a *finite*, unconditional source ledger. It packages the ordinary
von Mangoldt coefficients at the square cutoff in prime-first and
cofactor-first coordinates. No bound, PNT or spectral trace formula follows.

The zero-dependent trace-class/strip-interchange statements in Masullo's
manuscript are NOT imported as axioms; they remain explicit open obligations
in `research/MASULLO_FINITE_TRACE_GHOST_20261120.md`.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

/-- The physical high-prime/cofactor pair (only composite carriers). -/
def masulloGhostPairWeight (R p m : ℕ) : ℝ :=
  if p.Prime ∧ p * m ≤ R ^ 2 - 1 then Λ m else 0

/-- Ghost mass, summing the high-prime carrier first. -/
def masulloGhostPrimeFirst (R : ℕ) : ℝ :=
  ∑ p ∈ Finset.Ioc R (R ^ 2 - 1),
    ∑ m ∈ Finset.Ioc 1 (R - 1), masulloGhostPairWeight R p m

/-- The same complete source, summing the low cofactor first. -/
def masulloGhostCofactorFirst (R : ℕ) : ℝ :=
  ∑ m ∈ Finset.Ioc 1 (R - 1),
    ∑ p ∈ Finset.Ioc R (R ^ 2 - 1), masulloGhostPairWeight R p m

/-- Exact finite Fubini: no absolute-value estimate or dropped carrier. -/
theorem masulloGhostPrimeFirst_eq_cofactorFirst (R : ℕ) :
    masulloGhostPrimeFirst R = masulloGhostCofactorFirst R := by
  unfold masulloGhostPrimeFirst masulloGhostCofactorFirst
  exact Finset.sum_comm

/-- The finite, *literal* number of primes in the high-prime window for `m`. -/
def masulloGhostPrimeMultiplicity (R m : ℕ) : ℝ :=
  ∑ p ∈ Finset.Ioc R (R ^ 2 - 1),
    if p.Prime ∧ p * m ≤ R ^ 2 - 1 then 1 else 0

/-- Cohort form: each `Lambda(m)` is paid by its full actual-prime count. -/
theorem masulloGhostCofactorFirst_eq_weightedMultiplicity (R : ℕ) :
    masulloGhostCofactorFirst R =
      ∑ m ∈ Finset.Ioc 1 (R - 1), Λ m * masulloGhostPrimeMultiplicity R m := by
  unfold masulloGhostCofactorFirst
  apply Finset.sum_congr rfl
  intro m _hm
  unfold masulloGhostPrimeMultiplicity
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases h : p.Prime ∧ p * m ≤ R ^ 2 - 1
  · simp [masulloGhostPairWeight, h]
  · simp [masulloGhostPairWeight, h]

/-- The ghost is nonnegative, but this alone has no RH implication. -/
theorem masulloGhostPrimeFirst_nonneg (R : ℕ) :
    0 ≤ masulloGhostPrimeFirst R := by
  unfold masulloGhostPrimeFirst
  apply Finset.sum_nonneg
  intro p _hp
  apply Finset.sum_nonneg
  intro m _hm
  unfold masulloGhostPairWeight
  split_ifs
  · exact ArithmeticFunction.vonMangoldt_nonneg
  · exact le_refl _

/-- `mu * log = Lambda`, reusing the existing Mathlib zeta/Lambda identity. -/
theorem masulloMoebius_mul_log_eq_lambda :
    (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log = Λ := by
  calc
    (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log =
        (μ : ArithmeticFunction ℝ) *
          (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) * Λ) := by
            rw [ArithmeticFunction.zeta_mul_vonMangoldt]
    _ = ((μ : ArithmeticFunction ℝ) *
          ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)) * Λ := by
            ring
    _ = Λ := by
      rw [ArithmeticFunction.coe_moebius_mul_coe_zeta]
      simp

/-- The log-prime contribution in a nonunit cofactor's retained source is zero. -/
theorem masulloMoebius_divisor_sum_zero {m : ℕ} (hm : 1 < m) :
    (∑ d ∈ m.divisors, (((μ d : ℤ) : ℝ))) = 0 := by
  have h := sum_moebius_divisors_eq_one_or_zero m
  have hm1 : m ≠ 1 := ne_of_gt hm
  rw [if_neg hm1] at h
  exact_mod_cast h

/-- A *formal fibre model* of the retained low-prime-divisor log source.
For the actual carrier `p*m`, identifying this with the low-prime divisor
truncation also requires `p` prime and `m < p`, as explained in the note. -/
def masulloRetainedLogFibre (p m : ℕ) : ℝ :=
  ((μ : ArithmeticFunction ℝ) * ArithmeticFunction.log) m +
    Real.log p * (∑ d ∈ m.divisors, (((μ d : ℤ) : ℝ)))

/-- The model retains exactly `Lambda(m)` for a nonunit cofactor. -/
theorem masulloRetainedLogFibre_eq_lambda (p m : ℕ) (hm : 1 < m) :
    masulloRetainedLogFibre p m = Λ m := by
  unfold masulloRetainedLogFibre
  rw [masulloMoebius_mul_log_eq_lambda, masulloMoebius_divisor_sum_zero hm]
  ring

/-- The omitted high-prime divisor side is the exact negative of the retained
fibre. This is an algebraic model, not a proof of the analytic trace formula. -/
def masulloOmittedLogFibre (m : ℕ) : ℝ :=
  -((μ : ArithmeticFunction ℝ) * ArithmeticFunction.log) m

theorem masulloRetained_add_omitted_eq_zero (p m : ℕ) (hm : 1 < m) :
    masulloRetainedLogFibre p m + masulloOmittedLogFibre m = 0 := by
  rw [masulloRetainedLogFibre_eq_lambda p m hm]
  unfold masulloOmittedLogFibre
  rw [masulloMoebius_mul_log_eq_lambda]
  ring

/-- Finite-dimensional trace of a matrix with named diagonal values.
No biorthogonal norm, nuclearity, or limit interchange is assumed. -/
theorem masulloFiniteMatrixTrace_eq_diagonal {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (f : Fin n → ℂ)
    (hdiag : ∀ i, A i i = f i) :
    Matrix.trace A = ∑ i, f i := by
  change (∑ i : Fin n, A i i) = ∑ i : Fin n, f i
  apply Finset.sum_congr rfl
  intro i _hi
  exact hdiag i

end RHLean.Analysis