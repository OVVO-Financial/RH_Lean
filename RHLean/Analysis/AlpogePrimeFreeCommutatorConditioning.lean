import Mathlib

/-!
# A prime-free conditioning test for commutator coercivity

This two-dimensional complex matrix example satisfies the joint-injectivity
hypothesis of `GlobalTheory.T.commutator_coercive_on_annihilator` in
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/`
`CommutatorCoerciveOnAnnihilatorStatement.lean`.

The definition `squaredFrobenius` is literally the same sum as the source
`Formalism.REAL.hs`. The best coercivity constant is `(t^2)⁻¹` for nonzero
real t. At t = 2^(-k) every valid constant is at least 4^k. Thus the
finite-dimensional existence theorem has no parameter-uniform constant.
This tests that actual matrix hypothesis, not the full theta-cover datum.
Mathlib is the only import; no prime or RH hypothesis is used.
-/

noncomputable section

open scoped BigOperators
open Matrix

namespace RHLean.Analysis.NativeCommutatorConditioning

def squaredFrobenius (A : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  ∑ i, ∑ j, ‖A i j‖ ^ 2

def operator (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 0; (t : ℂ), 0]

def anchor : Fin 2 → ℂ := Pi.single 0 1

def probe : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 0, 1]

private theorem first_column_zero (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A *ᵥ anchor = 0) : A 0 0 = 0 ∧ A 1 0 = 0 := by
  have hcol : A.col 0 = 0 := by
    simpa only [anchor, Matrix.mulVec_single_one] using hA
  exact ⟨congrFun hcol 0, congrFun hcol 1⟩

/-- The exact joint-injectivity hypothesis in the source theorem. -/
theorem joint_injective (t : ℝ) (ht : t ≠ 0)
    (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hcomm : A * operator t = operator t * A)
    (hA : A *ᵥ anchor = 0) : A = 0 := by
  obtain ⟨h00, h10⟩ := first_column_zero A hA
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  have h01 : A 0 1 = 0 := by
    have h : A 0 1 * (t : ℂ) = 0 := by
      simpa [operator, Matrix.mul_apply, Fin.sum_univ_two] using
        congrArg (fun B : Matrix (Fin 2) (Fin 2) ℂ => B 0 0) hcomm
    exact (mul_eq_zero.mp h).resolve_right htC
  have h11 : A 1 1 = 0 := by
    have h : A 1 1 * (t : ℂ) = 0 := by
      simpa [operator, Matrix.mul_apply, Fin.sum_univ_two, h00] using
        congrArg (fun B : Matrix (Fin 2) (Fin 2) ℂ => B 1 0) hcomm
    exact (mul_eq_zero.mp h).resolve_right htC
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]

theorem energy_on_annihilator (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A *ᵥ anchor = 0) :
    squaredFrobenius A = ‖A 0 1‖ ^ 2 + ‖A 1 1‖ ^ 2 := by
  obtain ⟨h00, h10⟩ := first_column_zero A hA
  simp [squaredFrobenius, Fin.sum_univ_two, h00, h10]

theorem commutator_energy_on_annihilator (t : ℝ)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A *ᵥ anchor = 0) :
    squaredFrobenius (A * operator t - operator t * A) =
      t ^ 2 * (2 * ‖A 0 1‖ ^ 2 + ‖A 1 1‖ ^ 2) := by
  have h00 := (first_column_zero A hA).1
  simp [squaredFrobenius, operator, Matrix.mul_apply, Matrix.vecMul_apply_eq_sum,
    Fin.sum_univ_two, h00, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs] <;> ring

/-- A valid coercivity constant, with its complete parameter dependence. -/
theorem coercive (t : ℝ) (ht : t ≠ 0)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A *ᵥ anchor = 0) :
    squaredFrobenius A ≤
      (t ^ 2)⁻¹ * squaredFrobenius (A * operator t - operator t * A) := by
  rw [energy_on_annihilator A hA, commutator_energy_on_annihilator t A hA,
    ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 ht), one_mul]
  linarith [sq_nonneg ‖A 0 1‖]

theorem probe_annihilates : probe *ᵥ anchor = 0 := by
  rw [anchor, Matrix.mulVec_single_one]
  ext i
  fin_cases i <;> rfl

theorem probe_energy : squaredFrobenius probe = 1 := by
  norm_num [squaredFrobenius, probe, Fin.sum_univ_two]

theorem probe_commutator_energy (t : ℝ) :
    squaredFrobenius (probe * operator t - operator t * probe) = t ^ 2 := by
  rw [commutator_energy_on_annihilator t probe probe_annihilates]
  norm_num [probe]

/-- The unit-energy probe forces the matching lower bound for every
coercivity constant. The squared-norm convention is essential here. -/
theorem coercivity_constant_lower_bound (t c : ℝ) (ht : t ≠ 0)
    (hc : ∀ A : Matrix (Fin 2) (Fin 2) ℂ, A *ᵥ anchor = 0 →
      squaredFrobenius A ≤
        c * squaredFrobenius (A * operator t - operator t * A)) :
    (t ^ 2)⁻¹ ≤ c := by
  have h := hc probe probe_annihilates
  rw [probe_energy, probe_commutator_energy] at h
  have ht2 : 0 < t ^ 2 := sq_pos_of_ne_zero ht
  simpa only [one_div] using (div_le_iff₀ ht2).mpr h

/-- A fixed two-dimensional family already forces exponential squared
coercivity cost. Dimension alone cannot provide a uniform constant. -/
theorem exponential_constant_lower_bound (k : ℕ) (c : ℝ)
    (hc : ∀ A : Matrix (Fin 2) (Fin 2) ℂ, A *ᵥ anchor = 0 →
      squaredFrobenius A ≤ c * squaredFrobenius
        (A * operator (((2 : ℝ) ^ k)⁻¹) -
          operator (((2 : ℝ) ^ k)⁻¹) * A)) :
    (4 : ℝ) ^ k ≤ c := by
  have ht : ((2 : ℝ) ^ k)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero k (by norm_num))
  have h := coercivity_constant_lower_bound (((2 : ℝ) ^ k)⁻¹) c ht hc
  have hp : ((2 : ℝ) ^ k) ^ 2 = (4 : ℝ) ^ k := by
    rw [← pow_mul, Nat.mul_comm k 2, pow_mul]
    norm_num
  simpa only [inv_pow, inv_inv, hp] using h

end RHLean.Analysis.NativeCommutatorConditioning

/-! ## Explicit kernel axiom audit: expected only standard Lean axioms. -/
#print axioms RHLean.Analysis.NativeCommutatorConditioning.joint_injective
#print axioms RHLean.Analysis.NativeCommutatorConditioning.coercive
#print axioms RHLean.Analysis.NativeCommutatorConditioning.exponential_constant_lower_bound
