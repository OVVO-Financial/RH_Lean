import Mathlib

/-!
# Derivative-weighted 2 x 2 kernel: exact indefinite determinant

This is a purely algebraic theorem.  The scalar `a` can be *any* real
number, including the horizontal logarithmic derivative of the completed
zeta prefactor.  No analytic or RH hypothesis is used.

The zeta-specific function `alpha` has not yet been defined in the
repository, so the specialization below takes it as a function argument
rather than inventing an analytic definition.
-/

namespace RHLean.Analysis

/-- The determinant depends only on the radial factor and log separation,
and **not** on the diagonal shift `a`. -/
theorem derivative_weighted_kernel_det_algebra (a b ell : ℝ) :
    ( !![a, b * (a + (1 / 2 : ℝ) * ell);
         b * (a + (1 / 2 : ℝ) * ell), b ^ 2 * (a + ell)] :
        Matrix (Fin 2) (Fin 2) ℝ).det =
      -(1 / 4 : ℝ) * b ^ 2 * ell ^ 2 := by
  rw [Matrix.det_fin_two_of]
  ring

/-- Equation (14), universally quantified over the as-yet-unspecified
completed-zeta prefactor `alpha`. -/
theorem derivative_weighted_kernel_indefinite
    (alpha : ℂ → ℝ) (sigma : ℝ) (_hsigma : 0 < sigma) :
    let a := alpha (sigma : ℂ)
    let b := (2 : ℝ) ^ (-sigma)
    let M : Matrix (Fin 2) (Fin 2) ℝ :=
      !![a, b * (a + (1 / 2 : ℝ) * Real.log 2);
         b * (a + (1 / 2 : ℝ) * Real.log 2),
         b ^ 2 * (a + Real.log 2)]
    M.det = -(1 / 4 : ℝ) * b ^ 2 * (Real.log 2) ^ 2 := by
  dsimp
  exact derivative_weighted_kernel_det_algebra
    (alpha (sigma : ℂ)) ((2 : ℝ) ^ (-sigma)) (Real.log 2)

-- Certifies Equation (14) of "RH_Lean: expressing the real directional Gram
-- in arithmetic terms".  Its negative determinant rules out automatic PSD.

end RHLean.Analysis
