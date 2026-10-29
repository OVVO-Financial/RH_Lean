import Mathlib
import Mathlib.NumberTheory.LSeries.Linearity
import «research.MERTENS_EXPONENT_STRIP_MAP»
import «research.OFF_CRITICAL_ZERO_LOW_HIGH_COEFFICIENTS_20261029»

/-!
# Actual Mobius HIGH: reciprocal Euler identity and log derivative algebra

Use the genuinely filtered canonical low/high coefficients, not a synthetic
prime-counting staircase. On Re(s)>1, both Dirichlet sums converge absolutely
and their exact sum is the Euler reciprocal 1/zeta(s).

The LOW sum is already proved absolutely convergent on Re(s)>1/2 in the
preceding module. We therefore define the high meromorphic CANDIDATE by
1/zeta - LOW. This is a meromorphic continuation candidate, not a claim
that the high Dirichlet series converges where zeta has zeros.

The log derivative is proved as exact rational algebra. The separate
complex analytic identification with the von Mangoldt series and
pole/residue multiplicities is addressed in the analytic contract.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators LSeries.notation

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Each HIGH coefficient is a legitimate bounded actual Mobius weight. -/
theorem offcriticalHighCoefficient_norm_le_one (Lambda : ℝ) (m : ℕ) :
    ‖offcriticalHighCoefficient Lambda m‖ ≤ 1 := by
  by_cases h : IsCanonicalHighHeight Lambda (Nat.sqrt m) m
  · simpa [offcriticalHighCoefficient, h] using
      norm_canonicalMoebiusWeight_le_one m
  · simp [offcriticalHighCoefficient, h]

/-- Both genuine LOW and genuine HIGH Dirichlet series converge classically
in the original Euler half-plane. HIGH uses no hypothetical gain. -/
theorem offcriticalHigh_LSeriesSummable_of_one_lt_re
    (Lambda : ℝ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (offcriticalHighCoefficient Lambda) s := by
  apply LSeriesSummable_of_bounded_of_one_lt_re
    (m := (1 : ℝ))
  · intro n _hn
    exact offcriticalHighCoefficient_norm_le_one Lambda n
  · exact hs

/-- Ordinary Euler reciprocal on Re(s)>1. This uses the original
zeta/Mobius product theorem already available in RH_Lean's Mathlib imports. -/
theorem offcriticalActualMobius_LSeries_eq_invZeta
    {s : ℂ} (hs : 1 < s.re) :
    LSeries canonicalMoebiusWeight s = (riemannZeta s)⁻¹ := by
  have hprod : riemannZeta s * LSeries canonicalMoebiusWeight s = 1 := by
    rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs]
    exact ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs
  have hz : riemannZeta s ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hprod
    exact zero_ne_one hprod
  calc
    LSeries canonicalMoebiusWeight s =
        (riemannZeta s)⁻¹ *
          (riemannZeta s * LSeries canonicalMoebiusWeight s) := by
            rw [← mul_assoc, inv_mul_cancel₀ hz, one_mul]
    _ = (riemannZeta s)⁻¹ := by rw [hprod, mul_one]

/-- Exact Euler reciprocal: the true canonical LOW and HIGH coefficients
recombine without synthetic events or loss of signed arithmetic mass. -/
theorem offcriticalLowHigh_LSeries_eq_invZeta
    (Lambda : ℝ) {s : ℂ} (hs : 1 < s.re) :
    LSeries (offcriticalLowCoefficient Lambda) s +
      LSeries (offcriticalHighCoefficient Lambda) s =
        (riemannZeta s)⁻¹ := by
  have hlow : LSeriesSummable (offcriticalLowCoefficient Lambda) s :=
    offcriticalLow_LSeriesSummable Lambda
      (by linarith : (1 : ℝ) / 2 < s.re)
  have hhigh : LSeriesSummable (offcriticalHighCoefficient Lambda) s :=
    offcriticalHigh_LSeriesSummable_of_one_lt_re Lambda hs
  have hsum :
      offcriticalLowCoefficient Lambda +
        offcriticalHighCoefficient Lambda =
          canonicalMoebiusWeight := by
    funext n
    exact offcriticalLow_add_high_eq_moebius Lambda n
  calc
    LSeries (offcriticalLowCoefficient Lambda) s +
        LSeries (offcriticalHighCoefficient Lambda) s =
          LSeries (offcriticalLowCoefficient Lambda +
            offcriticalHighCoefficient Lambda) s :=
              (LSeries_add hlow hhigh).symm
    _ = LSeries canonicalMoebiusWeight s := by rw [hsum]
    _ = (riemannZeta s)⁻¹ :=
      offcriticalActualMobius_LSeries_eq_invZeta hs

/-- LOW has an actual holomorphic function, and this is HIGH's
meromorphic continuation CANDIDATE on the right half-plane. This definition
intentionally uses the analytic reciprocal rather than the divergent
pointwise HIGH series at a hypothetical zero. -/
def offcriticalHighReciprocal (Lambda : ℝ) (s : ℂ) : ℂ :=
  (riemannZeta s)⁻¹ -
    LSeries (offcriticalLowCoefficient Lambda) s

/-- Classical HIGH Dirichlet series equals its meromorphic continuation
candidate on its actual half-plane of absolute convergence. -/
theorem offcriticalHighReciprocal_eq_LSeries
    (Lambda : ℝ) {s : ℂ} (hs : 1 < s.re) :
    offcriticalHighReciprocal Lambda s =
      LSeries (offcriticalHighCoefficient Lambda) s := by
  unfold offcriticalHighReciprocal
  have hpair := offcriticalLowHigh_LSeries_eq_invZeta Lambda hs
  linear_combination -hpair

/-- Away from zeta zeros, LOW plus the HIGH reciprocal continuation
multiplies back to exactly one. No Dirichlet-series convergence at a zero
is assumed. -/
theorem offcriticalHighReciprocal_product
    (Lambda : ℝ) (s : ℂ) (hz : riemannZeta s ≠ 0) :
    riemannZeta s *
        (LSeries (offcriticalLowCoefficient Lambda) s +
          offcriticalHighReciprocal Lambda s) = 1 := by
  unfold offcriticalHighReciprocal
  have hcancel :
      LSeries (offcriticalLowCoefficient Lambda) s +
          ((riemannZeta s)⁻¹ -
            LSeries (offcriticalLowCoefficient Lambda) s) =
        (riemannZeta s)⁻¹ := by ring
  rw [hcancel]
  exact mul_inv_cancel₀ hz

/-- A genuine zeta zero cannot admit a FINITE pointwise reciprocal-product
identity. This is the local algebraic obstruction behind the HIGH pole.
Showing meromorphic pole ORDER requires the analytic zero multiplicity layer. -/
theorem offcriticalZero_forbids_finite_HIGH_reciprocal_identity
    (Lambda : ℝ) (rho : ℂ) (hzero : riemannZeta rho = 0)
    (highValue : ℂ) :
    riemannZeta rho *
      (LSeries (offcriticalLowCoefficient Lambda) rho + highValue) ≠ 1 := by
  simp [hzero]

/-- UNIVERSAL logarithmic-derivative split algebra. The variables z,dz,
low,dlow represent a nonzero Euler value, its derivative, and the
holomorphic LOW value/derivative. The original pole is in the first
fraction; the second is regular whenever 1-z*low is nonzero.

No differentiability is postulated here; this is an exact field identity
to instantiate with derivative rules in the next analytic step. -/
theorem offcritical_logDerivative_split_algebra
    (z dz low dlow : ℂ)
    (hz : z ≠ 0) (hgate : 1 - z * low ≠ 0) :
    -dz / z =
        (-dz - z ^ 2 * dlow) / (z * (1 - z * low)) +
          (dz * low + z * dlow) / (1 - z * low) := by
  field_simp [hz, hgate]
  ring

/-! ## Actual von Mangoldt / zeta logarithmic derivative -/

/-- This is the genuine von Mangoldt signal of the actual integers, with
neither floor-Li events nor synthetic canonical VF prime labels. The identity
is the classical Mathlib Euler-product theorem, with its exact domain. -/
theorem offcriticalVonMangoldt_LSeries_eq_zetaLogDerivative
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s =
      -(deriv riemannZeta s) / riemannZeta s := by
  exact ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs

/-- The LOW/HIGH algebra predicts the exact logarithmic-derivative split
where the true zeta value is nonzero and the HIGH numerator is nonzero.
This preserves the multiplicative Euler product, not only the zero-set
reflection, and is the algebraic step toward the actual-prime theta bridge. -/
theorem offcriticalVonMangoldt_logDerivative_split
    (s : ℂ) (Lambda : ℝ)
    (hz : riemannZeta s ≠ 0)
    (hgate : 1 - riemannZeta s *
        LSeries (offcriticalLowCoefficient Lambda) s ≠ 0) :
    -(deriv riemannZeta s) / riemannZeta s =
      (-(deriv riemannZeta s) -
          (riemannZeta s) ^ 2 *
            deriv (LSeries (offcriticalLowCoefficient Lambda)) s) /
        (riemannZeta s *
          (1 - riemannZeta s *
            LSeries (offcriticalLowCoefficient Lambda) s)) +
      (deriv riemannZeta s *
          LSeries (offcriticalLowCoefficient Lambda) s +
        riemannZeta s *
          deriv (LSeries (offcriticalLowCoefficient Lambda)) s) /
        (1 - riemannZeta s *
          LSeries (offcriticalLowCoefficient Lambda) s) := by
  exact offcritical_logDerivative_split_algebra
    (riemannZeta s) (deriv riemannZeta s)
    (LSeries (offcriticalLowCoefficient Lambda) s)
    (deriv (LSeries (offcriticalLowCoefficient Lambda)) s)
    hz hgate

end RHLean.Proof
