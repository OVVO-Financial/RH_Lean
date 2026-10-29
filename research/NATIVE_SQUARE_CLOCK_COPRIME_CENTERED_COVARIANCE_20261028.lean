import Mathlib
import RHLean.Analysis.ElevenWeightOneFirstMoment
import «research.EULER_FRACTIONAL_COUPLED_20261027»

/-!
# Native coprime-modulus square-clock covariance cancellation

This is the TRUE centered fractional-part profile of the quadratic
square clock at modulus d:
  f_d(R) = ((R^2 - 1) mod d)/d - E_{r mod d} ((r^2 - 1) mod d)/d.

It uses the existing RH_Lean arithmetic CRT tensor theorem
coprimeZMod_sum_tensor, not a random-sign or independence assumption.

For coprime d,e the full physical root orbit modulo d*e has EXACTLY
ZERO covariance between these two centered fractional source columns.
Common-prime sectors and the principal means are NOT discarded.
No OAI theorem, Mertens growth assumption, or new exponent is claimed.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

/-- Canonical Euclidean fractional part of the actual R²-1 clock on ZMod d. -/
def nativeEulerRootFractionZMod (d : ℕ) [NeZero d] (r : ZMod d) : ℚ :=
  ((r ^ 2 - 1).val : ℚ) / (d : ℚ)

/-- Actual root residue mean, kept as a separate PRINCIPAL frequency. -/
def nativeEulerRootMean (d : ℕ) [NeZero d] : ℚ :=
  (∑ r : ZMod d, nativeEulerRootFractionZMod d r) / (d : ℚ)

/-- The nonprincipal centered square-root fractional column. -/
def nativeEulerRootCentered (d : ℕ) [NeZero d] (r : ZMod d) : ℚ :=
  nativeEulerRootFractionZMod d r - nativeEulerRootMean d

/-- Each genuinely centered root-period column sums to zero. -/
theorem nativeEulerRootCentered_sum_zero (d : ℕ) [NeZero d] :
    (∑ r : ZMod d, nativeEulerRootCentered d r) = 0 := by
  have hd : (d : ℚ) ≠ 0 := by
    exact_mod_cast (NeZero.ne d)
  have hconst :
      (∑ _r : ZMod d, nativeEulerRootMean d) =
        (d : ℚ) * nativeEulerRootMean d := by
    simp [ZMod.card, nsmul_eq_mul]
  calc
    (∑ r : ZMod d, nativeEulerRootCentered d r) =
      (∑ r : ZMod d, nativeEulerRootFractionZMod d r) -
        (∑ _r : ZMod d, nativeEulerRootMean d) := by
        unfold nativeEulerRootCentered
        rw [Finset.sum_sub_distrib]
    _ = (∑ r : ZMod d, nativeEulerRootFractionZMod d r) -
          (d : ℚ) * nativeEulerRootMean d := by rw [hconst]
    _ = 0 := by
      unfold nativeEulerRootMean
      field_simp [hd] <;> ring

/-- A FULL root orbit kills all centered fractional cross-energy for
    coprime moduli, including genuine composite moduli. This retains the
    correct square-clock in BOTH factors and is a nontrivial zero of
    the complete signed covariance (not an inequality hypothesis). -/
theorem nativeEulerRootCoprimeCovariance_zero
    (d e : ℕ) [NeZero d] [NeZero e]
    (hcop : Nat.Coprime d e) :
    (∑ R : ZMod (d * e),
      nativeEulerRootCentered d ((ZMod.chineseRemainder hcop) R).1 *
      nativeEulerRootCentered e ((ZMod.chineseRemainder hcop) R).2) = 0 := by
  rw [RHLean.Analysis.coprimeZMod_sum_tensor d e hcop
    (nativeEulerRootCentered d) (nativeEulerRootCentered e)]
  rw [nativeEulerRootCentered_sum_zero, nativeEulerRootCentered_sum_zero]
  ring

/-- The cancellation survives the EXACT multiplicative Mobius sign
    attached to the chosen two denominator moduli. -/
theorem nativeEulerRootCoprimeMobiusCovariance_zero
    (d e : ℕ) [NeZero d] [NeZero e]
    (hcop : Nat.Coprime d e) :
    ((ArithmeticFunction.moebius d : ℤ) : ℚ) *
      ((ArithmeticFunction.moebius e : ℤ) : ℚ) *
      (∑ R : ZMod (d * e),
        nativeEulerRootCentered d ((ZMod.chineseRemainder hcop) R).1 *
        nativeEulerRootCentered e ((ZMod.chineseRemainder hcop) R).2) = 0 := by
  rw [nativeEulerRootCoprimeCovariance_zero d e hcop]
  ring

#print axioms nativeEulerRootCentered_sum_zero
#print axioms nativeEulerRootCoprimeCovariance_zero
#print axioms nativeEulerRootCoprimeMobiusCovariance_zero

end RHLean.Proof
