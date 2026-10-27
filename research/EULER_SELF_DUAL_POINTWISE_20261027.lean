import Mathlib
import «research.MERTENS_FINITE_PREFIX_EXTENSION»

/-!
# Self-dual Euler coefficients below the quadratic support horizon

The coefficient of zeta * (sum_{a<R} mu(a)/a^s)^2 at integer n<R^2
is mu(n) when n<R and -mu(n) when R<=n<R^2.

The proof REUSES the certified Newton finite-prefix theorem. In particular,
the root cutoff is an exact convolution-support fact, NOT a signed estimate.
The formula is intentionally not stated at or above n=R^2.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis.MertensFiniteExtension
open ArithmeticFunction

/-- Genuine historical Möbius prefix, integer Dirichlet coefficients. -/
def eulerSelfDualPrefix (R : ℕ) : ArithmeticFunction ℤ :=
  mobiusPrefix (R - 1)

/-- Coefficient of the *actual* finite Euler zeta-times-square convolution. -/
def eulerSelfDualConvolutionCoefficient (R n : ℕ) : ℤ :=
  ((eulerSelfDualPrefix R * eulerSelfDualPrefix R * zetaInt) n)

/-- Exact coefficient reconstruction below the self-dual horizon.  This
reuses the native Newton coefficient theorem, not an assumed prime model. -/
theorem eulerSelfDualConvolutionCoefficient_eq_signed_moebius
    (R n : ℕ) (hR : 2 ≤ R) (hn : n < R * R) :
    eulerSelfDualConvolutionCoefficient R n =
      if n < R then μ n else -μ n := by
  have hpred : R - 1 + 1 = R := by omega
  have hbelow : n < (R - 1 + 1) * (R - 1 + 1) := by
    simpa only [hpred] using hn
  have hnewton := newtonLift_prefix_exact (N := R - 1) (n := n) hbelow
  unfold newtonLift at hnewton
  change
    mobiusPrefix (R - 1) n + mobiusPrefix (R - 1) n -
      ((mobiusPrefix (R - 1) * mobiusPrefix (R - 1) * zetaInt) n) =
        μ n at hnewton
  have hcoeff :
      ((mobiusPrefix (R - 1) * mobiusPrefix (R - 1) * zetaInt) n) =
        mobiusPrefix (R - 1) n + mobiusPrefix (R - 1) n - μ n := by
    omega
  change ((mobiusPrefix (R - 1) * mobiusPrefix (R - 1) * zetaInt) n) =
    if n < R then μ n else -μ n
  rw [hcoeff]
  by_cases hsmall : n < R
  · have hle : n ≤ R - 1 := by omega
    simp [mobiusPrefix, hle, hsmall]
  · have hnot : ¬ n ≤ R - 1 := by omega
    simp [mobiusPrefix, hnot, hsmall]

/-- The exact coefficient formula specialized to the interior historical
prefix. -/
theorem eulerSelfDualConvolutionCoefficient_eq_moebius_of_lt_root
    (R n : ℕ) (hR : 2 ≤ R) (hn : n < R) :
    eulerSelfDualConvolutionCoefficient R n = μ n := by
  have hRpos : 0 < R := by omega
  have hRlt : R ≤ R * R := by
    nlinarith
  rw [eulerSelfDualConvolutionCoefficient_eq_signed_moebius
    R n hR (lt_of_lt_of_le hn hRlt)]
  simp [hn]

/-- The exact coefficient formula above the root but below the quadratic
support horizon; the sign flips. -/
theorem eulerSelfDualConvolutionCoefficient_eq_neg_moebius_of_root_le
    (R n : ℕ) (hR : 2 ≤ R)
    (hroot : R ≤ n) (hbelow : n < R * R) :
    eulerSelfDualConvolutionCoefficient R n = -μ n := by
  rw [eulerSelfDualConvolutionCoefficient_eq_signed_moebius
    R n hR hbelow]
  simp [Nat.not_lt.mpr hroot]

#print axioms eulerSelfDualConvolutionCoefficient_eq_signed_moebius

end RHLean.Proof
