import Mathlib
import RHLean.Analysis.NativePNTAxer

/-!
# Alpoge-to-finite-C exact signed von Mangoldt / Mobius source bridge

This module DOES NOT assume a cancellation estimate or import Alpoge's
terminal RH proof. It extracts the exact original Mobius source from the
native RHLean von Mangoldt convolution, with the logarithmic factor kept
until after the convolution has been reassembled.

The weighting theorem is valid for *any* finite physical mask, including
both square-root walls and any of the original owner / inertia filters.
For n >= 2, the exact algebra is

    mu(n) = -(mu * Lambda)(n) / log(n).

This is the necessary native source bridge for testing Alpoge's
character/projector machinery against the original finite-C numerator.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

/-- Pointwise logarithmic inverse of the complete native von Mangoldt
convolution. The formula is asserted only at n >= 2: log 1 = 0. -/
theorem alpogeMobius_eq_neg_mobiusLambda_div_log
    (n : ℕ) (hn : 2 ≤ n) :
    (μ : ArithmeticFunction ℝ) n =
      -(((μ : ArithmeticFunction ℝ) * Λ) n) /
        Real.log (n : ℝ) := by
  have h := congrArg
    (fun f : ArithmeticFunction ℝ => f n)
    arithmeticLogWeight_moebius
  change (μ : ArithmeticFunction ℝ) n * Real.log (n : ℝ) =
    -(((μ : ArithmeticFunction ℝ) * Λ) n) at h
  have hn1 : (1 : ℝ) < (n : ℝ) := by
    exact_mod_cast (show 1 < n by omega)
  have hlog : Real.log (n : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos hn1)
  exact (eq_div_iff hlog).2 h

/-- Exact finite transfer for an arbitrary signed physical weight.
No triangle inequality, character orthogonality, or absolute-value
replacement is used. Every prime power survives in mu*Lambda. -/
theorem alpogeMobius_weighted_eq_mobiusLambda
    (S : Finset ℕ) (w : ℕ → ℝ)
    (hS : ∀ n ∈ S, 2 ≤ n) :
    (∑ n ∈ S, w n * (μ : ArithmeticFunction ℝ) n) =
      -(∑ n ∈ S,
          w n * (((μ : ArithmeticFunction ℝ) * Λ) n) /
            Real.log (n : ℝ)) := by
  calc
    _ = ∑ n ∈ S,
        -(w n * (((μ : ArithmeticFunction ℝ) * Λ) n) /
            Real.log (n : ℝ)) := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [alpogeMobius_eq_neg_mobiusLambda_div_log n (hS n hn)]
          ring
    _ = _ := by rw [Finset.sum_neg_distrib]

/-- Literal two-wall sign used by the finite-C signed Euler source:
the historical wall is R, the physical upper wall is in the summation set. -/
def alpogeMobiusTwoWall (R n : ℕ) : ℝ :=
  if n < R then 1 else -1

/-- The native signed Mobius source with the single n=1 seed separated. -/
def alpogeMobiusTwoWallSource (R : ℕ) : ℝ :=
  1 + ∑ n ∈ Finset.Icc 2 (R ^ 2 - 1),
    alpogeMobiusTwoWall R n * (μ : ArithmeticFunction ℝ) n

/-- The same physical source expressed using Alpoge's native prime-power
von Mangoldt convolution, with its exact divisor compensation included. -/
def alpogeMobiusTwoWallLambdaSource (R : ℕ) : ℝ :=
  1 - ∑ n ∈ Finset.Icc 2 (R ^ 2 - 1),
    alpogeMobiusTwoWall R n *
      (((μ : ArithmeticFunction ℝ) * Λ) n) /
        Real.log (n : ℝ)

/-- Source-faithful finite-C transfer: the two-wall Mobius population is
identical to its complete Lambda-convolution population at every root.
This equality has NO missing conductor/ramification terms, and it alone
asserts no historical-envelope bound. -/
theorem alpogeMobiusTwoWall_eq_lambdaSource (R : ℕ) :
    alpogeMobiusTwoWallSource R =
      alpogeMobiusTwoWallLambdaSource R := by
  unfold alpogeMobiusTwoWallSource alpogeMobiusTwoWallLambdaSource
  have h := alpogeMobius_weighted_eq_mobiusLambda
    (Finset.Icc 2 (R ^ 2 - 1)) (alpogeMobiusTwoWall R)
    (by
      intro n hn
      exact (Finset.mem_Icc.mp hn).1)
  rw [h]
  ring

end RHLean.Analysis
