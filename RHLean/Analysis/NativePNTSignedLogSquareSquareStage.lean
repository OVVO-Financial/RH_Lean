import Mathlib
import RHLean.Analysis.NativePNTSignedLogSquareDyadicCell
import RHLean.Analysis.PrimeSieveBaseEightShallowAttack

/-!
# Square-stage realization of the signed log-square cells

This module places the signed `Lambda_2` dyadic cell on the repository's
actual square-block and exact-activity prime-wheel coordinate.

At the complete-square endpoint

`X_t = (t+1)^2 - 1`,

and for a transition cofactor `t/4 < c <= t/2`, the exact active-prime packet
is literally the reciprocal band

`X_t/(2c) < q <= X_t/c`.

Thus the two Chebyshev endpoints in

`Lambda_2(c) * (E(X_t/c) - E(X_t/(2c)))`

are not free reciprocal samples: they are the two endpoints of one genuine
square-stage exact-activity packet.  The final theorems transport the existing
same-sign signed surplus and opposite-sign no-crossing alternative onto this
packet coordinate.  No Selberg remainder is estimated here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

open RHLean.Proof

/-- Region II from the dyadic square-stage packet decomposition:
`t/4 < c <= t/2`. -/
def nativePNTSquareStageTransitionCofactors (t : ℕ) : Finset ℕ :=
  Finset.Icc (t / 4 + 1) (t / 2)

/-- Membership in the transition block gives the upper half-scale condition
needed for the exact-activity lower endpoint to be `X_t/(2c)`. -/
theorem nativePNTSquareStageTransitionCofactor_two_mul_le
    {t c : ℕ} (hc : c ∈ nativePNTSquareStageTransitionCofactors t) :
    2 * c ≤ t := by
  have hcI := Finset.mem_Icc.mp hc
  have hhalf : 2 * (t / 2) ≤ t := by omega
  exact (Nat.mul_le_mul_left 2 hcI.2).trans hhalf

/-- Every transition cofactor is positive once the transition block is
occupied. -/
theorem nativePNTSquareStageTransitionCofactor_pos
    {t c : ℕ} (hc : c ∈ nativePNTSquareStageTransitionCofactors t) :
    0 < c := by
  have hcI := Finset.mem_Icc.mp hc
  omega

/-- Below the half-scale boundary, the square-stage reciprocal predecessor is
already beyond the square-root cutoff. -/
theorem nativePNTSquareStage_sqrt_le_dyadicLower
    (t c : ℕ) (hc : 1 ≤ c) (hct : 2 * c ≤ t) :
    t + 1 ≤ squarePrefixEndpoint t / (2 * c) := by
  have h2cpos : 0 < 2 * c := by omega
  apply (Nat.le_div_iff_mul_le h2cpos).2
  have hmul : (t + 1) * (2 * c) ≤ (t + 1) * t :=
    Nat.mul_le_mul_left (t + 1) hct
  have hlt : (t + 1) * t < (t + 1) * (t + 1) :=
    Nat.mul_lt_mul_of_pos_left (Nat.lt_succ_self t) (by omega)
  have hsq : (t + 1) * (t + 1) = squarePrefixEndpoint t + 1 := by
    simpa [pow_two] using (squarePrefixEndpoint_add_one t).symm
  rw [hsq] at hlt
  omega

/-- **Architecture bridge.**  On the square-stage half-scale range, the
repository's exact active-prime interval is exactly the dyadic reciprocal band
used by the signed log-square cell. -/
theorem exactActivityPrimeInterval_eq_logSquareDyadicBand
    (t c : ℕ) (hc : 1 ≤ c) (hct : 2 * c ≤ t) :
    exactActivityPrimeInterval t c =
      (Finset.Ioc
        (squarePrefixEndpoint t / (2 * c))
        (squarePrefixEndpoint t / c)).filter Nat.Prime := by
  have hcpos : 0 < c := by omega
  rw [exactActivityPrimeInterval_eq_reciprocalPrimeBand t c hcpos]
  unfold primeSieveExactActivityReciprocalPrimeBand
  have hlower := nativePNTSquareStage_sqrt_le_dyadicLower t c hc hct
  rw [max_eq_right hlower]

/-- Transition-block specialization of the exact architecture bridge. -/
theorem exactActivityPrimeInterval_eq_logSquareDyadicBand_of_transition
    {t c : ℕ} (hc : c ∈ nativePNTSquareStageTransitionCofactors t) :
    exactActivityPrimeInterval t c =
      (Finset.Ioc
        (squarePrefixEndpoint t / (2 * c))
        (squarePrefixEndpoint t / c)).filter Nat.Prime := by
  exact exactActivityPrimeInterval_eq_logSquareDyadicBand t c
    (nativePNTSquareStageTransitionCofactor_pos hc)
    (nativePNTSquareStageTransitionCofactor_two_mul_le hc)

/-- The Chebyshev error increment across one exact square-stage activity packet. -/
def nativePNTSquareStageExactActivityErrorIncrement (t c : ℕ) : ℝ :=
  nativePNTError (squarePrefixEndpoint t / c) -
    nativePNTError (squarePrefixEndpoint t / (2 * c))

/-- The positive-kernel dyadic cell is exactly the error increment across the
same two endpoints as the square-stage exact-activity packet. -/
theorem nativePNTLambdaTwoDyadicSignedCell_squareStage_eq
    (t c : ℕ) :
    nativePNTLambdaTwoDyadicSignedCell (squarePrefixEndpoint t) c =
      nativeLambdaTwo c * nativePNTSquareStageExactActivityErrorIncrement t c := by
  rfl

/-- Same-sign beta-bad endpoints of one transition packet release the existing
positive `Lambda_2` local charge, now on the genuine square-stage coordinate. -/
theorem nativePNTSquareStageTransition_absSurplus_ge_of_bad_sameSign
    (t c : ℕ) (beta : ℝ)
    (hc : c ∈ nativePNTSquareStageTransitionCofactors t)
    (hbeta : 0 ≤ beta)
    (hsource :
      beta * ((squarePrefixEndpoint t / c : ℕ) : ℝ) ≤
        |nativePNTError (squarePrefixEndpoint t / c)|)
    (hchild :
      beta * ((squarePrefixEndpoint t / (2 * c) : ℕ) : ℝ) ≤
        |nativePNTError (squarePrefixEndpoint t / (2 * c))|)
    (hsign :
      (0 ≤ nativePNTError (squarePrefixEndpoint t / c) ∧
        0 ≤ nativePNTError (squarePrefixEndpoint t / (2 * c))) ∨
      (nativePNTError (squarePrefixEndpoint t / c) ≤ 0 ∧
        nativePNTError (squarePrefixEndpoint t / (2 * c)) ≤ 0)) :
    2 * beta * ((squarePrefixEndpoint t / (2 * c) : ℕ) : ℝ) *
        nativeLambdaTwo c ≤
      nativePNTLambdaTwoDyadicAbsSurplus (squarePrefixEndpoint t) c := by
  exact nativePNTLambdaTwoDyadicAbsSurplus_ge_of_bad_sameSign
    (squarePrefixEndpoint t) c beta
    (nativePNTSquareStageTransitionCofactor_pos hc) hbeta
    hsource hchild hsign

/-- Opposite-sign transition-packet endpoints force a beta-good integer inside
that very packet span once the native one-step no-crossing inequalities hold. -/
theorem nativePNTSquareStageTransition_exists_good_of_oppositeSign
    (t c : ℕ) (beta : ℝ)
    (hc : c ∈ nativePNTSquareStageTransitionCofactors t)
    (hbeta : 0 < beta)
    (hdown :
      1 < beta *
        (2 * ((squarePrefixEndpoint t / (2 * c) : ℕ) : ℝ) + 1))
    (hup :
      Real.log (((squarePrefixEndpoint t / c) + 1 : ℕ) : ℝ) - 1 <
        beta *
          (2 * ((squarePrefixEndpoint t / (2 * c) : ℕ) : ℝ) + 1))
    (hopposite :
      (nativePNTError (squarePrefixEndpoint t / (2 * c)) ≤ 0 ∧
        0 ≤ nativePNTError (squarePrefixEndpoint t / c)) ∨
      (nativePNTError (squarePrefixEndpoint t / c) ≤ 0 ∧
        0 ≤ nativePNTError (squarePrefixEndpoint t / (2 * c)))) :
    ∃ n ∈ Finset.Icc
        (squarePrefixEndpoint t / (2 * c))
        (squarePrefixEndpoint t / c),
      |nativePNTError n| < beta * (n : ℝ) := by
  have hcpos : 0 < c := nativePNTSquareStageTransitionCofactor_pos hc
  have hct : 2 * c ≤ t :=
    nativePNTSquareStageTransitionCofactor_two_mul_le hc
  have hA : 1 ≤ squarePrefixEndpoint t / (2 * c) := by
    have hsqrt := nativePNTSquareStage_sqrt_le_dyadicLower t c hcpos hct
    omega
  have hAB : squarePrefixEndpoint t / (2 * c) ≤ squarePrefixEndpoint t / c := by
    exact Nat.div_le_div_left (by omega) (by omega)
  exact nativePNTError_exists_beta_good_between_of_oppositeSign
    (squarePrefixEndpoint t / (2 * c))
    (squarePrefixEndpoint t / c) beta hA hAB hbeta hdown hup hopposite

end RHLean.Analysis
