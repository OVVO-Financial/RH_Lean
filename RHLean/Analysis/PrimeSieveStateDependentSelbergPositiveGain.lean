import Mathlib
import RHLean.Analysis.NativePNTEvolvingTailStep
import RHLean.Analysis.NativePNTReciprocalSquareCore

/-!
# State-dependent Selberg positive gain

The evolving PNT architecture reduces the analytic problem to one signed,
finite-scale quantity: the exact net gain from the current state.  This module
makes that arithmetic obligation explicit and proves the deterministic closure
from a power lower bound for the net gain to a power contraction of the slope.

No arithmetic positive-gain estimate is asserted here.  The missing input is
precisely a lower bound for the exact net gain, where the signed LambdaTwo good
mass, exact-activity identities, and evolving prime-wheel residual must enter.
-/

noncomputable section

namespace RHLean.Analysis

/-- Admissible state for the state-dependent Selberg contraction. -/
def PrimeSieveStateDependentSelbergAdmissible
    (R : Nat -> Real) (N M : Nat) (alpha beta : Real) : Prop :=
  NativePNTOneLogRemainderProfile R ∧
    2 <= N ∧
    0 <= alpha ∧
    0 <= beta ∧
    beta < alpha ∧
    (forall q : Nat, M <= q ->
      |nativePNTError q| <= alpha * (q : Real))

/-- The exact state-dependent net gain introduced by the evolving PNT engine. -/
abbrev primeSieveStateDependentSelbergNetGain
    (R : Nat -> Real) (N M : Nat) (alpha beta : Real) : Real :=
  nativePNTEvolvingTailNetGain R N M alpha beta

/-- The exact gain is the signed good-tail deficit minus every current
finite-scale cost. -/
theorem primeSieveStateDependentSelbergNetGain_eq
    (R : Nat -> Real) (N M : Nat) (alpha beta : Real) :
    primeSieveStateDependentSelbergNetGain R N M alpha beta =
      (alpha - beta) * (N : Real) *
          nativeLambdaTwoGoodTailRecipMass N M beta -
        nativePNTEvolvingTailCost R N M alpha := rfl

/-- A power-law positive-gain hypothesis.  We use a positive natural exponent
so that the cubic case `p = 3` connects directly to reciprocal-square growth. -/
def PrimeSieveStateDependentSelbergPositiveGainLaw
    (c : Real) (p : Nat) : Prop :=
  0 < c ∧ 0 < p ∧
    forall (R : Nat -> Real) (N M : Nat) (alpha beta : Real),
      PrimeSieveStateDependentSelbergAdmissible R N M alpha beta ->
      c * alpha ^ p * (N : Real) * (Real.log (N : Real)) ^ 2 <=
        primeSieveStateDependentSelbergNetGain R N M alpha beta

/-- The arithmetic target: some positive power law controls every admissible
state. -/
def PrimeSieveStateDependentSelbergHasPositiveGain : Prop :=
  exists c : Real, exists p : Nat,
    PrimeSieveStateDependentSelbergPositiveGainLaw c p

/-- Component form of the arithmetic obligation.  It is enough for the good
signed deficit to dominate the requested power gain plus the exact evolving
cost. -/
theorem primeSieveStateDependentSelberg_gain_of_component_budget
    (R : Nat -> Real) (N M : Nat) (alpha beta c : Real) (p : Nat)
    (hbudget :
      c * alpha ^ p * (N : Real) * (Real.log (N : Real)) ^ 2 +
          nativePNTEvolvingTailCost R N M alpha <=
        (alpha - beta) * (N : Real) *
          nativeLambdaTwoGoodTailRecipMass N M beta) :
    c * alpha ^ p * (N : Real) * (Real.log (N : Real)) ^ 2 <=
      primeSieveStateDependentSelbergNetGain R N M alpha beta := by
  unfold primeSieveStateDependentSelbergNetGain
    nativePNTEvolvingTailNetGain
  linarith

/-- Deterministic closure: a power lower bound for the exact net gain forces the
state-dependent slope update to contract by at least `c * alpha^p`. -/
theorem primeSieveStateDependentSelberg_slopeUpdate_le
    (R : Nat -> Real) (N M : Nat) (alpha beta c : Real) (p : Nat)
    (hN : 2 <= N)
    (hgain :
      c * alpha ^ p * (N : Real) * (Real.log (N : Real)) ^ 2 <=
        primeSieveStateDependentSelbergNetGain R N M alpha beta) :
    nativePNTEvolvingTailSlopeUpdate R N M alpha beta <=
      alpha - c * alpha ^ p := by
  have hNR : 0 < (N : Real) := by
    exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log (N : Real) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < N by omega)
  have hden : 0 < (N : Real) * (Real.log (N : Real)) ^ 2 :=
    mul_pos hNR (sq_pos_of_pos hlog)
  have hdiv :
      c * alpha ^ p <=
        primeSieveStateDependentSelbergNetGain R N M alpha beta /
          ((N : Real) * (Real.log (N : Real)) ^ 2) := by
    apply (le_div_iff₀ hden).2
    simpa [mul_assoc] using hgain
  unfold nativePNTEvolvingTailSlopeUpdate nativePNTEvolvingTailSlopeGain
  linarith

/-- The same power gain gives the contracted endpoint error bound directly. -/
theorem primeSieveStateDependentSelberg_error_le_power_contraction
    (R : Nat -> Real) (N M : Nat) (alpha beta c : Real) (p : Nat)
    (hadm : PrimeSieveStateDependentSelbergAdmissible R N M alpha beta)
    (hgain :
      c * alpha ^ p * (N : Real) * (Real.log (N : Real)) ^ 2 <=
        primeSieveStateDependentSelbergNetGain R N M alpha beta) :
    |nativePNTError N| <=
      (alpha - c * alpha ^ p) * (N : Real) := by
  rcases hadm with ⟨hR, hN, halpha, _hbeta0, _hbetaAlpha, htail⟩
  exact nativePNTError_tail_pointwise_improve_evolving
    R hR N M alpha beta (c * alpha ^ p)
    hN halpha htail hgain

/-- A positive-gain law closes every admissible state deterministically. -/
theorem primeSieveStateDependentSelberg_positiveGainLaw_slopeUpdate_le
    (c : Real) (p : Nat)
    (hlaw : PrimeSieveStateDependentSelbergPositiveGainLaw c p)
    (R : Nat -> Real) (N M : Nat) (alpha beta : Real)
    (hadm : PrimeSieveStateDependentSelbergAdmissible R N M alpha beta) :
    nativePNTEvolvingTailSlopeUpdate R N M alpha beta <=
      alpha - c * alpha ^ p := by
  rcases hlaw with ⟨_hc, _hp, hgain⟩
  exact primeSieveStateDependentSelberg_slopeUpdate_le
    R N M alpha beta c p hadm.2.1 (hgain R N M alpha beta hadm)

/-- Cubic positive gain is the case that yields reciprocal-square slope growth. -/
def PrimeSieveStateDependentSelbergCubicPositiveGainLaw (c : Real) : Prop :=
  PrimeSieveStateDependentSelbergPositiveGainLaw c 3

/-- Cubic specialization of deterministic state closure. -/
theorem primeSieveStateDependentSelberg_cubic_slopeUpdate_le
    (c : Real)
    (hlaw : PrimeSieveStateDependentSelbergCubicPositiveGainLaw c)
    (R : Nat -> Real) (N M : Nat) (alpha beta : Real)
    (hadm : PrimeSieveStateDependentSelbergAdmissible R N M alpha beta) :
    nativePNTEvolvingTailSlopeUpdate R N M alpha beta <=
      alpha - c * alpha ^ 3 := by
  exact primeSieveStateDependentSelberg_positiveGainLaw_slopeUpdate_le
    c 3 hlaw R N M alpha beta hadm

/-- Reciprocal-square growth survives when each positive cubic step contracts
at least as much as the exact cubic recurrence. -/
theorem inv_sq_rate_of_cubic_contraction_inequality
    (a : Nat -> Real) (C : Real)
    (hC : 0 <= C)
    (hpos : forall n, 0 < a n)
    (hrec : forall n, a (n + 1) <= a n - C * (a n) ^ 3) :
    forall n : Nat,
      1 / (a 0) ^ 2 + 2 * C * (n : Real) <= 1 / (a n) ^ 2 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hcubic : 0 < a n - C * (a n) ^ 3 :=
        lt_of_lt_of_le (hpos (n + 1)) (hrec n)
      have hstep := inv_sq_add_two_mul_le_inv_sq_cubic_step
        (a n) C (hpos n) hC hcubic
      have hsquare :
          (a (n + 1)) ^ 2 <= (a n - C * (a n) ^ 3) ^ 2 := by
        nlinarith [hpos (n + 1), hcubic, hrec n]
      have hinv :
          1 / (a n - C * (a n) ^ 3) ^ 2 <=
            1 / (a (n + 1)) ^ 2 := by
        apply (div_le_div_iff₀ (sq_pos_of_pos hcubic)
          (sq_pos_of_pos (hpos (n + 1)))).2
        simpa using hsquare
      calc
        1 / (a 0) ^ 2 + 2 * C * ((n + 1 : Nat) : Real) =
            (1 / (a 0) ^ 2 + 2 * C * (n : Real)) + 2 * C := by
          push_cast
          ring
        _ <= 1 / (a n) ^ 2 + 2 * C := add_le_add_right ih _
        _ <= 1 / (a n - C * (a n) ^ 3) ^ 2 := hstep
        _ <= 1 / (a (n + 1)) ^ 2 := hinv

/-- Direct quadratic rate for any positive sequence obeying the cubic
contraction inequality. -/
theorem cubic_contraction_inequality_quadratic_rate
    (a : Nat -> Real) (C : Real)
    (hC : 0 <= C)
    (hpos : forall n, 0 < a n)
    (hrec : forall n, a (n + 1) <= a n - C * (a n) ^ 3)
    (n : Nat) :
    2 * C * (n : Real) * (a n) ^ 2 <= 1 := by
  have hinv := inv_sq_rate_of_cubic_contraction_inequality
    a C hC hpos hrec n
  have hbase : 0 <= 1 / (a 0) ^ 2 := by positivity
  have hdrop :
      2 * C * (n : Real) <= 1 / (a n) ^ 2 := by
    linarith
  have hmul := mul_le_mul_of_nonneg_right hdrop (sq_nonneg (a n))
  calc
    2 * C * (n : Real) * (a n) ^ 2 <=
        (1 / (a n) ^ 2) * (a n) ^ 2 := by
      simpa [mul_assoc] using hmul
    _ = 1 := by
      field_simp [ne_of_gt (hpos n)]

/-- Cubic positive gain therefore gives the same quadratic target-slope budget
as the exact cubic recurrence: order `eta^(-2)`. -/
theorem cubic_contraction_inequality_le_eta_of_budget
    (a : Nat -> Real) (C eta : Real)
    (hC : 0 <= C) (heta : 0 < eta)
    (hpos : forall n, 0 < a n)
    (hrec : forall n, a (n + 1) <= a n - C * (a n) ^ 3)
    (n : Nat)
    (hbudget : 1 < 2 * C * (n : Real) * eta ^ 2) :
    a n <= eta := by
  have hrate := cubic_contraction_inequality_quadratic_rate
    a C hC hpos hrec n
  by_contra hnot
  have hetaSlope : eta < a n := lt_of_not_ge hnot
  have hsq : eta ^ 2 <= (a n) ^ 2 :=
    pow_le_pow_left₀ heta.le hetaSlope.le 2
  have hcoef0 : 0 <= 2 * C * (n : Real) := by
    exact mul_nonneg (mul_nonneg (by norm_num) hC) (by positivity)
  have hmul :
      2 * C * (n : Real) * eta ^ 2 <=
        2 * C * (n : Real) * (a n) ^ 2 :=
    mul_le_mul_of_nonneg_left hsq hcoef0
  have hone : 1 < 2 * C * (n : Real) * (a n) ^ 2 :=
    hbudget.trans_le hmul
  linarith

end RHLean.Analysis
