import Mathlib
import RHLean.Analysis.NativePNTEvolvingTailState

noncomputable section

namespace RHLean.Analysis

/-- Exact net contraction resource at the current state: the full good-tail
deficit minus every evolving finite-scale cost.  No fixed fraction of the
deficit is reserved here. -/
def nativePNTEvolvingTailNetGain
    (R : Nat -> Real) (N M : Nat) (alpha beta : Real) : Real :=
  (alpha - beta) * (N : Real) *
      nativeLambdaTwoGoodTailRecipMass N M beta -
    nativePNTEvolvingTailCost R N M alpha

/-- Fully generalized one-step PNT contraction.  Any requested slope drop
`delta` is valid exactly when the current net gain pays for
`delta * N * log(N)^2`.  There is no hard-coded quarter-step, no auxiliary
lower-bound constant for the good mass, and no frozen finite-scale error. -/
theorem nativePNTError_tail_pointwise_improve_evolving
    (R : Nat -> Real) (hR : NativePNTOneLogRemainderProfile R)
    (N M : Nat) (alpha beta delta : Real)
    (hN : 2 <= N)
    (halpha : 0 <= alpha)
    (htail : forall q : Nat, M <= q ->
      |nativePNTError q| <= alpha * (q : Real))
    (hgain :
      delta * (N : Real) * (Real.log (N : Real)) ^ 2 <=
        nativePNTEvolvingTailNetGain R N M alpha beta) :
    |nativePNTError N| <= (alpha - delta) * (N : Real) := by
  let L : Real := Real.log (N : Real)
  have hrec := nativePNTError_abs_log_sq_le_evolving_tail
    R hR N M (by omega) alpha beta halpha htail
  have hgain' :
      delta * (N : Real) * L ^ 2 <=
        (alpha - beta) * (N : Real) *
            nativeLambdaTwoGoodTailRecipMass N M beta -
          nativePNTEvolvingTailCost R N M alpha := by
    simpa [nativePNTEvolvingTailNetGain, L] using hgain
  have hbound :
      |nativePNTError N| * L ^ 2 <=
        (alpha - delta) * (N : Real) * L ^ 2 := by
    have hrec' :
        |nativePNTError N| * L ^ 2 <=
          alpha * (N : Real) * L ^ 2 -
            (alpha - beta) * (N : Real) *
              nativeLambdaTwoGoodTailRecipMass N M beta +
            nativePNTEvolvingTailCost R N M alpha := by
      simpa [L] using hrec
    calc
      |nativePNTError N| * L ^ 2 <=
          alpha * (N : Real) * L ^ 2 -
            (alpha - beta) * (N : Real) *
              nativeLambdaTwoGoodTailRecipMass N M beta +
            nativePNTEvolvingTailCost R N M alpha := hrec'
      _ <= alpha * (N : Real) * L ^ 2 -
            delta * (N : Real) * L ^ 2 := by
        linarith [hgain']
      _ = (alpha - delta) * (N : Real) * L ^ 2 := by ring
  have hL : 0 < L := by
    dsimp [L]
    apply Real.log_pos
    exact_mod_cast (show 1 < N by omega)
  have hLsq : 0 < L ^ 2 := sq_pos_of_pos hL
  have hcancel := (mul_le_mul_iff_left₀ hLsq).mp
    (show |nativePNTError N| * L ^ 2 <=
      ((alpha - delta) * (N : Real)) * L ^ 2 by
        simpa [mul_assoc] using hbound)
  exact hcancel

/-- Positive net-gain budget gives a genuinely strict slope contraction. -/
theorem nativePNTError_tail_pointwise_strict_improve_evolving
    (R : Nat -> Real) (hR : NativePNTOneLogRemainderProfile R)
    (N M : Nat) (alpha beta delta : Real)
    (hN : 2 <= N)
    (halpha : 0 <= alpha) (hdelta : 0 < delta)
    (htail : forall q : Nat, M <= q ->
      |nativePNTError q| <= alpha * (q : Real))
    (hgain :
      delta * (N : Real) * (Real.log (N : Real)) ^ 2 <=
        nativePNTEvolvingTailNetGain R N M alpha beta) :
    alpha - delta < alpha /\
      |nativePNTError N| <= (alpha - delta) * (N : Real) := by
  constructor
  · linarith
  · exact nativePNTError_tail_pointwise_improve_evolving
      R hR N M alpha beta delta hN halpha htail hgain

/-- Canonical specialization using the exact first Selberg remainder profile. -/
theorem nativePNTError_tail_pointwise_improve_canonical
    (N M : Nat) (alpha beta delta : Real)
    (hN : 2 <= N)
    (halpha : 0 <= alpha)
    (htail : forall q : Nat, M <= q ->
      |nativePNTError q| <= alpha * (q : Real))
    (hgain :
      delta * (N : Real) * (Real.log (N : Real)) ^ 2 <=
        nativePNTEvolvingTailNetGain
          nativePNTFirstRemainder N M alpha beta) :
    |nativePNTError N| <= (alpha - delta) * (N : Real) := by
  exact nativePNTError_tail_pointwise_improve_evolving
    nativePNTFirstRemainder nativePNTFirstRemainder_profile
    N M alpha beta delta hN halpha htail hgain

end RHLean.Analysis
