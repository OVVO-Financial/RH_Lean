import Mathlib
import RHLean.Analysis.NativePNTEvolvingTailState

noncomputable section

namespace RHLean.Analysis

/-- Generalized one-step PNT contraction driven only by current evolving state. -/
theorem nativePNTError_tail_pointwise_improve_evolving
    (R : Nat -> Real) (hR : NativePNTOneLogRemainderProfile R)
    (N M : Nat) (alpha beta c : Real)
    (hN : 3 <= N)
    (halpha : 0 <= alpha) (hba : beta < alpha) (hc : 0 < c)
    (htail : forall q : Nat, M <= q ->
      |nativePNTError q| <= alpha * (q : Real))
    (hgood : c * (Real.log (N : Real)) ^ 2 <=
      nativeLambdaTwoGoodTailRecipMass N M beta)
    (hcost :
      nativePNTEvolvingTailCost R N M alpha <=
        3 * (((alpha - beta) * c) / 4) *
          (N : Real) * (Real.log (N : Real)) ^ 2) :
    |nativePNTError N| <=
      (alpha - ((alpha - beta) * c) / 4) * (N : Real) := by
  let L : Real := Real.log (N : Real)
  let delta : Real := ((alpha - beta) * c) / 4
  have hab : 0 < alpha - beta := sub_pos.mpr hba
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  have hN0 : 0 <= (N : Real) := by positivity
  have hcoef0 : 0 <= (alpha - beta) * (N : Real) :=
    mul_nonneg hab.le hN0
  have hmul := mul_le_mul_of_nonneg_left hgood hcoef0
  have hdeficit :
      -(alpha - beta) * (N : Real) *
          nativeLambdaTwoGoodTailRecipMass N M beta <=
        -4 * delta * (N : Real) * L ^ 2 := by
    calc
      -(alpha - beta) * (N : Real) *
          nativeLambdaTwoGoodTailRecipMass N M beta =
        -((alpha - beta) * (N : Real) *
          nativeLambdaTwoGoodTailRecipMass N M beta) := by ring
      _ <= -((alpha - beta) * (N : Real) * (c * L ^ 2)) := by
        simpa [L] using neg_le_neg hmul
      _ = -4 * delta * (N : Real) * L ^ 2 := by
        dsimp [delta]
        ring
  have hrec := nativePNTError_abs_log_sq_le_evolving_tail
    R hR N M (by omega) alpha beta halpha htail
  have hcost' :
      nativePNTEvolvingTailCost R N M alpha <=
        3 * delta * (N : Real) * L ^ 2 := by
    simpa [delta, L, mul_assoc] using hcost
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
            4 * delta * (N : Real) * L ^ 2 +
            nativePNTEvolvingTailCost R N M alpha := by
        linarith
      _ <= alpha * (N : Real) * L ^ 2 -
            4 * delta * (N : Real) * L ^ 2 +
            3 * delta * (N : Real) * L ^ 2 := by
        exact add_le_add_left hcost'
          (alpha * (N : Real) * L ^ 2 -
            4 * delta * (N : Real) * L ^ 2)
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
  simpa [delta] using hcancel

/-- Canonical specialization using the exact first Selberg remainder profile. -/
theorem nativePNTError_tail_pointwise_improve_canonical
    (N M : Nat) (alpha beta c : Real)
    (hN : 3 <= N)
    (halpha : 0 <= alpha) (hba : beta < alpha) (hc : 0 < c)
    (htail : forall q : Nat, M <= q ->
      |nativePNTError q| <= alpha * (q : Real))
    (hgood : c * (Real.log (N : Real)) ^ 2 <=
      nativeLambdaTwoGoodTailRecipMass N M beta)
    (hcost :
      nativePNTEvolvingTailCost nativePNTFirstRemainder N M alpha <=
        3 * (((alpha - beta) * c) / 4) *
          (N : Real) * (Real.log (N : Real)) ^ 2) :
    |nativePNTError N| <=
      (alpha - ((alpha - beta) * c) / 4) * (N : Real) := by
  exact nativePNTError_tail_pointwise_improve_evolving
    nativePNTFirstRemainder nativePNTFirstRemainder_profile
    N M alpha beta c hN halpha hba hc htail hgood hcost

end RHLean.Analysis
