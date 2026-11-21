import Mathlib
import RHLean.Analysis.AlpogeGzErdosReciprocalHistory
import RHLean.Analysis.NativePNTLogSums

/-!
# Direct unconditional one-sided bound on the COMPLETE signed Erdos history

This is the ORIGINAL (not separately triangled) Alpoge Gz:
  Gz(N)=N*(nativePNTWeightedErrorMass(N-1)+H_N-log N+EulerGamma).
The pre-existing native *first* Mertens theorem and exact logarithmic
increment yield a UNIFORM one-step upward-slope bound:
  Gz(N+1)-Gz(N) <= log 4 + 2 + EulerGamma   for all N>=1.
Consequently Gz(M)<=Gz(N)+L*(M-N) at every N<=M.
The original square clock moves by 2R+1 integers, so its complete
one-sided signed-history movement is O(R) unconditionally.

These are genuinely unconditional estimates on the *complete* history
and do not introduce an independent prime/composite compensator.

IMPORTANT: The bound on successive differences does NOT bound Gz(N)
itself at sqrt(N) scale as N tends to infinity. The open task is to
control the *global signed accumulation* of these physical increments
using Alpoge's partner/height/covolume family or native NNS Co/Div.
No RH hypothesis is used and NO RH claim is made.
-/

noncomputable section
namespace RHLean.Analysis

/-- Actual (unconditional) upward slope constant, from the repository's
certified finite Mertens first theorem. -/
def alpogeErdosUpperSlope : ℝ :=
  Real.log (4 : ℝ) + 2 + Real.eulerMascheroniConstant

/-- The complete signed source has an EXACT local recurrence. All
endpoint prime powers cancel inside N*LambdaRecip(N)-psi(N). -/
theorem alpogeErdosGz_succ_sub
    (n : ℕ) :
    alpogeErdosGz (n + 1) - alpogeErdosGz n =
      (nativeLambdaRecip n - Real.log (n : ℝ) +
        Real.eulerMascheroniConstant) + 1 -
      ((n : ℝ) + 1) *
        (Real.log (((n + 1 : ℕ) : ℝ)) - Real.log (n : ℝ)) := by
  have hsource := alpogeErdos_lambdaRecip_sub_psi_succ n
  have hsrc :
      (((n + 1 : ℕ) : ℝ) * nativeLambdaRecip (n + 1) -
          nativePsi (n + 1)) -
      ((n : ℝ) * nativeLambdaRecip n - nativePsi n) =
          nativeLambdaRecip n := by
    push_cast at hsource ⊢
    nlinarith only [hsource]
  unfold alpogeErdosGz
  push_cast
  nlinarith only [hsrc]

/-- The correct-sign, one-step RH-critical movement bound on the
COMPLETE signed prefix, proved directly from native Mertens 1. -/
theorem alpogeErdosGz_succ_le
    (n : ℕ) (hn : 1 ≤ n) :
    alpogeErdosGz (n + 1) ≤
      alpogeErdosGz n + alpogeErdosUpperSlope := by
  have hstep := alpogeErdosGz_succ_sub n
  have hlog := nativeOne_le_succ_mul_log_succ_sub_log n hn
  have hrecip := (nativeLambdaRecip_sub_log_bounds n hn).2
  unfold alpogeErdosUpperSlope
  push_cast at hlog
  linarith

/-- Direct uniform bound for every interval, with its actual length.
No absolute values or replacement of the native Erdos source. -/
theorem alpogeErdosGz_le_of_le
    (N M : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M) :
    alpogeErdosGz M ≤
      alpogeErdosGz N +
        alpogeErdosUpperSlope * (((M - N : ℕ) : ℝ)) := by
  induction M, hNM using Nat.le_induction with
  | base => simp
  | succ M hNM ih =>
      have hstep := alpogeErdosGz_succ_le M (by omega)
      have hdiff : (M + 1) - N = (M - N) + 1 := by omega
      calc
        alpogeErdosGz (M + 1) ≤
            alpogeErdosGz M + alpogeErdosUpperSlope := hstep
        _ ≤ (alpogeErdosGz N +
            alpogeErdosUpperSlope * (((M - N : ℕ) : ℝ))) +
            alpogeErdosUpperSlope := by linarith [ih]
        _ = alpogeErdosGz N +
            alpogeErdosUpperSlope * (((M + 1 - N : ℕ) : ℝ)) := by
          rw [hdiff]
          push_cast
          ring

/-- The direct one-sided rate in the ORIGINAL complete signed Erdős
history coordinate, retaining the scaling N instead of bounding
independent lower/high Selberg pieces. -/
theorem alpogeErdosHistory_scaled_le_of_le
    (N M : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M) :
    (M : ℝ) * alpogeErdosCenteredHistory M ≤
      (N : ℝ) * alpogeErdosCenteredHistory N +
        alpogeErdosUpperSlope * (((M - N : ℕ) : ℝ)) := by
  rw [← alpogeErdosGz_eq_mul_history M (by omega),
      ← alpogeErdosGz_eq_mul_history N hN]
  exact alpogeErdosGz_le_of_le N M hN hNM

/-- RH-critical unconditional *local* improvement: the signed
historical source can rise by at most O(R) between consecutive
original square endpoints, with no hypotheses on distributions. -/
theorem alpogeErdosGz_next_square_le
    (R : ℕ) (hR : 2 ≤ R) :
    alpogeErdosGz ((R + 1) ^ 2 - 1) ≤
      alpogeErdosGz (R ^ 2 - 1) +
        alpogeErdosUpperSlope * ((2 * R + 1 : ℕ) : ℝ) := by
  have hRR : 4 ≤ R ^ 2 := by nlinarith
  have hlow : 1 ≤ R ^ 2 - 1 := by omega
  have hsq : (R + 1) ^ 2 = R ^ 2 + 2 * R + 1 := by ring
  have hle : R ^ 2 - 1 ≤ (R + 1) ^ 2 - 1 := by omega
  have hdiff :
      ((R + 1) ^ 2 - 1) - (R ^ 2 - 1) = 2 * R + 1 := by omega
  simpa only [hdiff] using
    (alpogeErdosGz_le_of_le (R ^ 2 - 1) ((R + 1) ^ 2 - 1)
      hlow hle)

end RHLean.Analysis
