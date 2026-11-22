import Mathlib
import RHLean.Analysis.AlpogeGzErdosReciprocalHistory
import RHLean.Proof.FinitePartialMoments

/-!
# One exact bridge point: native signed NNS history is Alpöge's Gz

The decisive analytic observable of the original Alpöge growth argument
is the real-valued Gz(N). The existing unconditional
  alpogeErdosGz_eq_mul_history
already identifies Gz(N) with RHLean's signed reciprocal Chebyshev history.

Here we write the SAME history directly as native NNS degree-one
UPM-LPM on the ACTUAL arithmetical source
  (psi(n)-n)/(n(n+1)), 1<=n<N
and prove the exact equivalence of EVERY ONE-SIDED bound, including the
globally quantified critical power bound. No determinant, auxiliary
Selmer model, analytic estimate, or external RH theorem is inserted.

This is an equivalence of the complete analytic OBSERVABLE, not a claim
that arbitrary integrals, cochains and prime-power characters are all
isomorphic. The user-supplied external critical bound can be transferred
through this iff, but is not proved by the iff alone.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

/-- The exact signed local source in Alpöge's original Gz (no truncation
besides the original N-1 endpoint, no absolute-value estimate). -/
def alpogeGzNNSSource (n : Nat) : Real :=
  nativePNTError n / ((n : Real) * (n + 1 : Real))

/-- The degree-one NNS positive channel of the original historical
signed source, with every integer site retained. -/
def alpogeGzNNSUpper (N : Nat) : Real :=
  upperPartialMass (Finset.Icc 1 (N - 1)) alpogeGzNNSSource

/-- The matching NNS negative channel, at precisely the same sites. -/
def alpogeGzNNSLower (N : Nat) : Real :=
  lowerPartialMass (Finset.Icc 1 (N - 1)) alpogeGzNNSSource

/-- The FULL centered history: the Euler-Mascheroni and harmonic
correction is exact and must not be discarded. -/
def alpogeGzNNSHistory (N : Nat) : Real :=
  alpogeGzNNSUpper N - alpogeGzNNSLower N +
    (harmonic N : Real) - Real.log (N : Real) +
    Real.eulerMascheroniConstant

/-- Native NNS reconstructs the EXACT signed reciprocal history,
not merely a numerically similar integral. -/
theorem alpogeGzNNSHistory_eq_centeredHistory (N : Nat) :
    alpogeGzNNSHistory N = alpogeErdosCenteredHistory N := by
  unfold alpogeGzNNSHistory alpogeGzNNSUpper alpogeGzNNSLower
  rw [upperPartialMass_sub_lowerPartialMass_eq_finiteSignedSum]
  rfl

/-- One exact source-preserving bridge between two methods. -/
theorem alpogeGz_eq_exact_NNSHistory (N : Nat) (hN : 1 <= N) :
    alpogeErdosGz N = (N : Real) * alpogeGzNNSHistory N := by
  rw [alpogeErdosGz_eq_mul_history N hN,
    alpogeGzNNSHistory_eq_centeredHistory]

/-- The critical inequality in Alpöge's Gz coordinate is IFF
the identically scaled inequality on native NNS UPM-LPM. -/
theorem alpogeGz_bound_iff_exact_NNS
    (N : Nat) (hN : 1 <= N) (B : Real) :
    alpogeErdosGz N <= B <->
      alpogeGzNNSHistory N <= B / (N : Real) := by
  rw [alpogeErdosGz_le_iff_history_le N hN B]
  rw [alpogeGzNNSHistory_eq_centeredHistory]

/-- The ENTIRE globally quantified critical bound transfers in BOTH
directions through one exact native analytic observable.
No RH-strength assertion is assumed or proved. -/
theorem alpogeGz_uniformBound_iff_exact_NNS
    (N0 : Nat) (c exponent : Real) :
    (∀ N : Nat, N0 <= N -> 1 <= N ->
      alpogeErdosGz N <= c * (N : Real) ^ exponent) <->
    (∀ N : Nat, N0 <= N -> 1 <= N ->
      alpogeGzNNSHistory N <=
        (c * (N : Real) ^ exponent) / (N : Real)) := by
  constructor
  · intro h N hN0 hN
    exact (alpogeGz_bound_iff_exact_NNS N hN _).mp (h N hN0 hN)
  · intro h N hN0 hN
    exact (alpogeGz_bound_iff_exact_NNS N hN _).mpr (h N hN0 hN)

/-- The original square endpoints are preserved WITHOUT interpolation. -/
theorem alpogeGz_square_iff_exact_NNS
    (R : Nat) (hR : 2 <= R) (B : Real) :
    alpogeErdosGz (R ^ 2 - 1) <= B <->
      alpogeGzNNSHistory (R ^ 2 - 1) <=
        B / ((R ^ 2 - 1 : Nat) : Real) := by
  have hR1 : 1 <= R ^ 2 - 1 := by
    have hsq : 4 <= R ^ 2 := by nlinarith
    omega
  exact alpogeGz_bound_iff_exact_NNS _ hR1 B

end RHLean.Analysis
