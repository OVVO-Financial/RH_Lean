import Mathlib
import RHLean.Analysis.AlpogeGzErdosReciprocalHistory
import RHLean.Analysis.NativePNTMobiusMoments
import RHLean.Proof.FinitePartialMoments

/-!
# Complete Alpöge Gz: a SHARP finite native NNS future-tail identity

This is the actual von-Mangoldt/Chebyshev source, not a proxy or a
separately absolute-valued Selberg band.

For every positive natural N,M (in particular N<=M), the difference
Gz(N)/N - Gz(M)/M is EXACTLY the negative of the signed NNS
future-tail difference of the reciprocal Chebyshev error, plus an
explicit Euler--harmonic endpoint correction.

The harmonic endpoint correction is between -1/M and +1/N.
Therefore the complete source has an UNCONDITIONAL one-sided bound
via a SAME-SOURCE signed NNS future tail with numerical error <=1.

This gives a sharp new local bound/reduction without an invented
cohomology presentation or any assumed prime cancellation. It does
NOT itself prove the critical N^(1/2+eps) global estimate: that
would require a uniform SIGNED tail lower bound, not just a
bound on all historical prefixes or the positive increment UPM2.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

/-- The literal original signed Chebyshev error atom of Alpöge Gz. -/
def alpogeGzNativeNNSTailAtom (n : Nat) : Real :=
  nativePNTError n / ((n : Real) * (n + 1 : Real))

/-- The complete signed NNS future tail between endpoints N and M;
no individual absolute values are applied before subtracting. -/
def alpogeGzNativeNNSTail (N M : Nat) : Real :=
    (upperPartialMass (Finset.Icc 1 (M - 1)) alpogeGzNativeNNSTailAtom -
     lowerPartialMass (Finset.Icc 1 (M - 1)) alpogeGzNativeNNSTailAtom) -
    (upperPartialMass (Finset.Icc 1 (N - 1)) alpogeGzNativeNNSTailAtom -
     lowerPartialMass (Finset.Icc 1 (N - 1)) alpogeGzNativeNNSTailAtom)

/-- NNS UPM-LPM is the exact algebraic difference between original
signed Erdős prefixes. Both endpoints are in the original physical
source: no new random, ideal, or matrix population is introduced. -/
theorem alpogeGzNativeNNSTail_eq_prefix_diff (N M : Nat) :
    alpogeGzNativeNNSTail N M =
      nativePNTWeightedErrorMass (M - 1) -
        nativePNTWeightedErrorMass (N - 1) := by
  unfold alpogeGzNativeNNSTail
  rw [upperPartialMass_sub_lowerPartialMass_eq_finiteSignedSum,
      upperPartialMass_sub_lowerPartialMass_eq_finiteSignedSum]
  rfl

/-- The Euler-harmonic difference, with its genuine constant retained. -/
def alpogeGzNativeHarmonicError (N : Nat) : Real :=
  (harmonic N : Real) - Real.log (N : Real) -
    Real.eulerMascheroniConstant

theorem alpogeGzNativeHarmonicError_bounds (N : Nat) (hN : 1 <= N) :
    0 <= alpogeGzNativeHarmonicError N ∧
    alpogeGzNativeHarmonicError N <= 1 / (N : Real) := by
  simpa [alpogeGzNativeHarmonicError, nativeHarmonicLogError] using
    nativeHarmonicLogError_bounds N hN

/-- The exact finite cross-method identity.
For N<=M this is the COMPLETE future signed NNS tail. -/
theorem alpogeGz_eq_NNS_futureTail_and_terminal
    (N M : Nat) (hN : 1 <= N) (hM : 1 <= M) :
    alpogeErdosGz N / (N : Real) =
      alpogeErdosGz M / (M : Real) -
        alpogeGzNativeNNSTail N M +
        alpogeGzNativeHarmonicError N -
        alpogeGzNativeHarmonicError M := by
  have hn : (N : Real) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hm : (M : Real) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  rw [alpogeErdosGz_eq_mul_history N hN,
      alpogeErdosGz_eq_mul_history M hM,
      alpogeGzNativeNNSTail_eq_prefix_diff]
  unfold alpogeErdosCenteredHistory alpogeGzNativeHarmonicError
  field_simp [hn, hm]
  ring

/-- FINITE and unconditional: the entire physical Gz is bounded by
the original signed NNS future tail with an endpoint collar of
exactly one integer unit (not x, sqrt x, or a hidden Selberg cost).
No terminal value is assumed small. -/
theorem alpogeGz_NNS_futureTail_oneSided_le
    (N M : Nat) (hN : 1 <= N) (hM : 1 <= M) :
    alpogeErdosGz N <=
      (N : Real) * (alpogeErdosGz M / (M : Real) -
        alpogeGzNativeNNSTail N M) + 1 := by
  have hn : (0 : Real) < (N : Real) := by exact_mod_cast hN
  have hmBoundN := alpogeGzNativeHarmonicError_bounds N hN
  have hmBoundM := alpogeGzNativeHarmonicError_bounds M hM
  have hEq := alpogeGz_eq_NNS_futureTail_and_terminal N M hN hM
  have hscaled :
      alpogeErdosGz N / (N : Real) <=
        alpogeErdosGz M / (M : Real) -
          alpogeGzNativeNNSTail N M + 1 / (N : Real) := by
    linarith
  rw [div_le_iff₀ hn] at hscaled
  have hunit : (1 / (N : Real)) * (N : Real) = 1 := by
    field_simp [ne_of_gt hn]
  calc
    alpogeErdosGz N <=
        (alpogeErdosGz M / (M : Real) -
          alpogeGzNativeNNSTail N M + 1 / (N : Real)) *
          (N : Real) := hscaled
    _ = (N : Real) *
        (alpogeErdosGz M / (M : Real) -
          alpogeGzNativeNNSTail N M) + 1 := by
      rw [add_mul, hunit]
      ring

/-- A sharper TWO-SIDED finite enclosure retaining the terminal
observable and the signed NNS source exactly. -/
theorem alpogeGz_NNS_futureTail_twoSided
    (N M : Nat) (hN : 1 <= N) (hM : 1 <= M) :
    alpogeErdosGz M / (M : Real) -
        alpogeGzNativeNNSTail N M - 1 / (M : Real) <=
      alpogeErdosGz N / (N : Real) ∧
    alpogeErdosGz N / (N : Real) <=
      alpogeErdosGz M / (M : Real) -
        alpogeGzNativeNNSTail N M + 1 / (N : Real) := by
  have hNerr := alpogeGzNativeHarmonicError_bounds N hN
  have hMerr := alpogeGzNativeHarmonicError_bounds M hM
  rw [alpogeGz_eq_NNS_futureTail_and_terminal N M hN hM]
  constructor <;> linarith

/-- An EXACT if-and-only-if for the desired pointwise bound:
a lower bound on the *full signed future tail*, with no loss of sign.
The terminal Gz(M) is included and MUST be paid or sent to infinity
using an independently proved prime number theorem rate. -/
theorem alpogeGz_upperBound_iff_NNS_tailLower
    (N M : Nat) (hN : 1 <= N) (hM : 1 <= M) (B : Real) :
    alpogeErdosGz N <= B ↔
      alpogeGzNativeNNSTail N M >=
        alpogeErdosGz M / (M : Real) +
        alpogeGzNativeHarmonicError N -
        alpogeGzNativeHarmonicError M -
        B / (N : Real) := by
  have hn : (0 : Real) < (N : Real) := by exact_mod_cast hN
  have hEq := alpogeGz_eq_NNS_futureTail_and_terminal N M hN hM
  constructor
  · intro h
    have hscaled : alpogeErdosGz N / (N : Real) <= B / (N : Real) :=
      (div_le_div_iff_of_pos_right hn).2 h
    linarith
  · intro h
    have hscaled : alpogeErdosGz N / (N : Real) <= B / (N : Real) := by
      linarith
    exact (div_le_div_iff_of_pos_right hn).1 hscaled

end RHLean.Analysis
