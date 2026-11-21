import Mathlib
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import RHLean.Analysis.NativePNTErrorMass
import RHLean.Proof.FinitePartialMoments

/-!
# Alpöge Gz is exactly RH_Lean's centered signed Erdős reciprocal history

This is a literal source-preserving identification, not an imported analytic
bound. It reuses the existing proved `nativePNTWeightedErrorMass_eq` and the
actual von Mangoldt, Chebyshev, and harmonic prefix sums.

Alpöge's integer Gz is
  N * (sum_{d <= N} Lambda(d)/d) - psi(N)
    - N*log(N) + (1+gamma)*N.

The exact arithmetic identity at every N >= 1 is
  Gz(N)/N = nativePNTWeightedErrorMass(N-1)
              + harmonic(N) - log(N) + gamma.

The nontrivial Alpöge ONE-SIDED critical Gz bound therefore translates to a
ONE-SIDED rate of convergence of RH_Lean's own signed reciprocal history,
not an absolute pointwise bound on every Chebyshev-error source. In
particular, the geometrical multiplicity/cost certificates must be applied
to the WHOLE centered prefix, with both signs and all earlier endpoints
retained. No saving of power is claimed by this exact identity alone.
-/

noncomputable section
open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace RHLean.Analysis

/-- The exact analytic observable of the external Alpöge Gz argument,
expressed on the ORIGINAL native von Mangoldt/Chebyshev arithmetic. -/
def alpogeErdosGz (N : ℕ) : ℝ :=
  (N : ℝ) * nativeLambdaRecip N - nativePsi N -
    (N : ℝ) * Real.log (N : ℝ) +
      (1 + Real.eulerMascheroniConstant) * (N : ℝ)

/-- The ORIGINAL signed Erdős reciprocal error mass, plus its exact
harmonic/logarithmic centering. This is a single signed source. -/
def alpogeErdosCenteredHistory (N : ℕ) : ℝ :=
  nativePNTWeightedErrorMass (N - 1) +
    (harmonic N : ℝ) - Real.log (N : ℝ) +
      Real.eulerMascheroniConstant

/-- At the integer successor, the end-point Lambda term cancels
on exactly the same prime-power site in N*LambdaRecip - psi.
Nothing is estimated or discarded. -/
theorem alpogeErdos_lambdaRecip_sub_psi_succ
    (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) * nativeLambdaRecip (n + 1) -
        nativePsi (n + 1) =
      ((n + 1 : ℕ) : ℝ) * nativeLambdaRecip n -
        nativePsi n := by
  rw [nativeLambdaRecip_succ, nativePsi_succ]
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hn]
  ring

/-- EXACT Gz/Erdős reciprocal-historical prefix identity, retaining
the genuine harmonic centering (Euler's constant is not elided). -/
theorem alpogeErdosGz_succ_eq_history
    (n : ℕ) :
    alpogeErdosGz (n + 1) =
      ((n + 1 : ℕ) : ℝ) *
        (nativePNTWeightedErrorMass n +
          (harmonic (n + 1) : ℝ) -
          Real.log (((n + 1 : ℕ) : ℝ)) +
          Real.eulerMascheroniConstant) := by
  have hsource := alpogeErdos_lambdaRecip_sub_psi_succ n
  have hmass := nativePNTWeightedErrorMass_eq n
  unfold alpogeErdosGz
  rw [hsource, hmass]
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hn]
  ring

/-- **Alpöge's Gz equals the native signed reciprocal history times N,
with no hypothesis, smoothing error, or dropped earlier source.** -/
theorem alpogeErdosGz_eq_mul_history
    (N : ℕ) (hN : 1 ≤ N) :
    alpogeErdosGz N =
      (N : ℝ) * alpogeErdosCenteredHistory N := by
  cases N with
  | zero => omega
  | succ n =>
      simpa [alpogeErdosCenteredHistory, Nat.succ_eq_add_one] using
        alpogeErdosGz_succ_eq_history n

/-- The geometrical Gz one-sided bound is exactly a one-sided bound on
the ORIGINAL centered weighted Chebyshev prefix, with scale divided by N.
This uses positivity of N but no cancellation or analytic assumption. -/
theorem alpogeErdosGz_le_iff_history_le
    (N : ℕ) (hN : 1 ≤ N) (B : ℝ) :
    alpogeErdosGz N ≤ B ↔
      alpogeErdosCenteredHistory N ≤ B / (N : ℝ) := by
  rw [alpogeErdosGz_eq_mul_history N hN]
  have hpos : 0 < (N : ℝ) := by exact_mod_cast hN
  constructor
  · intro h
    apply (le_div_iff₀ hpos).2
    simpa [mul_comm] using h
  · intro h
    simpa [mul_comm] using (le_div_iff₀ hpos).1 h

/-- The identical signed-history interpretation at the ORIGINAL square
endpoint X_R=R²-1. This is the observable to which an actual Alpöge
cost certificate must be connected. -/
theorem alpogeErdosGz_square_eq_history
    (R : ℕ) (hR : 2 ≤ R) :
    alpogeErdosGz (R ^ 2 - 1) =
      (((R ^ 2 - 1 : ℕ) : ℝ)) *
        alpogeErdosCenteredHistory (R ^ 2 - 1) := by
  apply alpogeErdosGz_eq_mul_history
  nlinarith

/-- The source-level first-moment UPM-LPM split of Gz at an actual
nonzero integer endpoint. This does not posit or assert a bound. -/
theorem alpogeErdosGz_upm_sub_lpm_history
    (N : ℕ) (hN : 1 ≤ N) :
    positivePart (alpogeErdosGz N) -
        negativePart (alpogeErdosGz N) =
      (N : ℝ) * alpogeErdosCenteredHistory N := by
  rw [positivePart_sub_negativePart,
    alpogeErdosGz_eq_mul_history N hN]

end RHLean.Analysis
