import Mathlib
import RHLean.Analysis.NativePNTSignedSecondSelberg

/-!
# Literal Alpoge Gz -> native Euler -> full signed Selberg bridge

The external Formalism.StatementOC definition is:
  Sz(x) = sum_(1<=n<=floor(x)) Lambda(n) * (x/n-1)
  Gz(x) = Sz(x) - x*log(x) + (1+EulerGamma)*x.

At natural x=N the identical finite source is proved equal to native
Chebyshev/reciprocal Lambda coordinates, and thus to the COMPLETE signed
second-Selberg error source, with all prime-pair, prime-square, other K2,
first-Selberg and floor terms. No source inequality or Gz bound is assumed.

The final bound-consumer theorem states the precise paid-source premise.
That premise, the full external analytic/geometric witness family and
a real-x/Landau import remain separate. No RH claim.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

/-- The already-certified finite Euler/Moebius coefficient identity from
PR #1156, reproduced under the native module boundary because this
research closure cannot import flattened research.NAME oleans. -/
theorem alpogeNativeMoebius_mul_log_eq_lambda :
    (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log = Λ := by
  calc
    (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log =
        (μ : ArithmeticFunction ℝ) *
          (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) * Λ) := by
            rw [ArithmeticFunction.zeta_mul_vonMangoldt]
    _ = ((μ : ArithmeticFunction ℝ) *
          ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)) * Λ := by
            ring
    _ = Λ := by
      rw [ArithmeticFunction.coe_moebius_mul_coe_zeta]
      simp

/-- Literal published Gz at a natural endpoint; the finite source of
Formalism.Gz in the RH_Lean mathlib environment. -/
def alpogeLiteralGzInteger (N : ℕ) : ℝ :=
  (∑ n ∈ Finset.Icc 1 N,
      Λ n * ((N : ℝ) / (n : ℝ) - 1)) -
    (N : ℝ) * Real.log (N : ℝ) +
    (1 + Real.eulerMascheroniConstant) * (N : ℝ)


/-- The COMPLETE external Gz function at an ARBITRARY REAL x, not just
at square or natural endpoints. This definition is term-for-term
the published Formalism.StatementOC.Gz in our RH_Lean environment. -/
def alpogeLiteralGzReal (x : ℝ) : ℝ :=
  (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
    Λ n * (x / (n : ℝ) - 1)) -
    x * Real.log x +
    (1 + Real.eulerMascheroniConstant) * x

/-- Exactly the same real-x function, now using native finite
reciprocal-Lambda and psi sums at the integral floor. -/
def alpogeNativeGzReal (x : ℝ) : ℝ :=
  x * nativeLambdaRecip ⌊x⌋₊ - nativePsi ⌊x⌋₊ -
    x * Real.log x + (1 + Real.eulerMascheroniConstant) * x

/-- Term-by-term exact identity even for nonintegral x; no smoothing
loss, jump convention, asymptotic, or Dirichlet character assumption. -/
theorem alpogeNativeGzReal_eq_literal (x : ℝ) :
    alpogeNativeGzReal x = alpogeLiteralGzReal x := by
  have hsource :
      x * nativeLambdaRecip ⌊x⌋₊ - nativePsi ⌊x⌋₊ =
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n * (x / (n : ℝ) - 1) := by
    unfold nativeLambdaRecip nativePsi
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _hn
    ring
  unfold alpogeNativeGzReal alpogeLiteralGzReal
  rw [hsource]

/-- At arbitrary real x, the integer Chebyshev error at floor x
recovers Gz with an EXACT scalar floor correction x-floor(x).
This avoids silently identifying psi(x)-x with psi(floor x)-floor x. -/
theorem alpogeNativeGzReal_eq_floor_error (x : ℝ) :
    alpogeNativeGzReal x =
      x * (nativeLambdaRecip ⌊x⌋₊ - Real.log x +
        Real.eulerMascheroniConstant) -
        nativePNTError ⌊x⌋₊ + (x - (⌊x⌋₊ : ℝ)) := by
  unfold alpogeNativeGzReal nativePNTError
  ring

/-- The native representation of exactly the same integer Gz signal. -/
def alpogeNativeGzInteger (N : ℕ) : ℝ :=
  (N : ℝ) * nativeLambdaRecip N - nativePsi N -
    (N : ℝ) * Real.log (N : ℝ) +
    (1 + Real.eulerMascheroniConstant) * (N : ℝ)

/-- Exact source match: no new character or sign heuristic is required
to identify the analytic Gz observable itself. -/
theorem alpogeNativeGzInteger_eq_literal (N : ℕ) :
    alpogeNativeGzInteger N = alpogeLiteralGzInteger N := by
  have hsource :
      (N : ℝ) * nativeLambdaRecip N - nativePsi N =
        ∑ n ∈ Finset.Icc 1 N,
          Λ n * ((N : ℝ) / (n : ℝ) - 1) := by
    unfold nativeLambdaRecip nativePsi
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _hn
    ring
  unfold alpogeNativeGzInteger alpogeLiteralGzInteger
  rw [hsource]

/-- The same Gz signal in the ORIGINAL Euler/Moebius basis,
using the already certified mu*log=Lambda identity of PR #1156. -/
theorem alpogeNativeGzInteger_eq_moebius (N : ℕ) :
    alpogeNativeGzInteger N =
      (∑ n ∈ Finset.Icc 1 N,
        ((μ : ArithmeticFunction ℝ) * ArithmeticFunction.log) n *
          ((N : ℝ) / (n : ℝ) - 1)) -
        (N : ℝ) * Real.log (N : ℝ) +
        (1 + Real.eulerMascheroniConstant) * (N : ℝ) := by
  rw [alpogeNativeMoebius_mul_log_eq_lambda]
  exact alpogeNativeGzInteger_eq_literal N

/-- Gz equals the FULL reciprocal-Lambda channel minus the ACTUAL
Chebyshev error. This is not a statistical assertion. -/
theorem alpogeNativeGzInteger_eq_reciprocal_sub_error (N : ℕ) :
    alpogeNativeGzInteger N =
      (N : ℝ) *
        (nativeLambdaRecip N - Real.log (N : ℝ) +
          Real.eulerMascheroniConstant) -
        nativePNTError N := by
  unfold alpogeNativeGzInteger nativePNTError
  ring

/-- Exact full signed second-Selberg recurrence in one named source. -/
def alpogeNativeCompleteSecondSelberg (N : ℕ) : ℝ :=
  nativePNTSignedSelbergRemainder N * Real.log (N : ℝ) -
    nativePNTLambdaSignedSelbergRemainderMass N +
    nativePNTSignedSecondSelbergKernelErrorMass N -
    nativePNTLambdaFloorLogSignedDefectMass N

theorem alpogeNativeCompleteSecondSelberg_eq_chebyshev (N : ℕ) :
    alpogeNativeCompleteSecondSelberg N =
      nativePNTError N * (Real.log (N : ℝ)) ^ 2 := by
  unfold alpogeNativeCompleteSecondSelberg
  exact (nativePNTError_mul_log_sq_eq_signedSecondSelberg N).symm

/-- FULL real-x translation of the same external Gz:
one literal reciprocal von Mangoldt channel, the exact scalar floor
correction, and ALL native signed second-Selberg error terms. -/
theorem alpogeNativeGzReal_mul_log_floor_sq (x : ℝ) :
    alpogeNativeGzReal x * (Real.log (⌊x⌋₊ : ℝ)) ^ 2 =
      (x * (nativeLambdaRecip ⌊x⌋₊ - Real.log x +
        Real.eulerMascheroniConstant) + (x - (⌊x⌋₊ : ℝ))) *
        (Real.log (⌊x⌋₊ : ℝ)) ^ 2 -
      alpogeNativeCompleteSecondSelberg ⌊x⌋₊ := by
  rw [alpogeNativeGzReal_eq_floor_error,
    alpogeNativeCompleteSecondSelberg_eq_chebyshev]
  ring

/-- A genuine source-to-analytic observable bridge at every natural x. -/
theorem alpogeNativeGzInteger_mul_log_sq (N : ℕ) :
    alpogeNativeGzInteger N * (Real.log (N : ℝ)) ^ 2 =
      ((N : ℝ) *
        (nativeLambdaRecip N - Real.log (N : ℝ) +
          Real.eulerMascheroniConstant)) *
        (Real.log (N : ℝ)) ^ 2 -
        alpogeNativeCompleteSecondSelberg N := by
  rw [alpogeNativeGzInteger_eq_reciprocal_sub_error,
    alpogeNativeCompleteSecondSelberg_eq_chebyshev]
  ring

/-- The exact native definition of PR #1160's 3R/4 <= p < R
physical prime band. This is local because the research-closure cannot
directly import flattened research oleans. -/
def alpogeNativePrimeBand (R p : ℕ) : Prop :=
  p.Prime ∧ 3 * R ≤ 4 * p ∧ p < R

/-- Every selected site is an ACTUAL product of prime owners. -/
def alpogeNativeBandSite (R n : ℕ) : Prop :=
  ∃ p q : ℕ,
    alpogeNativePrimeBand R p ∧
    alpogeNativePrimeBand R q ∧ n = p * q

/-- Signed K2*E for the selected physical square+semiprime band. -/
def alpogeNativeBandSecondSelberg (R : ℕ) : ℝ := by
  classical
  exact ∑ n ∈ (Finset.Icc 1 (R ^ 2 - 1)).filter (alpogeNativeBandSite R),
    nativePNTSignedSecondSelbergKernel n *
      nativePNTError ((R ^ 2 - 1) / n)

/-- Literally EVERY unselected K2*E term, with its sign. -/
def alpogeNativeOtherSecondSelberg (R : ℕ) : ℝ := by
  classical
  exact ∑ n ∈ (Finset.Icc 1 (R ^ 2 - 1)).filter
      (fun n => ¬ alpogeNativeBandSite R n),
    nativePNTSignedSecondSelbergKernel n *
      nativePNTError ((R ^ 2 - 1) / n)

/-- Exact partition of the FULL K2 mass, with no missing cross-prime term. -/
theorem alpogeNativeK2_mass_eq_band_add_other (R : ℕ) :
    nativePNTSignedSecondSelbergKernelErrorMass (R ^ 2 - 1) =
      alpogeNativeBandSecondSelberg R +
        alpogeNativeOtherSecondSelberg R := by
  classical
  unfold nativePNTSignedSecondSelbergKernelErrorMass
    alpogeNativeBandSecondSelberg alpogeNativeOtherSecondSelberg
  exact (Finset.sum_filter_add_sum_filter_not
    (s := Finset.Icc 1 (R ^ 2 - 1))
    (p := alpogeNativeBandSite R)
    (f := fun n => nativePNTSignedSecondSelbergKernel n *
       nativePNTError ((R ^ 2 - 1) / n))).symm

/-- The COMPLETE signed complement, not a norm and not a mask-only trace. -/
def alpogeNativeFullComplement (R : ℕ) : ℝ :=
  let X := R ^ 2 - 1
  nativePNTSignedSelbergRemainder X * Real.log (X : ℝ) -
    nativePNTLambdaSignedSelbergRemainderMass X +
    alpogeNativeOtherSecondSelberg R -
    nativePNTLambdaFloorLogSignedDefectMass X

/-- The selected band credit is minus the ACTUAL signed K2 term. -/
def alpogeNativeBandCredit (R : ℕ) : ℝ :=
  -alpogeNativeBandSecondSelberg R

/-- Exact signed identity: E(X)*log(X)^2 = C_R-B_R on square endpoints. -/
theorem alpogeNativeError_square_eq_fullComplement_sub_credit (R : ℕ) :
    nativePNTError (R ^ 2 - 1) *
      (Real.log ((R ^ 2 - 1 : ℕ) : ℝ)) ^ 2 =
      alpogeNativeFullComplement R - alpogeNativeBandCredit R := by
  have h := nativePNTError_mul_log_sq_eq_signedSecondSelberg (R ^ 2 - 1)
  rw [alpogeNativeK2_mass_eq_band_add_other] at h
  unfold alpogeNativeFullComplement alpogeNativeBandCredit
  dsimp
  linear_combination h

/-- Literal square-root source-to-Gz bridge, preserving both the
reciprocal-Lambda term and the entire signed complement. -/
theorem alpogeNativeGzSquare_eq_fullSource (R : ℕ) :
    alpogeNativeGzInteger (R ^ 2 - 1) *
      (Real.log ((R ^ 2 - 1 : ℕ) : ℝ)) ^ 2 =
      ((R ^ 2 - 1 : ℕ) : ℝ) *
        (nativeLambdaRecip (R ^ 2 - 1) -
          Real.log ((R ^ 2 - 1 : ℕ) : ℝ) +
          Real.eulerMascheroniConstant) *
        (Real.log ((R ^ 2 - 1 : ℕ) : ℝ)) ^ 2 -
      (alpogeNativeFullComplement R - alpogeNativeBandCredit R) := by
  have h := alpogeNativeError_square_eq_fullComplement_sub_credit R
  rw [alpogeNativeGzInteger_eq_reciprocal_sub_error]
  linear_combination -h

/-- Explicit one-sided Alpoge Gz consumer of the COMPLETE native signed
source. The PAID arithmetic inequality is a premise, not a conjecture
smuggled in as a theorem. -/
theorem alpogeNativeGzSquare_le_of_fullSource
    (R : ℕ) (hR : 2 ≤ R) (M : ℝ)
    (hpaid :
      ((R ^ 2 - 1 : ℕ) : ℝ) *
          (nativeLambdaRecip (R ^ 2 - 1) -
            Real.log ((R ^ 2 - 1 : ℕ) : ℝ) +
            Real.eulerMascheroniConstant) *
          (Real.log ((R ^ 2 - 1 : ℕ) : ℝ)) ^ 2 -
        (alpogeNativeFullComplement R - alpogeNativeBandCredit R) ≤
        M * (Real.log ((R ^ 2 - 1 : ℕ) : ℝ)) ^ 2) :
    alpogeNativeGzInteger (R ^ 2 - 1) ≤ M := by
  have hR4 : 4 ≤ R ^ 2 := by nlinarith
  have hX : 1 < R ^ 2 - 1 := by omega
  have hXreal : (1 : ℝ) < ((R ^ 2 - 1 : ℕ) : ℝ) := by exact_mod_cast hX
  have hLog : 0 < Real.log ((R ^ 2 - 1 : ℕ) : ℝ) :=
    Real.log_pos hXreal
  have hSq : 0 < (Real.log ((R ^ 2 - 1 : ℕ) : ℝ)) ^ 2 :=
    pow_pos hLog _
  have hBound :
      alpogeNativeGzInteger (R ^ 2 - 1) *
          (Real.log ((R ^ 2 - 1 : ℕ) : ℝ)) ^ 2 ≤
        M * (Real.log ((R ^ 2 - 1 : ℕ) : ℝ)) ^ 2 := by
    rw [alpogeNativeGzSquare_eq_fullSource]
    exact hpaid
  exact le_of_mul_le_mul_right hBound hSq

end RHLean.Analysis
