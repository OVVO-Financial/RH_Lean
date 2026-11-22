import Mathlib
import «research.VF_MID_VON_KOCH_BRIDGE»
import «research.VF_MID_LI_UNIFORM_QUADRATURE»
import RHLean.Analysis.AlpogeSignedSquareInterpolation

/-!
# Alpoge Gz: the original real prime delta in VF_mid coordinates

This is the exact, real-cutoff prime-error change of coordinates:
  Delta(t) = pi(t) - Li_2(t)
           = [pi(t) - VF_mid(t)] + [VF_mid(t) - Li_2(t)].

It holds for EVERY real t, not only at natural or square arguments.
It is also transported without triangle inequalities through the
actual logarithmic Abel kernel for the smoothed von-Mangoldt source:
  K_x(t) = 1/t + x * (log(t)-1)/t^2.

The square-bound implication and the native NNS reciprocal-history
consequence are bundled as honest implications. The RH -> sharp Gz
quantitative estimate is NOT in Mathlib and is NOT asserted as a
proof in this module. The terminal Alpoge theorem cannot substitute
for that analytic transfer without an actual Lean derivation.
-/

noncomputable section
open MeasureTheory intervalIntegral
open scoped BigOperators

namespace RHLean.Analysis

/-- The real von-Koch discrepancy, using genuine Nat.primeCounting
and the integral Li_2 normalization. -/
def alpogeRealPrimeDelta (t : ℝ) : ℝ :=
  vfMidPrimeLiError t

/-- The real prime error in the existing VF midpoint coordinate. -/
def alpogeVFMidPrimeDelta (t : ℝ) : ℝ :=
  vfMidPrimeError t

/-- Purely deterministic midpoint quadrature source. -/
def alpogeVFMidQuadratureDelta (t : ℝ) : ℝ :=
  vfMidLiError t

/-- EXACT delta(t) equivalence with the original genuine prime staircase.
In particular this is NOT just a finite square-endpoint identity. -/
theorem alpogeRealPrimeDelta_eq_vfMid_add_quadrature (t : ℝ) :
    alpogeRealPrimeDelta t =
      alpogeVFMidPrimeDelta t + alpogeVFMidQuadratureDelta t := by
  exact vfMidPrimeLiError_eq_primeError_add_liError t

/-- Conversely solve for the actual VF prime error, without assuming
that the quadrature term is small at every point. -/
theorem alpogeVFMidPrimeDelta_eq_real_sub_quadrature (t : ℝ) :
    alpogeVFMidPrimeDelta t =
      alpogeRealPrimeDelta t - alpogeVFMidQuadratureDelta t := by
  have h := alpogeRealPrimeDelta_eq_vfMid_add_quadrature t
  linarith

/-- The ACTUAL Abel kernel arising when a prime of size t is weighted
by log t * (x/t - 1). It need not be nonnegative for all t < x;
the signed kernel is always retained. -/
def alpogePrimeAbelKernel (x t : ℝ) : ℝ :=
  t⁻¹ + x * (Real.log t - 1) / t ^ 2

/-- The exact signed Abel-kernel transport at every real t.
No absolute values, dummy "prime-model" replacement, or isolated
prime-power sources are introduced. -/
theorem alpogePrimeAbelKernel_delta_eq
    (x t : ℝ) :
    alpogePrimeAbelKernel x t * alpogeRealPrimeDelta t =
      alpogePrimeAbelKernel x t * alpogeVFMidPrimeDelta t +
        alpogePrimeAbelKernel x t * alpogeVFMidQuadratureDelta t := by
  rw [alpogeRealPrimeDelta_eq_vfMid_add_quadrature]
  ring

/-- Signed finite discrete sampling of the *real* delta identity;
works for any (including signed) test weight, and keeps the complete
arithmetic history before any norm/positive-part split. -/
theorem alpogePrimeAbelKernel_delta_sum_exact
    (N : ℕ) (w : ℕ → ℝ) :
    (∑ n ∈ Finset.Icc 2 N,
        w n * alpogeRealPrimeDelta (n : ℝ)) =
      (∑ n ∈ Finset.Icc 2 N,
        w n * alpogeVFMidPrimeDelta (n : ℝ)) +
      (∑ n ∈ Finset.Icc 2 N,
        w n * alpogeVFMidQuadratureDelta (n : ℝ)) := by
  calc
    (∑ n ∈ Finset.Icc 2 N,
        w n * alpogeRealPrimeDelta (n : ℝ)) =
      (∑ n ∈ Finset.Icc 2 N,
        (w n * alpogeVFMidPrimeDelta (n : ℝ) +
          w n * alpogeVFMidQuadratureDelta (n : ℝ))) := by
        apply Finset.sum_congr rfl
        intro n _hn
        rw [alpogeRealPrimeDelta_eq_vfMid_add_quadrature]
        ring
    _ = _ := Finset.sum_add_distrib

/-- If both signed weighted histories are interval-integrable, the
full continuously weighted delta history is exactly their sum. This is
a *genuine* integral of the real prime staircase, not midpoint sampling.
The hypotheses ask only for integrability, not for any RH-strength bound. -/
theorem alpogePrimeAbelKernel_delta_integral_exact
    (x : ℝ)
    (hVF : IntervalIntegrable
      (fun t : ℝ => alpogePrimeAbelKernel x t * alpogeVFMidPrimeDelta t)
      MeasureTheory.volume 2 x)
    (hQ : IntervalIntegrable
      (fun t : ℝ => alpogePrimeAbelKernel x t * alpogeVFMidQuadratureDelta t)
      MeasureTheory.volume 2 x) :
    (∫ t in (2 : ℝ)..x,
      alpogePrimeAbelKernel x t * alpogeRealPrimeDelta t) =
      (∫ t in (2 : ℝ)..x,
        alpogePrimeAbelKernel x t * alpogeVFMidPrimeDelta t) +
      (∫ t in (2 : ℝ)..x,
        alpogePrimeAbelKernel x t * alpogeVFMidQuadratureDelta t) := by
  calc
    (∫ t in (2 : ℝ)..x,
        alpogePrimeAbelKernel x t * alpogeRealPrimeDelta t) =
      (∫ t in (2 : ℝ)..x,
        (alpogePrimeAbelKernel x t * alpogeVFMidPrimeDelta t +
          alpogePrimeAbelKernel x t * alpogeVFMidQuadratureDelta t)) := by
            congr 1
            funext t
            exact alpogePrimeAbelKernel_delta_eq x t
    _ = _ := intervalIntegral.integral_add hVF hQ

/-- The midpoint quadrature error is UNCONDITIONALLY bounded at
every square endpoint, with the existing explicit repository constant. -/
theorem alpogeSquareVFMidQuadrature_uniform (R : ℕ) (hR : 2 ≤ R) :
    |alpogeVFMidQuadratureDelta ((R : ℝ) ^ 2)| ≤
      vfMidLiSquareEndpointUniformConstant := by
  exact abs_vfMidLiError_sq_le_uniform hR

/-- At squares, prime-minus-Li and prime-minus-VF differ by
only the already proved deterministic O(1) quadrature source. -/
theorem alpogeSquareDelta_diff_vfMid_uniform
    (R : ℕ) (hR : 2 ≤ R) :
    |alpogeRealPrimeDelta ((R : ℝ) ^ 2) -
      alpogeVFMidPrimeDelta ((R : ℝ) ^ 2)| ≤
        vfMidLiSquareEndpointUniformConstant := by
  rw [alpogeRealPrimeDelta_eq_vfMid_add_quadrature]
  have h := alpogeSquareVFMidQuadrature_uniform R hR
  simpa only [add_sub_cancel_left] using h

/-- The already kernel-proved full real-line von-Koch equivalence
reused rather than reimported as an unproved criterion. -/
theorem alpogeVFMidVonKoch_iff_li2 :
    VFMidVonKochBoundedStatement ↔ PrimeLiVonKochBoundedStatement :=
  vfMidVonKochBounded_iff_primeLiVonKochBounded

/-- The native SQUARE-lattice VF statement is also exactly equivalent
to the all-real classical prime-minus-Li quantitative statement. -/
theorem alpogeVFMidSquareVonKoch_iff_li2 :
    VFMidSquareEndpointVonKochBoundedStatement ↔
      PrimeLiVonKochBoundedStatement :=
  vfMidSquareEndpointVonKochBounded_iff_primeLiVonKochBounded

/-- The precise arithmetic square-lattice quantity that a quantified
Alpoge theorem must prove to discharge the last hypothesis in #1184. -/
def AlpogeCriticalSquareGzStatement : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ R : ℕ, 2 ≤ R →
      |nativeAlpogeGz (R ^ 2)| ≤ C * (R : ℝ)

/-- Global critical bound on the *actual* full prime-power Gz. -/
def AlpogeCriticalAllGzStatement : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ N : ℕ, 4 ≤ N →
      |nativeAlpogeGz N| ≤ C * Real.sqrt (N : ℝ)

/-- Global critical convergence rate for the original signed NNS
reciprocal Chebyshev-error history, with harmonic/ Euler centering. -/
def AlpogeCriticalNNSHistoryStatement : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ N : ℕ, 4 ≤ N →
      |nativeAlpogeCenteredHistory N| ≤ C / Real.sqrt (N : ℝ)

/-- SOURCE-EXACT square-to-all consequence, reusing rather than
reproving the square-clock interpolation of #1184. -/
theorem alpogeCriticalAllGz_of_square :
    AlpogeCriticalSquareGzStatement → AlpogeCriticalAllGzStatement := by
  rintro ⟨C, hC, hSquare⟩
  let C' := 2 * C + 3 * alpogeGzInterpolationSlope
  have hC' : 0 ≤ C' := by
    dsimp [C']
    linarith [alpogeGzInterpolationSlope_nonneg]
  refine ⟨C', hC', ?_⟩
  intro N hN
  exact nativeAlpogeGz_all_of_square_lattice_critical C hC hSquare N hN

/-- The native NNS critical reciprocal-history bound is already a
formal consequence of the SAME square-lattice hypothesis. -/
theorem alpogeCriticalNNSHistory_of_square :
    AlpogeCriticalSquareGzStatement →
      AlpogeCriticalNNSHistoryStatement := by
  rintro ⟨C, hC, hSquare⟩
  let C' := 2 * C + 3 * alpogeGzInterpolationSlope
  have hC' : 0 ≤ C' := by
    dsimp [C']
    linarith [alpogeGzInterpolationSlope_nonneg]
  refine ⟨C', hC', ?_⟩
  intro N hN
  exact nativeAlpogeCenteredHistory_all_of_square_lattice_critical
    C hC hSquare N hN

/-- The reusable, genuinely proved downstream proof contract.
No RH theorem or strong estimate appears as an invented global fact. -/
theorem alpogeSquareCritical_closes_Gz_NNS :
    AlpogeCriticalSquareGzStatement →
      AlpogeCriticalAllGzStatement ∧ AlpogeCriticalNNSHistoryStatement := by
  intro h
  exact ⟨alpogeCriticalAllGz_of_square h,
    alpogeCriticalNNSHistory_of_square h⟩

/-- The analytic transfer still to be extracted from the FULL terminal
upstream theorem (not the earlier conditional CoreAt). This proposition
is deliberately not inhabited here: Mathlib does not yet contain the
sufficient smoothed explicit-formula theorem. -/
def AlpogeRHToSharpGzAndVonKochStatement : Prop :=
  RiemannHypothesis →
    AlpogeCriticalSquareGzStatement ∧ PrimeLiVonKochBoundedStatement

/-- Once the terminal Alpoge RH result AND the genuine quantitative
RH->Gz/von-Koch consequences are compiled, the downstream pipeline
requires no further estimates in the VF, square-block or NNS coordinates. -/
theorem alpogeQuantitativeConclusion_of_RH_and_analytic_transfer
    (hAnalytic : AlpogeRHToSharpGzAndVonKochStatement)
    (hRH : RiemannHypothesis) :
    AlpogeCriticalAllGzStatement ∧
    AlpogeCriticalNNSHistoryStatement ∧
    VFMidVonKochBoundedStatement := by
  obtain ⟨hSquare, hPrime⟩ := hAnalytic hRH
  exact ⟨alpogeCriticalAllGz_of_square hSquare,
    alpogeCriticalNNSHistory_of_square hSquare,
    vfMidVonKochBounded_of_primeLi hPrime⟩

end RHLean.Analysis
