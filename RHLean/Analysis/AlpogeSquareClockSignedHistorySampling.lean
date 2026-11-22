import Mathlib
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import RHLean.Analysis.NativePNTErrorMass
import RHLean.Analysis.NativePNTLogSums

/-!
# Direct signed Alpoge Gz: square-clock sampling at critical spacing

This is the original completed weighted von-Mangoldt source, NOT an
individual Selberg K2 channel or a Gaussian surrogate.

For integer N, define the original Gz(N) by its finite prime powers.
The native Abel identity identifies Gz(N)/N with the *complete*
centered signed Erdos reciprocal Chebyshev-error history.

The finite Mertens-first theorem gives a uniform ONE-SIDED increment
slope. Since successive R^2-1 endpoints are O(R) apart, controlling
Gz on these square endpoints at root scale is sufficient to control
it at ALL integer endpoints with the SAME power exponent.

This exact square-sampling theorem is UNCONDITIONAL.
Its square-endpoint hypothesis is NOT proved here: doing that at
O_eps(R^(1+eps)) is the actual deep RH-strength input, requiring
genuine Alpoge multiplicity/cost or another source-specific estimate.

No axiom, sorry, external RH theorem, or proposed multiplicity bound
is used in this module.
-/

noncomputable section
open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

/-- Genuine integer-point Alpoge source with all von Mangoldt prime powers. -/
def nativeAlpogeGz (N : ℕ) : ℝ :=
  (N : ℝ) * nativeLambdaRecip N - nativePsi N -
    (N : ℝ) * Real.log (N : ℝ) +
      (1 + Real.eulerMascheroniConstant) * (N : ℝ)

/-- Complete, signed Erdos history with exact harmonic/Euler centering. -/
def nativeAlpogeCenteredHistory (N : ℕ) : ℝ :=
  nativePNTWeightedErrorMass (N - 1) +
    (harmonic N : ℝ) - Real.log (N : ℝ) +
      Real.eulerMascheroniConstant

/-- The von Mangoldt term at an integer cancels inside
N*sum Lambda(d)/d - psi(N) BEFORE any norm or covariance split. -/
theorem nativeAlpogeGz_primePowerEndpoint_cancel (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) * nativeLambdaRecip (n + 1) -
        nativePsi (n + 1) =
      ((n + 1 : ℕ) : ℝ) * nativeLambdaRecip n -
        nativePsi n := by
  rw [nativeLambdaRecip_succ, nativePsi_succ]
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp [hn]
  ring_nf

/-- Original Gz equals N times the entire native signed reciprocal
history at EVERY integer endpoint N>=1; no analytic estimate occurs. -/
theorem nativeAlpogeGz_eq_centeredHistory
    (N : ℕ) (hN : 1 ≤ N) :
    nativeAlpogeGz N = (N : ℝ) * nativeAlpogeCenteredHistory N := by
  cases N with
  | zero => omega
  | succ n =>
      have hsrc := nativeAlpogeGz_primePowerEndpoint_cancel n
      have hmass := nativePNTWeightedErrorMass_eq n
      unfold nativeAlpogeGz nativeAlpogeCenteredHistory
      have hsub : n + 1 - 1 = n := by omega
      simp only [hsub]
      rw [hsrc, hmass]
      have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      push_cast
      field_simp [hn]
      ring_nf

/-- Exact original-source one-step first difference. -/
theorem nativeAlpogeGz_succ_sub (n : ℕ) :
    nativeAlpogeGz (n + 1) - nativeAlpogeGz n =
      (nativeLambdaRecip n - Real.log (n : ℝ) +
        Real.eulerMascheroniConstant) + 1 -
      ((n : ℝ) + 1) *
        (Real.log (((n + 1 : ℕ) : ℝ)) - Real.log (n : ℝ)) := by
  have hsource := nativeAlpogeGz_primePowerEndpoint_cancel n
  have hsrc :
      (((n + 1 : ℕ) : ℝ) * nativeLambdaRecip (n + 1) -
          nativePsi (n + 1)) -
      ((n : ℝ) * nativeLambdaRecip n - nativePsi n) =
          nativeLambdaRecip n := by
    push_cast at hsource ⊢
    nlinarith only [hsource]
  unfold nativeAlpogeGz
  push_cast at hsrc ⊢
  linear_combination hsrc

/-- **Direct arithmetic second derivative of the complete original Gz.**
The discrete curvature is exactly the genuine prime-power spike
Lambda(n+1)/(n+1) minus the deterministic second difference of x*log x.
No Selberg partition, separate K2 estimate, or random covariance proxy
is present. A high-order jet alone does not give a bound on its sum. -/
theorem nativeAlpogeGz_secondDifference_primePower (n : ℕ) :
    nativeAlpogeGz (n + 2) -
        2 * nativeAlpogeGz (n + 1) + nativeAlpogeGz n =
      Λ (n + 1) / ((n + 1 : ℕ) : ℝ) -
        (((n + 2 : ℕ) : ℝ) * Real.log ((n + 2 : ℕ) : ℝ) -
          2 * (((n + 1 : ℕ) : ℝ) *
            Real.log ((n + 1 : ℕ) : ℝ)) +
          (n : ℝ) * Real.log (n : ℝ)) := by
  have hnext := nativeAlpogeGz_succ_sub (n + 1)
  have hprev := nativeAlpogeGz_succ_sub n
  have hprime := nativeLambdaRecip_succ n
  push_cast at hnext hprev hprime ⊢
  have hlog2 : Real.log ((n : ℝ) + 1 + 1) =
      Real.log ((n : ℝ) + 2) := by
    congr 1
    ring
  rw [hlog2] at hnext
  linear_combination hnext - hprev + hprime

/-- Safe nonnegative upward slope for the original signed source. -/
def nativeAlpogeSafeSlope : ℝ :=
  Real.log (4 : ℝ) + 2 + |Real.eulerMascheroniConstant|

theorem nativeAlpogeSafeSlope_nonneg : 0 ≤ nativeAlpogeSafeSlope := by
  unfold nativeAlpogeSafeSlope
  have hlog : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  linarith [abs_nonneg Real.eulerMascheroniConstant]

/-- Genuine unconditional one-sided derivative estimate, derived from
the main-branch Mertens-first theorem and sharp log increment. -/
theorem nativeAlpogeGz_succ_le (n : ℕ) (hn : 1 ≤ n) :
    nativeAlpogeGz (n + 1) ≤
      nativeAlpogeGz n + nativeAlpogeSafeSlope := by
  have hstep := nativeAlpogeGz_succ_sub n
  have hlog := nativeOne_le_succ_mul_log_succ_sub_log n hn
  have hmertens := (nativeLambdaRecip_sub_log_bounds n hn).2
  simp only [Nat.cast_add, Nat.cast_one] at hstep
  unfold nativeAlpogeSafeSlope
  linarith [le_abs_self Real.eulerMascheroniConstant]

/-- Generic arithmetic discrete one-sided Lipschitz telescope.
This is the only interpolation mechanism used below. -/
theorem nativeOneSidedLipschitz_Icc
    (f : ℕ → ℝ) (L : ℝ)
    (hstep : ∀ n : ℕ, 1 ≤ n → f (n + 1) ≤ f n + L)
    (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    f b ≤ f a + L * (((b - a : ℕ) : ℝ)) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
      have hnext := hstep b (by omega)
      have hgap : (b + 1) - a = (b - a) + 1 := by omega
      calc
        f (b + 1) ≤ f b + L := hnext
        _ ≤ (f a + L * (((b - a : ℕ) : ℝ))) + L := by linarith [ih]
        _ = f a + L * (((b + 1 - a : ℕ) : ℝ)) := by
          rw [hgap]
          push_cast
          ring

/-- Floor-square geometry at the native endpoint X_R=R^2-1. -/
theorem nativeSquareClock_anchor_gap
    (N R : ℕ) (hN : 4 ≤ N)
    (hlo : R ^ 2 ≤ N + 1)
    (hhi : N + 1 < (R + 1) ^ 2) :
    2 ≤ R ∧ 1 ≤ R ^ 2 - 1 ∧
      R ^ 2 - 1 ≤ N ∧ N - (R ^ 2 - 1) ≤ 2 * R + 1 := by
  have hR : 2 ≤ R := by
    by_contra h
    have hR1 : R ≤ 1 := by omega
    nlinarith
  have hR2 : 4 ≤ R ^ 2 := by nlinarith
  have hsq : (R + 1) ^ 2 = R ^ 2 + 2 * R + 1 := by ring
  rw [hsq] at hhi
  constructor
  · exact hR
  constructor
  · omega
  constructor
  · omega
  · omega

/-- Critical square sampling: every integer N>=4 is within O(sqrt N)
of an earlier original square endpoint. There is NO unsmoothed collar
loss larger than the RH target scale. -/
theorem nativeOneSidedSquareClock_sampling
    (f : ℕ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hstep : ∀ n : ℕ, 1 ≤ n → f (n + 1) ≤ f n + L)
    (N : ℕ) (hN : 4 ≤ N) :
    let R := Nat.sqrt (N + 1)
    f N ≤ f (R ^ 2 - 1) + L * ((2 * R + 1 : ℕ) : ℝ) := by
  dsimp
  let R := Nat.sqrt (N + 1)
  have hlo : R ^ 2 ≤ N + 1 := Nat.sqrt_le' (N + 1)
  have hhi : N + 1 < (R + 1) ^ 2 := Nat.lt_succ_sqrt' (N + 1)
  rcases nativeSquareClock_anchor_gap N R hN hlo hhi with
    ⟨_hR, hleft, hanchor, hgap⟩
  have h := nativeOneSidedLipschitz_Icc
    f L hstep (R ^ 2 - 1) N hleft hanchor
  have hcast : (((N - (R ^ 2 - 1) : ℕ) : ℝ)) ≤
      ((2 * R + 1 : ℕ) : ℝ) := by
    exact_mod_cast hgap
  have hscale := mul_le_mul_of_nonneg_left hcast hL
  calc
    f N ≤ f (R ^ 2 - 1) + L * (((N - (R ^ 2 - 1) : ℕ) : ℝ)) := h
    _ ≤ f (R ^ 2 - 1) + L * ((2 * R + 1 : ℕ) : ℝ) := by
      linarith only [hscale]

/-- Apply square-clock sampling to the ENTIRE genuine Gz, not a selected
convolution band. Unconditional O(sqrt N) INTERPOLATION ERROR. -/
theorem nativeAlpogeGz_squareClock_sampling
    (N : ℕ) (hN : 4 ≤ N) :
    let R := Nat.sqrt (N + 1)
    nativeAlpogeGz N ≤
      nativeAlpogeGz (R ^ 2 - 1) +
        nativeAlpogeSafeSlope * ((2 * R + 1 : ℕ) : ℝ) := by
  exact nativeOneSidedSquareClock_sampling
    nativeAlpogeGz nativeAlpogeSafeSlope
      nativeAlpogeSafeSlope_nonneg nativeAlpogeGz_succ_le N hN

/-- This is the exact non-circular consumer: if an independently proved
square-endpoint bound U exists, ALL natural endpoints immediately inherit
it, at the RH-critical O(sqrt N) interpolation cost. The square bound is
EXPLICITLY ASSUMED, never presented as already established. -/
theorem nativeAlpogeGz_of_squareClock_bound
    (U : ℕ → ℝ)
    (hU : ∀ R : ℕ, 2 ≤ R →
      nativeAlpogeGz (R ^ 2 - 1) ≤ U R)
    (N : ℕ) (hN : 4 ≤ N) :
    let R := Nat.sqrt (N + 1)
    nativeAlpogeGz N ≤ U R +
      nativeAlpogeSafeSlope * ((2 * R + 1 : ℕ) : ℝ) := by
  dsimp
  let R := Nat.sqrt (N + 1)
  have hlo : R ^ 2 ≤ N + 1 := Nat.sqrt_le' (N + 1)
  have hhi : N + 1 < (R + 1) ^ 2 := Nat.lt_succ_sqrt' (N + 1)
  have hR := (nativeSquareClock_anchor_gap N R hN hlo hhi).1
  have hsample := nativeAlpogeGz_squareClock_sampling N hN
  dsimp at hsample
  calc
    nativeAlpogeGz N ≤ nativeAlpogeGz (R ^ 2 - 1) +
        nativeAlpogeSafeSlope * ((2 * R + 1 : ℕ) : ℝ) := hsample
    _ ≤ U R + nativeAlpogeSafeSlope * ((2 * R + 1 : ℕ) : ℝ) := by
      linarith only [hU R hR]

/-- Only the square anchors between the two supplied radii enter the bound. -/
theorem nativeAlpogeGz_window_of_squareClock_window (U : ℕ → ℝ) (R₀ R₁ : ℕ) (hR₀ : 2 ≤ R₀)
    (hU : ∀ R, R₀ ≤ R → R ≤ R₁ → nativeAlpogeGz (R ^ 2 - 1) ≤ U R)
    (N : ℕ) (hN : 4 ≤ N) (hlo : R₀ ≤ Nat.sqrt (N + 1)) (hhi : Nat.sqrt (N + 1) ≤ R₁) :
    nativeAlpogeGz N ≤ U (Nat.sqrt (N + 1)) +
      nativeAlpogeSafeSlope * ((2 * Nat.sqrt (N + 1) + 1 : ℕ) : ℝ) := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le hR₀
  exact (nativeAlpogeGz_squareClock_sampling N hN).trans (add_le_add_left (hU _ hlo hhi) _)

end RHLean.Analysis
