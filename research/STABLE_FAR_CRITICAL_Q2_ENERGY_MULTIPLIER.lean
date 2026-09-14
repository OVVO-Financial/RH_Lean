import Mathlib
import «research.STABLE_FAR_PERRON_RETURNED_FIBER_INTERFACE»

/-!
# Critical-line q² multiplier has exact reciprocal energy

The Perron returned-fibre interface already proves that q² translation is
scalar on the critical log mode.  This file identifies that scalar exactly as

  q⁻¹ * exp(-2 i tau log q)

and records its norm and squared norm.  Thus the q⁻² recursive energy scale is
not inserted as an estimate: it is the exact modulus square of q² translation
on the critical half-density coordinate.

No zeta zero, RH hypothesis, simplicity hypothesis, or LOW-4 estimate appears.
-/

noncomputable section

namespace RHLean.Proof

/-- The pure q² log-frequency multiplier has unit modulus. -/
theorem norm_stableFarQ2LogFrequencyMultiplier
    (tau : ℝ) (q : ℕ) :
    ‖stableFarQ2LogFrequencyMultiplier tau q‖ = 1 := by
  unfold stableFarQ2LogFrequencyMultiplier stableFarLogFrequencyMode
  let u : ℝ := tau * (-(2 * Real.log (q : ℝ)))
  change ‖Complex.exp (Complex.I * (u : ℂ))‖ = 1
  rw [Complex.norm_exp]
  simp

/-- **Exact reciprocal-phase form of critical q² descent.**  For positive q,
the half-density factor `exp(-log q)` is literally `1/q`; the remaining factor
is the unit-modulus q² log-frequency phase. -/
theorem stableFarCriticalQ2LogMultiplier_eq_reciprocal_phase
    (tau : ℝ) {q : ℕ} (hq : 0 < q) :
    stableFarCriticalQ2LogMultiplier tau q =
      (1 / (q : ℂ)) * stableFarQ2LogFrequencyMultiplier tau q := by
  unfold stableFarCriticalQ2LogMultiplier
  apply congrArg (fun z : ℂ => z * stableFarQ2LogFrequencyMultiplier tau q)
  rw [← Complex.ofReal_exp]
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  rw [Real.exp_neg, Real.exp_log hqR]
  push_cast
  simp [one_div]

/-- The critical q² multiplier contracts amplitude by exactly `1/q`. -/
theorem norm_stableFarCriticalQ2LogMultiplier
    (tau : ℝ) {q : ℕ} (hq : 0 < q) :
    ‖stableFarCriticalQ2LogMultiplier tau q‖ = 1 / (q : ℝ) := by
  rw [stableFarCriticalQ2LogMultiplier_eq_reciprocal_phase tau hq,
    norm_mul, norm_stableFarQ2LogFrequencyMultiplier]
  simp

/-- **Exact q⁻² energy law.**  Squaring the critical q² translation multiplier
produces the recursive daughter factor `1/q²` exactly. -/
theorem norm_sq_stableFarCriticalQ2LogMultiplier
    (tau : ℝ) {q : ℕ} (hq : 0 < q) :
    ‖stableFarCriticalQ2LogMultiplier tau q‖ ^ 2 =
      1 / (q : ℝ) ^ 2 := by
  rw [norm_stableFarCriticalQ2LogMultiplier tau hq]
  ring

end RHLean.Proof
