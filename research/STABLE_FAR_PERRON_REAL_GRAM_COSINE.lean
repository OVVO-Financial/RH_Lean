import Mathlib
import «research.STABLE_FAR_PERRON_REALIFICATION»

/-!
# The real Perron Gram kernel is logarithmic cosine alignment

After the realification bridge, no complex geometry remains in the cross-owner
quadratic interaction.  This file makes that statement explicit.

For q^2 descent define the log-frequency angle

  theta_q(tau) = -2 * tau * log q.

The #708 critical multiplier is

  (1/q) * exp(i * theta_q),

and the normalized real Gram kernel between owners q and r is therefore

  cos(theta_q - theta_r) / (q*r).

Equivalently it is

  cos(2*tau*(log r - log q)) / (q*r).

Thus the remaining LOW-4 frame problem is a real symmetric oscillatory Gram
problem on logarithmic prime separations.  This module proves only the exact
identity; it introduces no estimate, no zero of zeta, and no RH hypothesis.
-/

noncomputable section

namespace RHLean.Proof

/-- Real angle carried by q^2 descent at log-frequency `tau`. -/
def stableFarCriticalQ2RealAngle (tau : ℝ) (q : ℕ) : ℝ :=
  -2 * tau * Real.log (q : ℝ)

/-- The pure q^2 phase is literally cosine plus sine times `i`. -/
theorem stableFarQ2LogFrequencyMultiplier_eq_cos_sin
    (tau : ℝ) (q : ℕ) :
    stableFarQ2LogFrequencyMultiplier tau q =
      (Real.cos (stableFarCriticalQ2RealAngle tau q) : ℂ) +
        (Real.sin (stableFarCriticalQ2RealAngle tau q) : ℂ) * Complex.I := by
  unfold stableFarQ2LogFrequencyMultiplier stableFarLogFrequencyMode
  have harg :
      Complex.I * (((tau * (-(2 * Real.log (q : ℝ))) : ℝ)) : ℂ) =
        ((stableFarCriticalQ2RealAngle tau q : ℝ) : ℂ) * Complex.I := by
    simp [stableFarCriticalQ2RealAngle]
    ring
  rw [harg, Complex.exp_mul_I]
  simp

/-- The q^2 phase has the expected cosine real coordinate. -/
theorem stableFarQ2LogFrequencyMultiplier_re
    (tau : ℝ) (q : ℕ) :
    (stableFarQ2LogFrequencyMultiplier tau q).re =
      Real.cos (stableFarCriticalQ2RealAngle tau q) := by
  rw [stableFarQ2LogFrequencyMultiplier_eq_cos_sin]
  simp

/-- The q^2 phase has the expected sine imaginary coordinate. -/
theorem stableFarQ2LogFrequencyMultiplier_im
    (tau : ℝ) (q : ℕ) :
    (stableFarQ2LogFrequencyMultiplier tau q).im =
      Real.sin (stableFarCriticalQ2RealAngle tau q) := by
  rw [stableFarQ2LogFrequencyMultiplier_eq_cos_sin]
  simp

/-- The complex reciprocal of a natural owner is the real-axis embedding of
its real reciprocal.  Stating this explicitly avoids any denominator case
split later in the coordinate proofs. -/
theorem stableFar_complexReciprocal_nat_eq_ofReal (q : ℕ) :
    (1 / (q : ℂ)) = ((1 / (q : ℝ) : ℝ) : ℂ) := by
  simpa [one_div] using (Complex.ofReal_inv (q : ℝ)).symm

/-- The critical q^2 multiplier has the expected real cosine coordinate. -/
theorem stableFarCriticalQ2LogMultiplier_re
    (tau : ℝ) {q : ℕ} (hq : 0 < q) :
    (stableFarCriticalQ2LogMultiplier tau q).re =
      (1 / (q : ℝ)) * Real.cos (stableFarCriticalQ2RealAngle tau q) := by
  rw [stableFarCriticalQ2LogMultiplier_eq_reciprocal_phase tau hq,
    stableFar_complexReciprocal_nat_eq_ofReal,
    Complex.mul_re,
    stableFarQ2LogFrequencyMultiplier_re]
  simp

/-- The critical q^2 multiplier has the expected real sine coordinate. -/
theorem stableFarCriticalQ2LogMultiplier_im
    (tau : ℝ) {q : ℕ} (hq : 0 < q) :
    (stableFarCriticalQ2LogMultiplier tau q).im =
      (1 / (q : ℝ)) * Real.sin (stableFarCriticalQ2RealAngle tau q) := by
  rw [stableFarCriticalQ2LogMultiplier_eq_reciprocal_phase tau hq,
    stableFar_complexReciprocal_nat_eq_ofReal,
    Complex.mul_im,
    stableFarQ2LogFrequencyMultiplier_im]
  simp

/-- **Exact cosine Gram kernel.**  Cross-owner interaction is reciprocal
amplitude times cosine of the relative logarithmic phase. -/
theorem stableFarCriticalQ2RealGramKernel_eq_cos_sub
    (tau : ℝ) {q r : ℕ} (hq : 0 < q) (hr : 0 < r) :
    stableFarCriticalQ2RealGramKernel tau q r =
      ((1 / (q : ℝ)) * (1 / (r : ℝ))) *
        Real.cos
          (stableFarCriticalQ2RealAngle tau q -
            stableFarCriticalQ2RealAngle tau r) := by
  rw [stableFarCriticalQ2RealGramKernel]
  rw [stableFarCriticalQ2LogMultiplier_re tau hq,
    stableFarCriticalQ2LogMultiplier_re tau hr,
    stableFarCriticalQ2LogMultiplier_im tau hq,
    stableFarCriticalQ2LogMultiplier_im tau hr]
  rw [Real.cos_sub]
  ring

/-- Relative q/r phase is exactly logarithmic prime separation. -/
theorem stableFarCriticalQ2RealAngle_sub
    (tau : ℝ) (q r : ℕ) :
    stableFarCriticalQ2RealAngle tau q -
        stableFarCriticalQ2RealAngle tau r =
      2 * tau * (Real.log (r : ℝ) - Real.log (q : ℝ)) := by
  simp [stableFarCriticalQ2RealAngle]
  ring

/-- **Perron alignment normal form.**  The cross-owner Gram entry depends only
on reciprocal owner scale and the cosine of logarithmic separation. -/
theorem stableFarCriticalQ2RealGramKernel_eq_logCosine
    (tau : ℝ) {q r : ℕ} (hq : 0 < q) (hr : 0 < r) :
    stableFarCriticalQ2RealGramKernel tau q r =
      ((1 / (q : ℝ)) * (1 / (r : ℝ))) *
        Real.cos
          (2 * tau * (Real.log (r : ℝ) - Real.log (q : ℝ))) := by
  rw [stableFarCriticalQ2RealGramKernel_eq_cos_sub tau hq hr,
    stableFarCriticalQ2RealAngle_sub]

/-- Symmetry is now a literal real Gram symmetry. -/
theorem stableFarCriticalQ2RealGramKernel_comm
    (tau : ℝ) (q r : ℕ) :
    stableFarCriticalQ2RealGramKernel tau q r =
      stableFarCriticalQ2RealGramKernel tau r q := by
  unfold stableFarCriticalQ2RealGramKernel
  ring

end RHLean.Proof
