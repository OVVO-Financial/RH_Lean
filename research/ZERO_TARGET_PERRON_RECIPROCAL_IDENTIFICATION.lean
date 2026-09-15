import Mathlib
import «research.ZERO_TARGET_MELLIN_FRESH_PRIME_SQUARE»

/-!
# Exact reciprocal identification of the zero-target quadratic with the Perron q² energy

The local Mellin-square module allows an arbitrary nonnegative real scaling
ratio `r`.  The two-way real/complex coordinate fixes which specialization
corresponds to the already-compiled critical q² Perron multiplier.

If both real coordinates are scaled by `r`, then Fred's complex coordinate
`Psi(x,y)` itself is scaled by `r`.  Therefore the critical q² *amplitude*
`1/p` corresponds to

  r = 1/p,

not to `r^2 = 1/p`.  Since the zero-target covariance mode is quadratic,

  co_0 - div_0 = Re(Psi(x,y)^2),

its double-corner coefficient is then exactly `1/p^2`.  This is literally the
squared norm of the critical q² Perron multiplier from #708.

The older algebraic specialization `r^2 = 1/p` remains a true statement about
a square-root parameterization of the quadratic corner, but it is not the
real-pair scaling that matches the complex q² amplitude.  The theorems below
record the coordinate-correct identification used going forward.
-/

noncomputable section

namespace RHLean.Proof

/-- Scaling both real coordinates by `r` scales the complex Fermat coordinate
by the same real scalar. -/
theorem stableFarRealPairToComplex_smul_both
    (r x y : ℝ) :
    stableFarRealPairToComplex (r * x, r * y) =
      (r : ℂ) * stableFarRealPairToComplex (x, y) := by
  apply Complex.ext <;>
    simp [stableFarRealPairToComplex] <;> ring

/-- The signed fresh-prime double corner has the corresponding negative complex
amplitude; the sign disappears after squaring. -/
theorem stableFarRealPairToComplex_neg_smul_both
    (r x y : ℝ) :
    stableFarRealPairToComplex (-(r * x), -(r * y)) =
      -(r : ℂ) * stableFarRealPairToComplex (x, y) := by
  apply Complex.ext <;>
    simp [stableFarRealPairToComplex] <;> ring

/-- **Coordinate-correct reciprocal specialization.**  Scaling each physical
real coordinate by the critical q² amplitude `1/p` scales the zero-target
quadratic excess by exactly `1/p²`. -/
theorem zeroTargetMellinFreshPrimeSquare_doubleCorner_reciprocal
    {p : ℕ} (hp : 0 < p) (x y : ℝ) :
    zeroTargetCoPartialPair (-((1 / (p : ℝ)) * x))
          (-((1 / (p : ℝ)) * y)) -
        zeroTargetDivergentPair (-((1 / (p : ℝ)) * x))
          (-((1 / (p : ℝ)) * y)) =
      (1 / (p : ℝ) ^ 2) *
        (zeroTargetCoPartialPair x y - zeroTargetDivergentPair x y) := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hr : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
  have h := zeroTargetMellinFreshPrimeSquare_doubleCorner_excess
    hr x y
  simpa [div_pow] using h

/-- The reciprocal quadratic coefficient is exactly the norm-square of the
critical q² Perron multiplier, including its arbitrary log-frequency phase. -/
theorem zeroTarget_reciprocalSquare_eq_norm_sq_criticalQ2Multiplier
    (tau : ℝ) {p : ℕ} (hp : 0 < p) :
    (1 / (p : ℝ) ^ 2) =
      ‖stableFarCriticalQ2LogMultiplier tau p‖ ^ 2 := by
  rw [norm_sq_stableFarCriticalQ2LogMultiplier tau hp]

/-- Hence the reciprocal double-corner zero-target excess can be written with
the exact Perron q² energy coefficient. -/
theorem zeroTargetMellinFreshPrimeSquare_doubleCorner_eq_criticalPerronEnergy
    (tau : ℝ) {p : ℕ} (hp : 0 < p) (x y : ℝ) :
    zeroTargetCoPartialPair (-((1 / (p : ℝ)) * x))
          (-((1 / (p : ℝ)) * y)) -
        zeroTargetDivergentPair (-((1 / (p : ℝ)) * x))
          (-((1 / (p : ℝ)) * y)) =
      ‖stableFarCriticalQ2LogMultiplier tau p‖ ^ 2 *
        (zeroTargetCoPartialPair x y - zeroTargetDivergentPair x y) := by
  rw [← zeroTarget_reciprocalSquare_eq_norm_sq_criticalQ2Multiplier tau hp]
  exact zeroTargetMellinFreshPrimeSquare_doubleCorner_reciprocal hp x y

end RHLean.Proof
