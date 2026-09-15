import Mathlib
import «research.STABLE_FAR_PERRON_REALIFICATION»
import «research.STABLE_FAR_PERRON_QUARTER_FRAME_BOUND»
import «research.ZERO_TARGET_PARTIAL_MOMENT_COVARIANCE»

/-!
# Zero-target covariance as a squared-complex Mellin fresh-prime square

This module reconciles three already-compiled coordinates on one exact local
algebraic object:

* Fred's real-pair/complex map `Psi(x,y)`;
* the target-zero partial-moment decomposition `co_0 - div_0 = x*y`;
* the critical q-square Perron multiplier with amplitude `1/p` and energy
  `1/p^2`.

For one fresh-prime coordinate, let `r >= 0` be the scalar amplitude ratio
under insertion.  The four corners of the two-coordinate square are

  (x,y), (-r*x,y), (x,-r*y), (-r*x,-r*y).

Because one sign flip swaps co-partial and divergent sectors while two sign
flips preserve them, summing the four corners gives the exact sector matrix

  [ 1+r^2   2r   ]
  [   2r   1+r^2 ] .

Hence the signed covariance mode `co_0-div_0` is an eigenvector with eigenvalue
`(1-r)^2`.  At the raw endpoint `r=1` this mode has a *double zero*.  If the
critical ratio satisfies `r^2=1/p`, the double corner has amplitude `1/p`, so
its squared energy is exactly `1/p^2`, the same multiplier used by the Perron
quarter-frame theorem.

No norm is applied to the physical owner census here and no LOW-4/RH statement
is asserted.  This file supplies the exact local intertwiner needed for the
next global signed reassembly.
-/

noncomputable section

namespace RHLean.Proof

/-- Fred's inverse realification sends `(x,y)` to the native Fermat point. -/
theorem zeroTargetRealPairToComplex_eq_fermatPoint (x y : ℝ) :
    stableFarRealPairToComplex (x, y) = RHLean.Geometry.fermatPoint x y := by
  exact stableFarRealPairToComplex_factorPair x y

/-- **Target-zero covariance is the real coordinate of the squared complex
point.**  This is exactly the NNS `co_0-div_0` reassembly in the squared-Fermat
coordinate. -/
theorem zeroTargetPairExcess_eq_realPart_realPairToComplex_sq (x y : ℝ) :
    zeroTargetCoPartialPair x y - zeroTargetDivergentPair x y =
      ((stableFarRealPairToComplex (x, y)) ^ 2).re := by
  rw [zeroTargetCoPartial_sub_divergent_eq_mul,
    zeroTargetRealPairToComplex_eq_fermatPoint,
    RHLean.Geometry.fermatPoint_sq_re]

/-- Flipping the first real coordinate is `i * conjugation` in Fred's complex
coordinate. -/
theorem stableFarRealPairToComplex_neg_first (x y : ℝ) :
    stableFarRealPairToComplex (-x, y) =
      Complex.I * star (stableFarRealPairToComplex (x, y)) := by
  apply Complex.ext <;>
    simp [stableFarRealPairToComplex] <;> ring

/-- Flipping the second real coordinate is `-i * conjugation`. -/
theorem stableFarRealPairToComplex_neg_second (x y : ℝ) :
    stableFarRealPairToComplex (x, -y) =
      -Complex.I * star (stableFarRealPairToComplex (x, y)) := by
  apply Complex.ext <;>
    simp [stableFarRealPairToComplex] <;> ring

/-- Flipping both real coordinates is ordinary complex negation. -/
theorem stableFarRealPairToComplex_neg_both (x y : ℝ) :
    stableFarRealPairToComplex (-x, -y) =
      -stableFarRealPairToComplex (x, y) := by
  apply Complex.ext <;>
    simp [stableFarRealPairToComplex] <;> ring

/-- The squared-complex real coordinate changes sign after one real-coordinate
flip. -/
theorem realPart_realPairToComplex_sq_neg_first (x y : ℝ) :
    ((stableFarRealPairToComplex (-x, y)) ^ 2).re =
      -((stableFarRealPairToComplex (x, y)) ^ 2).re := by
  rw [← zeroTargetPairExcess_eq_realPart_realPairToComplex_sq,
    ← zeroTargetPairExcess_eq_realPart_realPairToComplex_sq]
  simp [zeroTargetCoPartialPair, zeroTargetDivergentPair]
  ring

/-- Two sign flips preserve the squared-complex real coordinate. -/
theorem realPart_realPairToComplex_sq_neg_both (x y : ℝ) :
    ((stableFarRealPairToComplex (-x, -y)) ^ 2).re =
      ((stableFarRealPairToComplex (x, y)) ^ 2).re := by
  rw [stableFarRealPairToComplex_neg_both]
  ring

/-! ## Nonnegative Mellin amplitude scaling of zero-target sectors -/

/-- Upper target-zero part is homogeneous for nonnegative amplitudes. -/
theorem zeroTargetUpperPart_nonneg_smul
    {r : ℝ} (hr : 0 ≤ r) (x : ℝ) :
    zeroTargetUpperPart (r * x) = r * zeroTargetUpperPart x := by
  unfold zeroTargetUpperPart
  rw [abs_mul, abs_of_nonneg hr]
  ring

/-- Lower target-zero part is homogeneous for nonnegative amplitudes. -/
theorem zeroTargetLowerPart_nonneg_smul
    {r : ℝ} (hr : 0 ≤ r) (x : ℝ) :
    zeroTargetLowerPart (r * x) = r * zeroTargetLowerPart x := by
  unfold zeroTargetLowerPart
  rw [abs_mul, abs_of_nonneg hr]
  ring

/-- One fresh-prime sign flip with amplitude ratio `r` sends co-partial mass to
`r` times divergent mass. -/
theorem zeroTargetCoPartialPair_neg_smul_left
    {r : ℝ} (hr : 0 ≤ r) (x y : ℝ) :
    zeroTargetCoPartialPair (-(r * x)) y =
      r * zeroTargetDivergentPair x y := by
  simp [zeroTargetCoPartialPair, zeroTargetDivergentPair,
    zeroTargetCUPM, zeroTargetCLPM, zeroTargetDLPM, zeroTargetDUPM,
    zeroTargetUpperPart_neg, zeroTargetLowerPart_neg,
    zeroTargetUpperPart_nonneg_smul hr,
    zeroTargetLowerPart_nonneg_smul hr]
  ring

/-- The divergent sector is exchanged in the opposite direction. -/
theorem zeroTargetDivergentPair_neg_smul_left
    {r : ℝ} (hr : 0 ≤ r) (x y : ℝ) :
    zeroTargetDivergentPair (-(r * x)) y =
      r * zeroTargetCoPartialPair x y := by
  simp [zeroTargetCoPartialPair, zeroTargetDivergentPair,
    zeroTargetCUPM, zeroTargetCLPM, zeroTargetDLPM, zeroTargetDUPM,
    zeroTargetUpperPart_neg, zeroTargetLowerPart_neg,
    zeroTargetUpperPart_nonneg_smul hr,
    zeroTargetLowerPart_nonneg_smul hr]
  ring

/-- Right-coordinate version of the co/div sector exchange. -/
theorem zeroTargetCoPartialPair_neg_smul_right
    {r : ℝ} (hr : 0 ≤ r) (x y : ℝ) :
    zeroTargetCoPartialPair x (-(r * y)) =
      r * zeroTargetDivergentPair x y := by
  unfold zeroTargetCoPartialPair zeroTargetDivergentPair
  unfold zeroTargetCUPM zeroTargetCLPM zeroTargetDLPM zeroTargetDUPM
  rw [zeroTargetUpperPart_neg, zeroTargetLowerPart_neg,
    zeroTargetUpperPart_nonneg_smul hr,
    zeroTargetLowerPart_nonneg_smul hr]
  ring

/-- Right-coordinate version for the divergent sector. -/
theorem zeroTargetDivergentPair_neg_smul_right
    {r : ℝ} (hr : 0 ≤ r) (x y : ℝ) :
    zeroTargetDivergentPair x (-(r * y)) =
      r * zeroTargetCoPartialPair x y := by
  unfold zeroTargetCoPartialPair zeroTargetDivergentPair
  unfold zeroTargetCUPM zeroTargetCLPM zeroTargetDLPM zeroTargetDUPM
  rw [zeroTargetUpperPart_neg, zeroTargetLowerPart_neg,
    zeroTargetUpperPart_nonneg_smul hr,
    zeroTargetLowerPart_nonneg_smul hr]
  ring

/-- Scaling and flipping both coordinates preserves the co sector up to `r^2`. -/
theorem zeroTargetCoPartialPair_neg_smul_both
    {r : ℝ} (hr : 0 ≤ r) (x y : ℝ) :
    zeroTargetCoPartialPair (-(r * x)) (-(r * y)) =
      r ^ 2 * zeroTargetCoPartialPair x y := by
  rw [zeroTargetCoPartialPair_neg_smul_left hr,
    zeroTargetDivergentPair_neg_smul_right hr]
  ring

/-- Same double-coordinate scaling for the divergent sector. -/
theorem zeroTargetDivergentPair_neg_smul_both
    {r : ℝ} (hr : 0 ≤ r) (x y : ℝ) :
    zeroTargetDivergentPair (-(r * x)) (-(r * y)) =
      r ^ 2 * zeroTargetDivergentPair x y := by
  rw [zeroTargetDivergentPair_neg_smul_left hr,
    zeroTargetCoPartialPair_neg_smul_right hr]
  ring

/-! ## Exact two-sector fresh-prime square -/

/-- Sum of co-partial mass on all four Mellin-weighted fresh-prime corners. -/
def zeroTargetMellinFreshPrimeSquareCo
    (r x y : ℝ) : ℝ :=
  zeroTargetCoPartialPair x y +
    zeroTargetCoPartialPair (-(r * x)) y +
    zeroTargetCoPartialPair x (-(r * y)) +
    zeroTargetCoPartialPair (-(r * x)) (-(r * y))

/-- Sum of divergent mass on the same four corners. -/
def zeroTargetMellinFreshPrimeSquareDiv
    (r x y : ℝ) : ℝ :=
  zeroTargetDivergentPair x y +
    zeroTargetDivergentPair (-(r * x)) y +
    zeroTargetDivergentPair x (-(r * y)) +
    zeroTargetDivergentPair (-(r * x)) (-(r * y))

/-- **Co-sector row of the exact 2x2 Mellin square matrix.** -/
theorem zeroTargetMellinFreshPrimeSquareCo_eq
    {r : ℝ} (hr : 0 ≤ r) (x y : ℝ) :
    zeroTargetMellinFreshPrimeSquareCo r x y =
      (1 + r ^ 2) * zeroTargetCoPartialPair x y +
        2 * r * zeroTargetDivergentPair x y := by
  unfold zeroTargetMellinFreshPrimeSquareCo
  rw [zeroTargetCoPartialPair_neg_smul_left hr,
    zeroTargetCoPartialPair_neg_smul_right hr,
    zeroTargetCoPartialPair_neg_smul_both hr]
  ring

/-- **Divergent-sector row of the exact 2x2 Mellin square matrix.** -/
theorem zeroTargetMellinFreshPrimeSquareDiv_eq
    {r : ℝ} (hr : 0 ≤ r) (x y : ℝ) :
    zeroTargetMellinFreshPrimeSquareDiv r x y =
      2 * r * zeroTargetCoPartialPair x y +
        (1 + r ^ 2) * zeroTargetDivergentPair x y := by
  unfold zeroTargetMellinFreshPrimeSquareDiv
  rw [zeroTargetDivergentPair_neg_smul_left hr,
    zeroTargetDivergentPair_neg_smul_right hr,
    zeroTargetDivergentPair_neg_smul_both hr]
  ring

/-- **Signed covariance eigenmode.**  The zero-target mode `co-div` is an exact
eigenvector of the Mellin fresh-prime square with eigenvalue `(1-r)^2`. -/
theorem zeroTargetMellinFreshPrimeSquare_excess_eq
    {r : ℝ} (hr : 0 ≤ r) (x y : ℝ) :
    zeroTargetMellinFreshPrimeSquareCo r x y -
        zeroTargetMellinFreshPrimeSquareDiv r x y =
      (1 - r) ^ 2 *
        (zeroTargetCoPartialPair x y - zeroTargetDivergentPair x y) := by
  rw [zeroTargetMellinFreshPrimeSquareCo_eq hr,
    zeroTargetMellinFreshPrimeSquareDiv_eq hr]
  ring

/-- The unsigned sector mode `co+div` has the complementary eigenvalue
`(1+r)^2`. -/
theorem zeroTargetMellinFreshPrimeSquare_total_eq
    {r : ℝ} (hr : 0 ≤ r) (x y : ℝ) :
    zeroTargetMellinFreshPrimeSquareCo r x y +
        zeroTargetMellinFreshPrimeSquareDiv r x y =
      (1 + r) ^ 2 *
        (zeroTargetCoPartialPair x y + zeroTargetDivergentPair x y) := by
  rw [zeroTargetMellinFreshPrimeSquareCo_eq hr,
    zeroTargetMellinFreshPrimeSquareDiv_eq hr]
  ring

/-- **Raw/Othello covariance cancellation has a double zero.**  At ratio one,
the complete fresh-prime square annihilates `co-div` exactly. -/
@[simp] theorem zeroTargetMellinFreshPrimeSquare_excess_one
    (x y : ℝ) :
    zeroTargetMellinFreshPrimeSquareCo 1 x y -
        zeroTargetMellinFreshPrimeSquareDiv 1 x y = 0 := by
  rw [zeroTargetMellinFreshPrimeSquare_excess_eq (by norm_num : (0 : ℝ) ≤ 1)]
  ring

/-- The covariance eigenvalue is literally a square of the one-dimensional
Mellin defect.  This records the second-order vanishing algebraically, without
invoking a derivative API. -/
theorem zeroTargetMellinFreshPrimeSquare_doubleZero_factor (r : ℝ) :
    (1 - r) ^ 2 = (r - 1) ^ 2 := by
  ring

/-- The double corner itself carries `r^2` times the raw signed covariance
mode. -/
theorem zeroTargetMellinFreshPrimeSquare_doubleCorner_excess
    {r : ℝ} (hr : 0 ≤ r) (x y : ℝ) :
    zeroTargetCoPartialPair (-(r * x)) (-(r * y)) -
        zeroTargetDivergentPair (-(r * x)) (-(r * y)) =
      r ^ 2 *
        (zeroTargetCoPartialPair x y - zeroTargetDivergentPair x y) := by
  rw [zeroTargetCoPartialPair_neg_smul_both hr,
    zeroTargetDivergentPair_neg_smul_both hr]
  ring

/-- **Critical q-square interface.**  If the one-coordinate Mellin amplitude
ratio has square `1/p`, then the double fresh-prime corner has exactly the
`1/p` amplitude used by the critical q-square Perron multiplier. -/
theorem zeroTargetMellinFreshPrimeSquare_doubleCorner_critical
    {r : ℝ} (hr : 0 ≤ r) {p : ℕ} (_hp : 0 < p)
    (hcritical : r ^ 2 = 1 / (p : ℝ)) (x y : ℝ) :
    zeroTargetCoPartialPair (-(r * x)) (-(r * y)) -
        zeroTargetDivergentPair (-(r * x)) (-(r * y)) =
      (1 / (p : ℝ)) *
        (zeroTargetCoPartialPair x y - zeroTargetDivergentPair x y) := by
  rw [zeroTargetMellinFreshPrimeSquare_doubleCorner_excess hr, hcritical]

/-- Squaring the critical double-corner amplitude gives the exact `1/p^2`
energy coefficient already used by the Perron quarter-frame. -/
theorem zeroTargetMellinFreshPrimeSquare_critical_energy_coefficient
    {r : ℝ} {p : ℕ} (_hp : 0 < p)
    (hcritical : r ^ 2 = 1 / (p : ℝ)) :
    (r ^ 2) ^ 2 = 1 / (p : ℝ) ^ 2 := by
  rw [hcritical]
  ring

end RHLean.Proof
