import Mathlib
import RHLean.Geometry.ComplexSquareRecovery
import «research.STABLE_FAR_CRITICAL_Q2_ENERGY_MULTIPLIER»

/-!
# Realification of the stable-far Perron interface

The squared-complex/Fermat coordinate used throughout the project has a natural
real-pair form

  phi(a + b i) = (a - b, a + b).

A real scalar therefore lands on the diagonal `(r,r)`, while a pure imaginary
scalar lands on the anti-diagonal `(-b,b)`.  On the native Fermat point
`A(c,q) + i B(c,q)`, this map is exactly `(c,q)`: it is the inverse of the
factor-pair encoding already formalized in `RHLean.Geometry`.

This file proves that the map is invertible, preserves the full complex Gram
form after the fixed normalization by `1/2`, and intertwines complex
multiplication with the standard real `2 x 2` multiplication matrix.

Specializing to the Perron multiplier compiled in #708 shows that q^2 descent
is, entirely over the reals, a `1/q` orthogonal planar action whose energy is
exactly multiplied by `1/q^2`.  Cross-owner interaction becomes one explicit
real symmetric Gram kernel.

No RH hypothesis, zero of zeta, LOW-4 estimate, or frame inequality is used.
-/

noncomputable section

namespace RHLean.Proof

/-- Fred Viole's complex-to-real-pair coordinate:
`a + b i -> (a-b, a+b)`. -/
def stableFarComplexToRealPair (z : ℂ) : ℝ × ℝ :=
  (z.re - z.im, z.re + z.im)

/-- Exact inverse of `stableFarComplexToRealPair`. -/
def stableFarRealPairToComplex (v : ℝ × ℝ) : ℂ :=
  ⟨(v.1 + v.2) / 2, (v.2 - v.1) / 2⟩

@[simp] theorem stableFarRealPairToComplex_complexToRealPair (z : ℂ) :
    stableFarRealPairToComplex (stableFarComplexToRealPair z) = z := by
  apply Complex.ext <;>
    simp [stableFarRealPairToComplex, stableFarComplexToRealPair]

@[simp] theorem stableFarComplexToRealPair_realPairToComplex (v : ℝ × ℝ) :
    stableFarComplexToRealPair (stableFarRealPairToComplex v) = v := by
  apply Prod.ext <;>
    simp [stableFarRealPairToComplex, stableFarComplexToRealPair] <;> ring

/-- **Factor-coordinate reconciliation.**  Fred's realification sends the
existing Fermat complex point directly back to its original real factor pair. -/
theorem stableFarComplexToRealPair_fermatPoint (c q : ℝ) :
    stableFarComplexToRealPair (RHLean.Geometry.fermatPoint c q) = (c, q) := by
  apply Prod.ext
  · simpa [stableFarComplexToRealPair, RHLean.Geometry.fermatPoint] using
      RHLean.Geometry.fermatA_sub_fermatB c q
  · simpa [stableFarComplexToRealPair, RHLean.Geometry.fermatPoint] using
      RHLean.Geometry.fermatA_add_fermatB c q

/-- Conversely, the inverse realification of `(c,q)` is exactly the Fermat
point already used by the squared-complex framework. -/
theorem stableFarRealPairToComplex_factorPair (c q : ℝ) :
    stableFarRealPairToComplex (c, q) = RHLean.Geometry.fermatPoint c q := by
  have h := congrArg stableFarRealPairToComplex
    (stableFarComplexToRealPair_fermatPoint c q)
  simpa using h.symm

/-- Real arithmetic is exactly the diagonal in the realified coordinate. -/
@[simp] theorem stableFarComplexToRealPair_ofReal (r : ℝ) :
    stableFarComplexToRealPair (r : ℂ) = (r, r) := by
  simp [stableFarComplexToRealPair]

/-- Pure imaginary arithmetic is exactly the anti-diagonal. -/
@[simp] theorem stableFarComplexToRealPair_pureImaginary (b : ℝ) :
    stableFarComplexToRealPair (Complex.I * (b : ℂ)) = (-b, b) := by
  simp [stableFarComplexToRealPair]

/-- Conjugation swaps the two realified coordinates. -/
@[simp] theorem stableFarComplexToRealPair_star (z : ℂ) :
    stableFarComplexToRealPair (star z) =
      ((stableFarComplexToRealPair z).2,
        (stableFarComplexToRealPair z).1) := by
  simp [stableFarComplexToRealPair]

/-- A conjugate pair lands exactly back on the diagonal. -/
theorem stableFarComplexToRealPair_add_star (z : ℂ) :
    stableFarComplexToRealPair (z + star z) =
      (2 * z.re, 2 * z.re) := by
  apply Prod.ext <;> simp [stableFarComplexToRealPair] <;> ring

/-- Euclidean squared energy on the real pair. -/
def stableFarRealPairEnergy (v : ℝ × ℝ) : ℝ :=
  v.1 ^ 2 + v.2 ^ 2

/-- Euclidean dot product on the real pair. -/
def stableFarRealPairDot (u v : ℝ × ℝ) : ℝ :=
  u.1 * v.1 + u.2 * v.2

/-- Normalize the raw pair energy by the fixed factor introduced by
`a+bi -> (a-b,a+b)`. -/
def stableFarRealPairNormalizedEnergy (v : ℝ × ℝ) : ℝ :=
  stableFarRealPairEnergy v / 2

/-- Normalized real Gram product. -/
def stableFarRealPairNormalizedDot (u v : ℝ × ℝ) : ℝ :=
  stableFarRealPairDot u v / 2

/-- The unnormalized realification has exactly twice the complex energy. -/
theorem stableFarRealPairEnergy_complexToRealPair (z : ℂ) :
    stableFarRealPairEnergy (stableFarComplexToRealPair z) =
      2 * ‖z‖ ^ 2 := by
  rw [Complex.sq_norm]
  simp [stableFarRealPairEnergy, stableFarComplexToRealPair,
    Complex.normSq_apply]
  ring

/-- **Exact Hilbert-space isometry after normalization.** -/
theorem stableFarRealPairNormalizedEnergy_complexToRealPair (z : ℂ) :
    stableFarRealPairNormalizedEnergy (stableFarComplexToRealPair z) =
      ‖z‖ ^ 2 := by
  rw [stableFarRealPairNormalizedEnergy,
    stableFarRealPairEnergy_complexToRealPair]
  ring

/-- A real scalar `(r,r)` therefore has exactly its ordinary square as
normalized real-pair energy. -/
@[simp] theorem stableFarRealPairNormalizedEnergy_diagonal (r : ℝ) :
    stableFarRealPairNormalizedEnergy (r, r) = r ^ 2 := by
  simp [stableFarRealPairNormalizedEnergy, stableFarRealPairEnergy]

/-- The raw real dot product is twice the Hermitian real part. -/
theorem stableFarRealPairDot_complexToRealPair (z w : ℂ) :
    stableFarRealPairDot (stableFarComplexToRealPair z)
        (stableFarComplexToRealPair w) =
      2 * (z * star w).re := by
  simp [stableFarRealPairDot, stableFarComplexToRealPair,
    Complex.mul_re]
  ring

/-- **Exact Gram preservation after normalization.** -/
theorem stableFarRealPairNormalizedDot_complexToRealPair (z w : ℂ) :
    stableFarRealPairNormalizedDot (stableFarComplexToRealPair z)
        (stableFarComplexToRealPair w) =
      (z * star w).re := by
  rw [stableFarRealPairNormalizedDot,
    stableFarRealPairDot_complexToRealPair]
  ring

/-- Standard real two-coordinate representation of multiplication by a complex
scalar. -/
def stableFarRealComplexMul (m : ℂ) (v : ℝ × ℝ) : ℝ × ℝ :=
  (m.re * v.1 - m.im * v.2,
    m.im * v.1 + m.re * v.2)

/-- **Exact commuting square.**  Realifying after complex multiplication is the
same as applying the corresponding real `2 x 2` action after realification. -/
theorem stableFarComplexToRealPair_mul (m z : ℂ) :
    stableFarComplexToRealPair (m * z) =
      stableFarRealComplexMul m (stableFarComplexToRealPair z) := by
  apply Prod.ext
  · simp [stableFarComplexToRealPair, stableFarRealComplexMul,
      Complex.mul_re, Complex.mul_im]
    ring
  · simp [stableFarComplexToRealPair, stableFarRealComplexMul,
      Complex.mul_re, Complex.mul_im]
    ring

/-- The real multiplication matrix scales Euclidean energy by the complex norm
square, with no cross-term loss. -/
theorem stableFarRealPairEnergy_realComplexMul
    (m : ℂ) (v : ℝ × ℝ) :
    stableFarRealPairEnergy (stableFarRealComplexMul m v) =
      Complex.normSq m * stableFarRealPairEnergy v := by
  simp [stableFarRealPairEnergy, stableFarRealComplexMul,
    Complex.normSq_apply]
  ring

/-- The same scaling law in normalized energy. -/
theorem stableFarRealPairNormalizedEnergy_realComplexMul
    (m : ℂ) (v : ℝ × ℝ) :
    stableFarRealPairNormalizedEnergy (stableFarRealComplexMul m v) =
      Complex.normSq m * stableFarRealPairNormalizedEnergy v := by
  unfold stableFarRealPairNormalizedEnergy
  rw [stableFarRealPairEnergy_realComplexMul]
  ring

/-- Real-pair version of the #708 critical q^2 multiplier. -/
def stableFarCriticalQ2RealAction
    (tau : ℝ) (q : ℕ) (v : ℝ × ℝ) : ℝ × ℝ :=
  stableFarRealComplexMul (stableFarCriticalQ2LogMultiplier tau q) v

/-- The #708 complex q^2 action and the real-pair q^2 action are literally the
same operator in two coordinates. -/
theorem stableFarComplexToRealPair_criticalQ2_mul
    (tau : ℝ) (q : ℕ) (z : ℂ) :
    stableFarComplexToRealPair
        (stableFarCriticalQ2LogMultiplier tau q * z) =
      stableFarCriticalQ2RealAction tau q
        (stableFarComplexToRealPair z) := by
  exact stableFarComplexToRealPair_mul _ _

/-- **Exact real q^-2 energy law.**  The critical q^2 Perron action is a real
planar action with energy contraction exactly `1/q^2`. -/
theorem stableFarCriticalQ2RealAction_energy
    (tau : ℝ) {q : ℕ} (hq : 0 < q) (v : ℝ × ℝ) :
    stableFarRealPairEnergy (stableFarCriticalQ2RealAction tau q v) =
      (1 / (q : ℝ) ^ 2) * stableFarRealPairEnergy v := by
  unfold stableFarCriticalQ2RealAction
  rw [stableFarRealPairEnergy_realComplexMul]
  have hm :
      Complex.normSq (stableFarCriticalQ2LogMultiplier tau q) =
        1 / (q : ℝ) ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    exact norm_sq_stableFarCriticalQ2LogMultiplier tau hq
  rw [hm]

/-- The q^-2 law preserves the normalized Hilbert-space convention exactly. -/
theorem stableFarCriticalQ2RealAction_normalizedEnergy
    (tau : ℝ) {q : ℕ} (hq : 0 < q) (v : ℝ × ℝ) :
    stableFarRealPairNormalizedEnergy (stableFarCriticalQ2RealAction tau q v) =
      (1 / (q : ℝ) ^ 2) * stableFarRealPairNormalizedEnergy v := by
  unfold stableFarRealPairNormalizedEnergy
  rw [stableFarCriticalQ2RealAction_energy tau hq]
  ring

/-- Acting on a real arithmetic scalar `(a,a)` resolves its Perron phase into
two real coordinates. -/
theorem stableFarCriticalQ2RealAction_diagonal
    (tau : ℝ) (q : ℕ) (a : ℝ) :
    stableFarCriticalQ2RealAction tau q (a, a) =
      ((stableFarCriticalQ2LogMultiplier tau q).re * a -
          (stableFarCriticalQ2LogMultiplier tau q).im * a,
        (stableFarCriticalQ2LogMultiplier tau q).im * a +
          (stableFarCriticalQ2LogMultiplier tau q).re * a) := by
  rfl

/-- Conjugate multipliers acting on one real diagonal scalar cancel their
anti-diagonal components exactly and return to the arithmetic diagonal. -/
theorem stableFarRealComplexMul_star_add_on_diagonal
    (m : ℂ) (a : ℝ) :
    let u := stableFarRealComplexMul m (a, a)
    let v := stableFarRealComplexMul (star m) (a, a)
    (u.1 + v.1, u.2 + v.2) =
      (2 * m.re * a, 2 * m.re * a) := by
  simp [stableFarRealComplexMul]
  ring

/-! ## The remaining cross-owner interaction is a real Gram kernel -/

/-- Real symmetric kernel carried by two critical q^2 Perron multipliers. -/
def stableFarCriticalQ2RealGramKernel
    (tau : ℝ) (q r : ℕ) : ℝ :=
  (stableFarCriticalQ2LogMultiplier tau q).re *
      (stableFarCriticalQ2LogMultiplier tau r).re +
    (stableFarCriticalQ2LogMultiplier tau q).im *
      (stableFarCriticalQ2LogMultiplier tau r).im

/-- The real kernel is exactly the Hermitian real part, but is now expressed as
one ordinary real scalar. -/
theorem stableFarCriticalQ2RealGramKernel_eq_re_mul_star
    (tau : ℝ) (q r : ℕ) :
    stableFarCriticalQ2RealGramKernel tau q r =
      (stableFarCriticalQ2LogMultiplier tau q *
        star (stableFarCriticalQ2LogMultiplier tau r)).re := by
  simp [stableFarCriticalQ2RealGramKernel, Complex.mul_re]
  ring

/-- Cross-owner Perron interaction of real arithmetic amplitudes is exactly the
real Gram kernel; no complex norm or triangle inequality has been taken. -/
theorem stableFarCriticalQ2RealAction_diagonal_normalizedDot
    (tau : ℝ) (q r : ℕ) (a b : ℝ) :
    stableFarRealPairNormalizedDot
        (stableFarCriticalQ2RealAction tau q (a, a))
        (stableFarCriticalQ2RealAction tau r (b, b)) =
      a * b * stableFarCriticalQ2RealGramKernel tau q r := by
  simp [stableFarRealPairNormalizedDot, stableFarRealPairDot,
    stableFarCriticalQ2RealAction, stableFarRealComplexMul,
    stableFarCriticalQ2RealGramKernel]
  ring

/-- Diagonal of the real Gram kernel is exactly the q^-2 daughter-energy
multiplier already compiled in #708. -/
theorem stableFarCriticalQ2RealGramKernel_self
    (tau : ℝ) {q : ℕ} (hq : 0 < q) :
    stableFarCriticalQ2RealGramKernel tau q q =
      1 / (q : ℝ) ^ 2 := by
  have hm :
      Complex.normSq (stableFarCriticalQ2LogMultiplier tau q) =
        1 / (q : ℝ) ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    exact norm_sq_stableFarCriticalQ2LogMultiplier tau hq
  simpa [stableFarCriticalQ2RealGramKernel, Complex.normSq_apply,
    pow_two] using hm

/-- The realified returned-fibre Perron projection. -/
def stableFarReturnedLogFrequencyCenteredRealPair
    (tau : ℝ) (R r p : ℕ) : ℝ × ℝ :=
  stableFarComplexToRealPair
    (stableFarReturnedLogFrequencyCenteredMass tau R r p)

/-- At zero frequency the returned-fibre Perron projection is genuinely real,
so its realification lies on the diagonal. -/
theorem stableFarReturnedLogFrequencyCenteredRealPair_zero_diagonal
    {R r p : ℕ} (hr : r.Prime) (hp : p.Prime) :
    stableFarReturnedLogFrequencyCenteredRealPair 0 R r p =
      ((stableFarReturnedLogFrequencyCenteredMass 0 R r p).re,
        (stableFarReturnedLogFrequencyCenteredMass 0 R r p).re) := by
  unfold stableFarReturnedLogFrequencyCenteredRealPair
  rw [stableFarReturnedLogFrequencyCenteredMass_zero hr hp]
  simp [stableFarComplexToRealPair, canonicalMoebiusWeight]

end RHLean.Proof
