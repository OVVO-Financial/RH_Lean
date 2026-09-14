import Mathlib
import «research.STABLE_FAR_CRITICAL_Q2_ENERGY_MULTIPLIER»

/-!
# Realification of the stable-far Perron interface

The squared-complex/Fermat coordinate used throughout the project has a natural
real-pair form

  phi(a + b i) = (a - b, a + b).

A real scalar therefore lands on the diagonal `(r,r)`, while a pure imaginary
scalar lands on the anti-diagonal `(-b,b)`.  This file proves that this is an
invertible real coordinate change, preserves the complex quadratic form up to
the fixed factor `2`, and intertwines complex multiplication with the standard
real `2 x 2` multiplication matrix.

Specializing to the Perron multiplier compiled in #708 shows that q^2 descent
is, entirely over the reals, a `1/q` orthogonal planar action whose energy is
exactly multiplied by `1/q^2`.

No RH hypothesis, zero of zeta, LOW-4 estimate, or norm inequality is used.
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
  apply Complex.ext
  · simp [stableFarRealPairToComplex, stableFarComplexToRealPair]
    ring
  · simp [stableFarRealPairToComplex, stableFarComplexToRealPair]
    ring

@[simp] theorem stableFarComplexToRealPair_realPairToComplex (v : ℝ × ℝ) :
    stableFarComplexToRealPair (stableFarRealPairToComplex v) = v := by
  apply Prod.ext
  · simp [stableFarRealPairToComplex, stableFarComplexToRealPair]
    ring
  · simp [stableFarRealPairToComplex, stableFarComplexToRealPair]
    ring

/-- Real arithmetic is exactly the diagonal in the realified coordinate. -/
@[simp] theorem stableFarComplexToRealPair_ofReal (r : ℝ) :
    stableFarComplexToRealPair (r : ℂ) = (r, r) := by
  simp [stableFarComplexToRealPair]

/-- Pure imaginary arithmetic is exactly the anti-diagonal. -/
@[simp] theorem stableFarComplexToRealPair_pureImaginary (b : ℝ) :
    stableFarComplexToRealPair (Complex.I * (b : ℂ)) = (-b, b) := by
  simp [stableFarComplexToRealPair]

/-- Conjugation swaps the two realified coordinates. -/
@[simp] theorem stableFarComplexToRealPair_conj (z : ℂ) :
    stableFarComplexToRealPair (conj z) =
      ((stableFarComplexToRealPair z).2,
        (stableFarComplexToRealPair z).1) := by
  simp [stableFarComplexToRealPair]

/-- A conjugate pair lands exactly back on the diagonal. -/
theorem stableFarComplexToRealPair_add_conj (z : ℂ) :
    stableFarComplexToRealPair (z + conj z) =
      (2 * z.re, 2 * z.re) := by
  apply Prod.ext <;> simp [stableFarComplexToRealPair] <;> ring

/-- Euclidean squared energy on the real pair. -/
def stableFarRealPairEnergy (v : ℝ × ℝ) : ℝ :=
  v.1 ^ 2 + v.2 ^ 2

/-- Euclidean dot product on the real pair. -/
def stableFarRealPairDot (u v : ℝ × ℝ) : ℝ :=
  u.1 * v.1 + u.2 * v.2

/-- The realification preserves complex energy up to the fixed factor `2`. -/
theorem stableFarRealPairEnergy_complexToRealPair (z : ℂ) :
    stableFarRealPairEnergy (stableFarComplexToRealPair z) =
      2 * ‖z‖ ^ 2 := by
  rw [Complex.sq_norm]
  simp [stableFarRealPairEnergy, stableFarComplexToRealPair,
    Complex.normSq_apply]
  ring

/-- The real dot product is twice the Hermitian real part.  Hence Gram data is
preserved exactly up to the same fixed factor `2`. -/
theorem stableFarRealPairDot_complexToRealPair (z w : ℂ) :
    stableFarRealPairDot (stableFarComplexToRealPair z)
        (stableFarComplexToRealPair w) =
      2 * (z * conj w).re := by
  simp [stableFarRealPairDot, stableFarComplexToRealPair,
    Complex.mul_re]
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
theorem stableFarRealComplexMul_conj_add_on_diagonal
    (m : ℂ) (a : ℝ) :
    let u := stableFarRealComplexMul m (a, a)
    let v := stableFarRealComplexMul (conj m) (a, a)
    (u.1 + v.1, u.2 + v.2) =
      (2 * m.re * a, 2 * m.re * a) := by
  simp [stableFarRealComplexMul]
  ring

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
  simp [stableFarComplexToRealPair]

end RHLean.Proof
