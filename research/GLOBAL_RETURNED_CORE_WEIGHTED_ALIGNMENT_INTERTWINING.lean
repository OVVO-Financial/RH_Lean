import Mathlib
import RHLean.Arithmetic.PrimeCombFiniteDifferenceFreshPrime
import «research.STABLE_FAR_CRITICAL_Q2_ENERGY_MULTIPLIER»

/-!
# Weighted prime-alignment intertwining

The raw finite-prime comb already has the exact fresh-prime difference
`f(x) - f(floor(x/p))`, and those floor shifts commute.  The critical Perron
coordinate replaces the unit child coefficient by a scalar local ratio `z`
(and in particular by `m_p(tau) = exp(-2 i tau log p)/p`).

This file records that the same operator algebra survives for an arbitrary
scalar ratio.  Hence the small-prime stacked pictures are instances of one
commuting family of weighted Euler differences, not separate identities.
-/

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic

/-- Weighted one-prime Euler difference. -/
def weightedFreshPrimeDifference
    (z : ℂ) (p : ℕ) (f : ℕ → ℂ) : ℕ → ℂ :=
  fun x => f x - z * f (x / p)

@[simp] theorem weightedFreshPrimeDifference_apply
    (z : ℂ) (p : ℕ) (f : ℕ → ℂ) (x : ℕ) :
    weightedFreshPrimeDifference z p f x = f x - z * f (x / p) := by
  rfl

/-- Unit ratio recovers the raw fresh-prime finite difference. -/
theorem weightedFreshPrimeDifference_one_eq_raw
    (p : ℕ) (f : ℕ → ℂ) :
    weightedFreshPrimeDifference 1 p f = freshPrimeDifference p f := by
  funext x
  simp [weightedFreshPrimeDifference, freshPrimeDifference_apply]

/-- A weighted fresh-prime difference commutes with every floor scale shift. -/
theorem weightedFreshPrimeDifference_shift_comm
    (z : ℂ) (p e : ℕ) (f : ℕ → ℂ) :
    weightedFreshPrimeDifference z p (shift e f) =
      shift e (weightedFreshPrimeDifference z p f) := by
  funext x
  simp only [weightedFreshPrimeDifference_apply, shift]
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm e p]

/-- **Weighted prime intertwining.**  Two prime coordinates commute even with
arbitrary complex local ratios.  The only arithmetic input is commutation of
their floor dilations. -/
theorem weightedFreshPrimeDifference_comm
    (z w : ℂ) (p q : ℕ) (f : ℕ → ℂ) :
    weightedFreshPrimeDifference z p
        (weightedFreshPrimeDifference w q f) =
      weightedFreshPrimeDifference w q
        (weightedFreshPrimeDifference z p f) := by
  funext x
  simp only [weightedFreshPrimeDifference_apply]
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm p q]
  ring

/-- Critical Perron specialization of the weighted one-prime difference. -/
def criticalPerronFreshPrimeDifference
    (tau : ℝ) (p : ℕ) (f : ℕ → ℂ) : ℕ → ℂ :=
  weightedFreshPrimeDifference
    (stableFarCriticalQ2LogMultiplier tau p) p f

/-- The critical Perron prime coordinate commutes with q² daughter descent. -/
theorem criticalPerronFreshPrimeDifference_q2Shift_comm
    (tau : ℝ) (p q : ℕ) (f : ℕ → ℂ) :
    criticalPerronFreshPrimeDifference tau p (shift (q * q) f) =
      shift (q * q) (criticalPerronFreshPrimeDifference tau p f) := by
  exact weightedFreshPrimeDifference_shift_comm
    (stableFarCriticalQ2LogMultiplier tau p) p (q * q) f

/-- Distinct critical Perron prime coordinates intertwine exactly. -/
theorem criticalPerronFreshPrimeDifference_comm
    (tau : ℝ) (p q : ℕ) (f : ℕ → ℂ) :
    criticalPerronFreshPrimeDifference tau p
        (criticalPerronFreshPrimeDifference tau q f) =
      criticalPerronFreshPrimeDifference tau q
        (criticalPerronFreshPrimeDifference tau p f) := by
  exact weightedFreshPrimeDifference_comm
    (stableFarCriticalQ2LogMultiplier tau p)
    (stableFarCriticalQ2LogMultiplier tau q) p q f

/-- At zero frequency the local ratio is literally `1/p`. -/
theorem criticalPerronFreshPrimeDifference_zero
    {p : ℕ} (hp : 0 < p) (f : ℕ → ℂ) (x : ℕ) :
    criticalPerronFreshPrimeDifference 0 p f x =
      f x - (1 / (p : ℂ)) * f (x / p) := by
  unfold criticalPerronFreshPrimeDifference
  rw [weightedFreshPrimeDifference_apply,
    stableFarCriticalQ2LogMultiplier_eq_reciprocal_phase 0 hp]
  simp

end RHLean.Proof
