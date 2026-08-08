import Mathlib
import RHLean.Analysis.MertensStepFunction

/-!
# Mertens step-function asymptotics

The pointwise power estimate coming from `MertensEnergyBoundedStatement` is
already supplied by the merged `MertensStepFunction` layer.  This module does
only the real-variable lift needed by Mellin continuation: since for `t >= 1`
we have `floor(t) + 1 <= 2t`, every exponent `r > 1/2` gives the required
`M(floor t) = O(t^r)` bound.
-/

open scoped BigOperators

noncomputable section

namespace RHLean.Analysis

open Filter Asymptotics

/-- The Mertens energy criterion gives the real floor-step bound
`M(floor t) = O(t^r)` for every `r > 1/2`.  This is exactly the at-infinity
hypothesis needed by the Mellin-transform continuation theorem. -/
theorem mertensStep_isBigO_rpow_atTop_of_energy
    (hM : MertensEnergyBoundedStatement) {r : ℝ}
    (hr : (1 : ℝ) / 2 < r) :
    mertensStep =O[atTop] fun t : ℝ => t ^ r := by
  rcases mertensStep_powerGrowth_of_energy hM hr with ⟨K, hK, hbound⟩
  have hr0 : 0 ≤ r := by linarith
  refine IsBigO.of_bound (K * Real.rpow 2 r) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have ht0 : 0 ≤ t := le_trans zero_le_one ht
  have hfloor :
      (((⌊t⌋₊ + 1 : ℕ) : ℝ)) ≤ 2 * t := by
    calc
      (((⌊t⌋₊ + 1 : ℕ) : ℝ)) = (⌊t⌋₊ : ℝ) + 1 := by norm_num
      _ ≤ t + 1 := add_le_add_right (Nat.floor_le ht0) 1
      _ ≤ 2 * t := by linarith
  have hfloor0 : 0 ≤ (((⌊t⌋₊ + 1 : ℕ) : ℝ)) := by positivity
  have hpow :
      Real.rpow (((⌊t⌋₊ + 1 : ℕ) : ℝ)) r ≤
        Real.rpow (2 * t) r :=
    Real.rpow_le_rpow hfloor0 hfloor hr0
  have htwo0 : (0 : ℝ) ≤ 2 := by norm_num
  have htPow0 : 0 ≤ Real.rpow t r := Real.rpow_nonneg ht0 r
  calc
    ‖mertensStep t‖ ≤
        K * Real.rpow (((⌊t⌋₊ + 1 : ℕ) : ℝ)) r := hbound t
    _ ≤ K * Real.rpow (2 * t) r :=
      mul_le_mul_of_nonneg_left hpow hK
    _ = (K * Real.rpow 2 r) * Real.rpow t r := by
      rw [Real.mul_rpow htwo0 ht0]
      ring
    _ = (K * Real.rpow 2 r) * ‖t ^ r‖ := by
      rw [Real.norm_of_nonneg htPow0]

end RHLean.Analysis
