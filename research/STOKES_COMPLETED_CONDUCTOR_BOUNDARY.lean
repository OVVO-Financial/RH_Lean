import Mathlib
import RHLean.Analysis.RamanujanDivisorBoundary
import RHLean.Analysis.CorrectedConductorBoundaryDefectGeneral

/-!
# Completed conductor periods leave only one endpoint residue

This is the exact Ramanujan/divisor-boundary version of the endpoint-frequency
picture.  A divisor-residue boundary is periodic in its upper endpoint with
period equal to its modulus.  Hence every complete period may be removed
algebraically, leaving only one final incomplete residue interval.

The existing short-interval theorem then gives the sharp uniform bound

  |divisorIntervalBoundary d a lower upper| <= d

for every positive modulus `d` and every finite interval.  No probability,
prime-spacing input, or asymptotic estimate is used.
-/

noncomputable section

namespace RHLean.Analysis

/-- **Exact completed-period reduction.**  A divisor boundary on an arbitrary
interval equals the same boundary on the residual incomplete `d`-period. -/
theorem divisorIntervalBoundary_eq_residualPeriod
    {d : ℕ} (hd : 0 < d)
    (a lower upper : ℕ) (hlower : lower ≤ upper) :
    divisorIntervalBoundary d a lower upper =
      divisorIntervalBoundary d a lower
        (lower + ((upper - lower) % d)) := by
  let n := upper - lower
  let r := n % d
  let c := n / d
  have hupper : upper = lower + n := by
    dsimp [n]
    omega
  have hdivmod : n = c * d + r := by
    dsimp [c, r]
    calc
      upper - lower = d * ((upper - lower) / d) + (upper - lower) % d :=
        (Nat.div_add_mod (upper - lower) d).symm
      _ = ((upper - lower) / d) * d + (upper - lower) % d := by
        rw [Nat.mul_comm d ((upper - lower) / d)]
  have hre : lower ≤ lower + r := Nat.le_add_right _ _
  have harg : upper = (lower + r) + c * d := by
    rw [hupper, hdivmod]
    omega
  have hdcd : d ∣ c * d := by
    exact dvd_mul_left d c
  calc
    divisorIntervalBoundary d a lower upper =
        divisorIntervalBoundary d a lower ((lower + r) + c * d) := by
          rw [harg]
    _ = divisorIntervalBoundary d a lower (lower + r) :=
      divisorIntervalBoundary_add_multiple
        d a lower (lower + r) (c * d) hd hdcd hre
    _ = divisorIntervalBoundary d a lower
        (lower + ((upper - lower) % d)) := by
          rfl

/-- **Sharp deterministic endpoint-alignment bound.**

Every completed residue period cancels exactly.  The sole surviving incomplete
period contributes at most one modulus to the centered residue discrepancy. -/
theorem abs_divisorIntervalBoundary_le_modulus
    (d a lower upper : ℕ)
    (hd : 0 < d) (hlower : lower ≤ upper) :
    |divisorIntervalBoundary d a lower upper| ≤ (d : ℤ) := by
  rw [divisorIntervalBoundary_eq_residualPeriod hd a lower upper hlower]
  let r := (upper - lower) % d
  have hrlt : r < d := by
    dsimp [r]
    exact Nat.mod_lt _ hd
  have hre : lower ≤ lower + r := Nat.le_add_right _ _
  have hshort : (lower + r) - lower < d := by
    omega
  exact abs_divisorIntervalBoundary_le_modulus_of_short
    d a lower (lower + r) hre hshort

end RHLean.Analysis
