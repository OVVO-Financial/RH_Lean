import Mathlib
import RHLean.Analysis.PhysicalDegreeOneLeastSquareChannels
import RHLean.Arithmetic.PrimeWheelThreeSlotRecovery

/-!
# Exceptional least-square local intertwining

This file begins the physical LOCAL-BLOCK theorem on the actual least-square
channels.  The first case `q=3` is already strong enough to stress-test the
separation between the finite CRT blocker wheel and the full square-root
recovery wheel.

One complete nine-edge least-3 block is an unrestricted Möbius interval by the
existing physical recurrence.  Replacing both Mertens endpoints by the exact
`raw - 2*smooth` three-slot recovered prefix gives a LOCAL-BLOCK identity for
an arbitrary recovery wheel `S` satisfying square-root coverage.  No selected
CRT/blocker wheel appears in the theorem.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic

/-- **Physical q=3 LOCAL-BLOCK.**  A complete least-`3^2` physical block is
exactly the difference of the full recovered three-slot field at its two local
endpoints.  The recovery wheel `S` is arbitrary subject only to its own prime
coverage hypotheses; it is not identified with a finite blocker wheel. -/
theorem physicalD9_nine_step_eq_recoveredThreeSlot_interval
    (S : Finset ℕ) (upper L : ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hcover : PrimeWheelSqrtCoverage S upper)
    (hupper : 36 * L + 32 ≤ upper) :
    physicalD9 (9 * (L + 1)) - physicalD9 (9 * L) =
      primeWheelThreeSlotRecoveredPrefix S upper (9 * L + 8) -
        primeWheelThreeSlotRecoveredPrefix S upper (9 * L + 2) := by
  have hhi : 4 * (9 * L + 8) ≤ upper := by
    nlinarith
  have hlo : 4 * (9 * L + 2) ≤ upper := by
    omega
  have hrecHi :=
    primeWheelThreeSlotRecoveredPrefix_eq_fourSlotCellSum
      S upper (9 * L + 8) hprime hcover hhi
  have hrecLo :=
    primeWheelThreeSlotRecoveredPrefix_eq_fourSlotCellSum
      S upper (9 * L + 2) hprime hcover hlo
  have hmHi := moebiusPositivePrefix_four_mul_eq_fourSlotCellSum (9 * L + 8)
  have hmLo := moebiusPositivePrefix_four_mul_eq_fourSlotCellSum (9 * L + 2)
  rw [physicalD9_nine_step_recurrence]
  rw [show 36 * L + 32 = 4 * (9 * L + 8) by ring,
    show 36 * L + 8 = 4 * (9 * L + 2) by ring]
  rw [hmHi, hmLo, ← hrecHi, ← hrecLo]

end RHLean.Analysis
