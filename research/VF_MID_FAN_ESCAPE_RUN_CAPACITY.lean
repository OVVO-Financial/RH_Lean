import Mathlib
import «research.VF_MID_FINAL_RAW_CLIPPED_TELESCOPE»
import «research.VF_MID_FAN_ESCAPE_CAPACITY_BILLS»

/-!
# Exact frozen-wheel capacity against upper fan escape

This file supplies the upper-wall / prime-cluster half of the fan capacitor.

For a frozen subdoubling run [A,B), the repository already proves

  PrefixSupply(A,B) = PrimeSupply(A,B) + CompositeSurvivorSupply(A,B).

Hence

  PrimeSupply(A,B) <= PrefixSupply(A,B)

with no analytic prime-density estimate.  The prefix supply is a finite wheel
survivor capacity.

The exact upper fan bill from VF_MID_FAN_ESCAPE_CAPACITY_BILLS.lean is the
least natural number of unit prime-count jumps needed to rise from the center
at A^2 above the upper radial wall at B^2.  Therefore, whenever the frozen
prefix supply itself is strictly smaller than that bill, the actual prime
cluster cannot cross the upper wall.

This is a finite capacity contradiction, not a global prime-cluster theorem.
-/

noncomputable section

namespace RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Surviving composite population in the frozen run is nonnegative. -/
theorem vfMidDyadicPrefixCompositeSupply_nonneg
    (A B : ℕ) :
    0 ≤ vfMidDyadicPrefixCompositeSupply A B := by
  unfold vfMidDyadicPrefixCompositeSupply
  positivity

/-- **Exact frozen-wheel upper capacity.**

Actual prime supply over the run cannot exceed the total frozen prefix
survivor population. -/
theorem vfMidDyadicPrimeSupply_le_prefixSupply
    {A B : ℕ}
    (hA : 3 ≤ A) (hAB : A ≤ B) :
    vfMidDyadicPrimeSupply A B ≤
      vfMidDyadicPrefixSupply A A B := by
  have hsplit :=
    vfMidDyadicPrefixSupply_eq_prime_add_composite hA hAB
  have hcomp := vfMidDyadicPrefixCompositeSupply_nonneg A B
  linarith

/-- Natural-number prime jump count between square endpoints. -/
def vfMidDyadicPrimeJumpCount (A B : ℕ) : ℕ :=
  Nat.primeCounting (B ^ 2) - Nat.primeCounting (A ^ 2)

/-- The natural jump count casts exactly to the existing real prime supply. -/
theorem vfMidDyadicPrimeJumpCount_cast_eq_primeSupply
    {A B : ℕ} (hAB : A ≤ B) :
    (vfMidDyadicPrimeJumpCount A B : ℝ) =
      vfMidDyadicPrimeSupply A B := by
  have hsq : A ^ 2 ≤ B ^ 2 :=
    Nat.pow_le_pow_left hAB 2
  have hpc :
      Nat.primeCounting (A ^ 2) ≤ Nat.primeCounting (B ^ 2) :=
    Nat.monotone_primeCounting hsq
  unfold vfMidDyadicPrimeJumpCount vfMidDyadicPrimeSupply
  rw [Nat.cast_sub hpc]

/-- The square-root displacement B-A really lands at B. -/
theorem vfMidRadial_runOffset_add
    {A B : ℕ} (hAB : A ≤ B) :
    A + (B - A) = B := by
  omega

/-- **Frozen prefix capacity below the exact fan bill forbids upper escape.**

The conclusion is stated at the actual natural prime-jump count, before any
starting-center hypothesis is imposed. -/
theorem vfMidRadialUpper_noBreak_of_prefixSupply_lt_bill
    {K : ℝ} {A B : ℕ}
    (hA : 3 ≤ A) (hAB : A ≤ B)
    (hcap :
      vfMidDyadicPrefixSupply A A B <
        (vfMidRadialUpperPrimeJumpBill K A (B - A) : ℝ)) :
    ¬ (vfMidSolvedFantasyRadialUpperCount K B <
      vfMidRadialCenterCount A +
        (vfMidDyadicPrimeJumpCount A B : ℝ)) := by
  have hprimeCap :=
    vfMidDyadicPrimeSupply_le_prefixSupply hA hAB
  have hcast :=
    vfMidDyadicPrimeJumpCount_cast_eq_primeSupply hAB
  have hqreal :
      (vfMidDyadicPrimeJumpCount A B : ℝ) <
        (vfMidRadialUpperPrimeJumpBill K A (B - A) : ℝ) := by
    rw [hcast]
    exact hprimeCap.trans_lt hcap
  have hq :
      vfMidDyadicPrimeJumpCount A B <
        vfMidRadialUpperPrimeJumpBill K A (B - A) := by
    exact_mod_cast hqreal
  have hmin :=
    vfMidRadialUpperPrimeJumpBill_minimal
      K A (B - A) hq
  simpa [vfMidRadial_runOffset_add hAB] using hmin

/-- Prime counting at B^2 is the starting count plus the natural jump count. -/
theorem vfMidPrimeCounting_sq_eq_start_add_jumpCount
    {A B : ℕ} (hAB : A ≤ B) :
    (Nat.primeCounting (B ^ 2) : ℝ) =
      (Nat.primeCounting (A ^ 2) : ℝ) +
        (vfMidDyadicPrimeJumpCount A B : ℝ) := by
  have hsq : A ^ 2 ≤ B ^ 2 :=
    Nat.pow_le_pow_left hAB 2
  have hpc :
      Nat.primeCounting (A ^ 2) ≤ Nat.primeCounting (B ^ 2) :=
    Nat.monotone_primeCounting hsq
  unfold vfMidDyadicPrimeJumpCount
  rw [Nat.cast_sub hpc]
  ring

/-- **Centered-start upper containment from finite wheel capacity.**

If the actual count starts exactly at the fan center at A^2, and even the
entire frozen prefix survivor capacity is smaller than the exact number of
prime jumps needed to clear the upper wall at B^2, then the actual prime count
at B^2 remains below that upper wall.

No global prime-cluster law is used. -/
theorem vfMidRadialUpper_actualPrime_le_of_center_and_prefixCapacity
    {K : ℝ} {A B : ℕ}
    (hA : 3 ≤ A) (hAB : A ≤ B)
    (hcenter :
      (Nat.primeCounting (A ^ 2) : ℝ) =
        vfMidRadialCenterCount A)
    (hcap :
      vfMidDyadicPrefixSupply A A B <
        (vfMidRadialUpperPrimeJumpBill K A (B - A) : ℝ)) :
    (Nat.primeCounting (B ^ 2) : ℝ) ≤
      vfMidSolvedFantasyRadialUpperCount K B := by
  have hnot :=
    vfMidRadialUpper_noBreak_of_prefixSupply_lt_bill hA hAB hcap
  have hcount :=
    vfMidPrimeCounting_sq_eq_start_add_jumpCount hAB
  rw [hcenter] at hcount
  by_contra habove
  have habove' :
      vfMidSolvedFantasyRadialUpperCount K B <
        (Nat.primeCounting (B ^ 2) : ℝ) :=
    lt_of_not_ge habove
  apply hnot
  rw [← hcount]
  exact habove'



end RHLean.Analysis
