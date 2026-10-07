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
  have hcount :=
    primeCard_Ioc_add_primeCounting_eq hsq
  have hpc :
      Nat.primeCounting (A ^ 2) ≤ Nat.primeCounting (B ^ 2) := by
    omega
  unfold vfMidDyadicPrimeJumpCount vfMidDyadicPrimeSupply
  rw [Nat.cast_sub hpc]
  norm_num

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
  have hcount :=
    primeCard_Ioc_add_primeCounting_eq hsq
  have hpc :
      Nat.primeCounting (A ^ 2) ≤ Nat.primeCounting (B ^ 2) := by
    omega
  unfold vfMidDyadicPrimeJumpCount
  rw [Nat.cast_sub hpc]
  push_cast
  linarith

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


/-! ## Variable-prefix wheel capacity over a complete square run -/

/-- Actual prime population over the consecutive square blocks
`R in [A,A+s)`, kept as a natural number for direct comparison with the
integer upper-wall jump bill. -/
def vfMidSquareRunPrimeSupply (A s : ℕ) : ℕ :=
  ∑ R ∈ Finset.Ico A (A + s), vfMidIntegerBlockPrimeSupply R

/-- Deterministic run capacity obtained by choosing an admissible prefix-wheel
cutoff independently in every block. -/
def vfMidSquareRunPrefixWheelCapacity
    (S : ℕ → ℕ) (A s : ℕ) : ℕ :=
  ∑ R ∈ Finset.Ico A (A + s), vfMidPrefixWheelEnvelope (S R) R

/-- **Exact finite run wheel capacity.**

Every block may use its own prefix cutoff `S R <= R`; summing the compiled
blockwise envelopes gives a deterministic upper bound for the complete actual
prime population of the run. -/
theorem vfMidSquareRunPrimeSupply_le_prefixWheelCapacity
    (S : ℕ → ℕ) (A s : ℕ)
    (hA : 2 ≤ A)
    (hS : ∀ R ∈ Finset.Ico A (A + s), S R ≤ R) :
    vfMidSquareRunPrimeSupply A s ≤
      vfMidSquareRunPrefixWheelCapacity S A s := by
  unfold vfMidSquareRunPrimeSupply vfMidSquareRunPrefixWheelCapacity
  apply Finset.sum_le_sum
  intro R hR
  have hAR : A ≤ R := (Finset.mem_Ico.mp hR).1
  have hR2 : 2 ≤ R := hA.trans hAR
  exact
    vfMidIntegerBlockPrimeSupply_le_prefixWheelEnvelope
      (S R) R hR2 (hS R hR)

/-- The natural run population is exactly the existing real dyadic prime
supply. -/
theorem vfMidSquareRunPrimeSupply_cast_eq_dyadicPrimeSupply
    (A s : ℕ) :
    (vfMidSquareRunPrimeSupply A s : ℝ) =
      vfMidDyadicPrimeSupply A (A + s) := by
  rw [vfMidDyadicPrimeSupply_eq_sum_blockPrimeSupply
    A (A + s) (by omega)]
  unfold vfMidSquareRunPrimeSupply
  push_cast
  rfl

/-- **Variable-prefix wheel capacity below the fan bill forbids upper escape.**

This is the exact finite-capacity contradiction in the same natural-count
currency as the upper jump bill. -/
theorem vfMidRadialUpper_noBreak_of_runPrefixWheelCapacity_lt_bill
    (S : ℕ → ℕ) (K : ℝ) (A s : ℕ)
    (hA : 2 ≤ A)
    (hS : ∀ R ∈ Finset.Ico A (A + s), S R ≤ R)
    (hcap :
      vfMidSquareRunPrefixWheelCapacity S A s <
        vfMidRadialUpperPrimeJumpBill K A s) :
    ¬ (vfMidSolvedFantasyRadialUpperCount K (A + s) <
      vfMidRadialCenterCount A +
        (vfMidSquareRunPrimeSupply A s : ℝ)) := by
  have hsupply :=
    vfMidSquareRunPrimeSupply_le_prefixWheelCapacity S A s hA hS
  have hq :
      vfMidSquareRunPrimeSupply A s <
        vfMidRadialUpperPrimeJumpBill K A s :=
    hsupply.trans_lt hcap
  exact vfMidRadialUpperPrimeJumpBill_minimal K A s hq

/-- The same upper no-crossing theorem written directly as the actual
square-endpoint prime-count increment. -/
theorem vfMidRadialUpper_noBreak_of_runPrefixWheelCapacity_lt_bill_primeCounting
    (S : ℕ → ℕ) (K : ℝ) (A s : ℕ)
    (hA : 2 ≤ A)
    (hS : ∀ R ∈ Finset.Ico A (A + s), S R ≤ R)
    (hcap :
      vfMidSquareRunPrefixWheelCapacity S A s <
        vfMidRadialUpperPrimeJumpBill K A s) :
    ¬ (vfMidSolvedFantasyRadialUpperCount K (A + s) <
      vfMidRadialCenterCount A +
        ((Nat.primeCounting ((A + s) ^ 2) : ℝ) -
          (Nat.primeCounting (A ^ 2) : ℝ))) := by
  have hno :=
    vfMidRadialUpper_noBreak_of_runPrefixWheelCapacity_lt_bill
      S K A s hA hS hcap
  have hrun :=
    vfMidSquareRunPrimeSupply_cast_eq_dyadicPrimeSupply A s
  unfold vfMidDyadicPrimeSupply at hrun
  simpa [hrun] using hno

/-- **One-block wheel specialization.**

Any single admissible prefix-wheel envelope which is smaller than the exact
one-block jump bill already forbids an upper-wall crossing in that block. -/
theorem vfMidRadialUpper_noBreak_oneBlock_of_prefixWheelEnvelope_lt_bill
    (K : ℝ) (T R : ℕ)
    (hR : 2 ≤ R) (hTR : T ≤ R)
    (hcap :
      vfMidPrefixWheelEnvelope T R <
        vfMidRadialUpperPrimeJumpBill K R 1) :
    ¬ (vfMidSolvedFantasyRadialUpperCount K (R + 1) <
      vfMidRadialCenterCount R +
        (vfMidIntegerBlockPrimeSupply R : ℝ)) := by
  have hsupply :=
    vfMidIntegerBlockPrimeSupply_le_prefixWheelEnvelope T R hR hTR
  have hq :
      vfMidIntegerBlockPrimeSupply R <
        vfMidRadialUpperPrimeJumpBill K R 1 :=
    hsupply.trans_lt hcap
  have hmin :=
    vfMidRadialUpperPrimeJumpBill_minimal K R 1 hq
  simpa using hmin

/-- Coarse all-scale fallback: summing the compiled block bound
`P_R <= R` over a run. -/
theorem vfMidSquareRunPrimeSupply_le_sum_roots
    (A s : ℕ) (hA : 2 ≤ A) :
    vfMidSquareRunPrimeSupply A s ≤
      ∑ R ∈ Finset.Ico A (A + s), R := by
  unfold vfMidSquareRunPrimeSupply
  apply Finset.sum_le_sum
  intro R hR
  have hAR : A ≤ R := (Finset.mem_Ico.mp hR).1
  exact vfMidIntegerBlockPrimeSupply_le_R R (hA.trans hAR)


end RHLean.Analysis
