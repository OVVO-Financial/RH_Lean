import Mathlib
import «research.VF_MID_PHI_CUTOFF_TELESCOPE»

/-!
# Odd-prefixed Li transform for the VF owner transfer

The VF dyadic reduction freezes the actual prime prefix through 2 before the
late-owner correction begins.  The repository's exact Li singleton weight at
q=2 is zero.  Therefore a comparison against the unmodified Li state carries
a deterministic mismatch already at the lower cutoff.

This file removes that mismatch exactly.

For an all-scale Li state L define

  Phi_oddLi(N,y) = Phi_L(N,y) - Phi_L(floor(N/2),y).

This is the quotient-sum transform after applying the actual hard-core factor
I-A_2 to the Li model.  Since the q=2 Li weight is zero and activated floor
operators commute, this is the natural Li evolution with the actual parity
prefix already installed.

At cutoff 2 it is exactly the actual prefix-wheel count F_2(N).  Hence the
actual-minus-oddLi transformed displacement is identically zero at the frozen
prefix.  The later displacement telescope therefore has only its upper
boundary term.

No quantitative estimate is asserted here.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- The repository's exact Li singleton mass at site two is zero. -/
theorem primeSievePNTDensity_two_eq_zero :
    primeSievePNTDensity 2 = 0 := by
  have hLi2 :
      logarithmicIntegralFromTwo (((2 : ℕ) : ℝ)) = 0 := by
    norm_num [logarithmicIntegralFromTwo]
  have hLi1 :
      logarithmicIntegralFromTwo (((2 - 1 : ℕ) : ℝ)) = 0 := by
    norm_num [logarithmicIntegralFromTwo_one]
  unfold primeSievePNTDensity
  rw [hLi2, hLi1]
  simp

private theorem primeFrequencyState_cutoff_one
    {w : ℕ → ℂ} {S : ℕ → ℕ → ℂ}
    (hS : IsPrimeFrequencyState w S)
    {x : ℕ} (hx : 1 ≤ x) :
    S x 1 = 1 := by
  rw [hS x 1]
  unfold primeFrequencyStep
  rw [min_eq_right hx]
  simp

/-- Every frequency-state transform at cutoff one is just the number of
positive integer sites up to the endpoint. -/
theorem primeFrequencyCumulativeTransform_one_eq_endpoint
    {w : ℕ → ℂ} {S : ℕ → ℕ → ℂ}
    (hS : IsPrimeFrequencyState w S)
    (N : ℕ) :
    primeFrequencyCumulativeTransform S N 1 = (N : ℂ) := by
  unfold primeFrequencyCumulativeTransform
  calc
    (∑ k ∈ Finset.Icc 1 N, S (N / k) 1) =
        ∑ _k ∈ Finset.Icc 1 N, (1 : ℂ) := by
          apply Finset.sum_congr rfl
          intro k hk
          have hkI := Finset.mem_Icc.mp hk
          have hkpos : 0 < k := by omega
          have hchild : 1 ≤ N / k :=
            (Nat.one_le_div_iff hkpos).2 hkI.2
          exact primeFrequencyState_cutoff_one hS hchild
    _ = (N : ℂ) := by
          rw [Finset.sum_const, Nat.card_Icc]
          simp

/-- Phi after installing the actual parity factor on an exact-Li state. -/
def vfMidOddLiCumulativeTransform
    (L : ℕ → ℕ → ℂ) (N y : ℕ) : ℂ :=
  primeFrequencyCumulativeTransform L N y -
    primeFrequencyCumulativeTransform L (N / 2) y

/-- At cutoff two the odd-prefixed Li transform is exactly the actual
fixed-prefix survivor count. -/
theorem vfMidOddLiCumulativeTransform_two_eq_prefixWheelCounting
    {L : ℕ → ℕ → ℂ}
    (hL : IsAllScaleLiState L)
    (N : ℕ) :
    vfMidOddLiCumulativeTransform L N 2 =
      (vfMidPrefixWheelCounting 2 N : ℂ) := by
  have hL' : IsPrimeFrequencyState primeSievePNTDensity L := hL
  have hN :=
    primeFrequencyCumulativeTransform_cutoff_step
      hL' N 2 (by norm_num)
  have hN2 :=
    primeFrequencyCumulativeTransform_cutoff_step
      hL' (N / 2) 2 (by norm_num)
  rw [primeSievePNTDensity_two_eq_zero, zero_mul, sub_zero,
    primeFrequencyCumulativeTransform_one_eq_endpoint hL'] at hN hN2
  have hpref :=
    vfMidPrefixWheelCounting_cast_complex_step
      N 2 (by norm_num)
  rw [vfMidPrefixWheelCounting_one] at hpref
  norm_num [primeSievePrimeIndicator] at hpref
  unfold vfMidOddLiCumulativeTransform
  rw [hN, hN2]
  exact hpref.symm

/-- The odd-prefixed Li transform evolves by the same Li hard-core recurrence
at every later site q>=3. -/
theorem vfMidOddLiCumulativeTransform_cutoff_step
    {L : ℕ → ℕ → ℂ}
    (hL : IsAllScaleLiState L)
    (N q : ℕ) (hq : 3 ≤ q) :
    vfMidOddLiCumulativeTransform L N q =
      vfMidOddLiCumulativeTransform L N (q - 1) -
        primeSievePNTDensity q *
          vfMidOddLiCumulativeTransform L (N / q) (q - 1) := by
  have hL' : IsPrimeFrequencyState primeSievePNTDensity L := hL
  have hN :=
    primeFrequencyCumulativeTransform_cutoff_step hL' N q (by omega)
  have hN2 :=
    primeFrequencyCumulativeTransform_cutoff_step hL' (N / 2) q (by omega)
  have hdiv :
      (N / 2) / q = (N / q) / 2 := by
    simp only [Nat.div_div_eq_div_mul]
    rw [Nat.mul_comm 2 q]
  unfold vfMidOddLiCumulativeTransform
  rw [hN, hN2, hdiv]
  ring

/-- Actual-minus-oddLi transformed displacement. -/
def vfMidOddLiCumulativeDisplacement
    (Actual L : ℕ → ℕ → ℂ) (N y : ℕ) : ℂ :=
  primeFrequencyCumulativeTransform Actual N y -
    vfMidOddLiCumulativeTransform L N y

/-- The transformed displacement vanishes exactly at the frozen parity
prefix. -/
theorem vfMidOddLiCumulativeDisplacement_two_eq_zero
    {Actual L : ℕ → ℕ → ℂ}
    (hActual : IsAllScaleActualPrimeState Actual)
    (hL : IsAllScaleLiState L)
    (N : ℕ) :
    vfMidOddLiCumulativeDisplacement Actual L N 2 = 0 := by
  unfold vfMidOddLiCumulativeDisplacement
  rw [actualPrimeCumulativeTransform_eq_prefixWheelCounting
        hActual N 2 (by norm_num),
      vfMidOddLiCumulativeTransform_two_eq_prefixWheelCounting hL N]
  ring

/-- After cutoff two, the odd-prefixed displacement has exactly the same
forcing/propagation recurrence as the original actual-minus-Li displacement. -/
theorem vfMidOddLiCumulativeDisplacement_cutoff_step
    {Actual L : ℕ → ℕ → ℂ}
    (hActual : IsAllScaleActualPrimeState Actual)
    (hL : IsAllScaleLiState L)
    (N q : ℕ) (hq : 3 ≤ q) :
    vfMidOddLiCumulativeDisplacement Actual L N q =
      vfMidOddLiCumulativeDisplacement Actual L N (q - 1) -
        primeSievePNTDensity q *
          vfMidOddLiCumulativeDisplacement Actual L (N / q) (q - 1) -
        (primeSievePrimeIndicator q - primeSievePNTDensity q) *
          primeFrequencyCumulativeTransform Actual (N / q) (q - 1) := by
  have hA' : IsPrimeFrequencyState primeSievePrimeIndicator Actual := hActual
  have hAstep :=
    primeFrequencyCumulativeTransform_cutoff_step hA' N q (by omega)
  have hLstep :=
    vfMidOddLiCumulativeTransform_cutoff_step hL N q hq
  unfold vfMidOddLiCumulativeDisplacement
  rw [hAstep, hLstep]
  ring

/-! ## Square-interval coordinates -/

def vfMidOddLiSquareInterval
    (L : ℕ → ℕ → ℂ) (R y : ℕ) : ℂ :=
  vfMidOddLiCumulativeTransform L ((R + 1) ^ 2 - 1) y -
    vfMidOddLiCumulativeTransform L (R ^ 2) y

def vfMidOddLiOwnerChildInterval
    (L : ℕ → ℕ → ℂ) (R q : ℕ) : ℂ :=
  vfMidOddLiCumulativeTransform L
      (((R + 1) ^ 2 - 1) / q) (q - 1) -
    vfMidOddLiCumulativeTransform L
      (R ^ 2 / q) (q - 1)

theorem vfMidOddLiSquareInterval_cutoff_step
    {L : ℕ → ℕ → ℂ}
    (hL : IsAllScaleLiState L)
    (R q : ℕ) (hq : 3 ≤ q) :
    vfMidOddLiSquareInterval L R q =
      vfMidOddLiSquareInterval L R (q - 1) -
        primeSievePNTDensity q *
          vfMidOddLiOwnerChildInterval L R q := by
  unfold vfMidOddLiSquareInterval vfMidOddLiOwnerChildInterval
  rw [vfMidOddLiCumulativeTransform_cutoff_step hL
        ((R + 1) ^ 2 - 1) q hq,
      vfMidOddLiCumulativeTransform_cutoff_step hL
        (R ^ 2) q hq]
  ring

def vfMidOddLiWeightedCutoffRemoval
    (L : ℕ → ℕ → ℂ) (R z y : ℕ) : ℂ :=
  ∑ q ∈ Finset.Ioc z y,
    primeSievePNTDensity q *
      vfMidOddLiOwnerChildInterval L R q

/-- The odd-prefixed Li removal still telescopes exactly in cutoff. -/
theorem vfMidOddLiWeightedCutoffRemoval_eq_interval_sub
    {L : ℕ → ℕ → ℂ}
    (hL : IsAllScaleLiState L)
    (R z y : ℕ) (hz : 2 ≤ z) (hzy : z ≤ y) :
    vfMidOddLiWeightedCutoffRemoval L R z y =
      vfMidOddLiSquareInterval L R z -
        vfMidOddLiSquareInterval L R y := by
  induction y with
  | zero =>
      have : z = 0 := by omega
      omega
  | succ y ih =>
      by_cases h : z ≤ y
      · rw [vfMidOddLiWeightedCutoffRemoval,
          Finset.sum_Ioc_succ_top h]
        have hi := ih h
        rw [vfMidOddLiWeightedCutoffRemoval] at hi
        rw [hi]
        have hstep :=
          vfMidOddLiSquareInterval_cutoff_step
            hL R (y + 1) (by omega : 3 ≤ y + 1)
        simp only [Nat.add_sub_cancel] at hstep
        rw [hstep]
        ring
      · have heq : z = y + 1 := by omega
        subst z
        simp [vfMidOddLiWeightedCutoffRemoval]

def vfMidOddLiSquareDisplacementInterval
    (Actual L : ℕ → ℕ → ℂ) (R y : ℕ) : ℂ :=
  vfMidOddLiCumulativeDisplacement Actual L ((R + 1) ^ 2 - 1) y -
    vfMidOddLiCumulativeDisplacement Actual L (R ^ 2) y

theorem vfMidOddLiSquareDisplacementInterval_two_eq_zero
    {Actual L : ℕ → ℕ → ℂ}
    (hActual : IsAllScaleActualPrimeState Actual)
    (hL : IsAllScaleLiState L)
    (R : ℕ) :
    vfMidOddLiSquareDisplacementInterval Actual L R 2 = 0 := by
  unfold vfMidOddLiSquareDisplacementInterval
  rw [vfMidOddLiCumulativeDisplacement_two_eq_zero hActual hL,
    vfMidOddLiCumulativeDisplacement_two_eq_zero hActual hL]
  ring

/-- **Parity-aligned one-block transfer telescope.**
Because the transformed actual and odd-prefixed Li states agree at cutoff two,
the entire actual-minus-model owner correction over (2,R] is a single upper
displacement boundary. -/
theorem vfMidSquareBandLateOwnerCards_cast_eq_oddLiRemoval_sub_displacement
    {Actual L : ℕ → ℕ → ℂ}
    (hActual : IsAllScaleActualPrimeState Actual)
    (hL : IsAllScaleLiState L)
    {R : ℕ} (hR : 3 ≤ R) :
    ((∑ p ∈ vfMidSquareBandLateOwnerPrimes 2 R,
        (vfMidSquareBandCompositeOwner R p).card : ℕ) : ℂ) =
      vfMidOddLiWeightedCutoffRemoval L R 2 R -
        vfMidOddLiSquareDisplacementInterval Actual L R R := by
  rw [vfMidSquareBandLateOwnerCards_cast_eq_actualWeightedPhiRemoval
      hActual hR]
  have hActualTel :=
    vfMidPhiWeightedCutoffRemoval_eq_interval_sub
      (w := primeSievePrimeIndicator)
      (S := Actual) hActual R 2 R (by norm_num) (by omega)
  have hLiTel :=
    vfMidOddLiWeightedCutoffRemoval_eq_interval_sub
      hL R 2 R (by norm_num) (by omega)
  rw [hActualTel, hLiTel]
  have hzero :=
    vfMidOddLiSquareDisplacementInterval_two_eq_zero
      hActual hL R
  unfold vfMidOddLiSquareDisplacementInterval
    vfMidOddLiCumulativeDisplacement at hzero
  unfold vfMidPhiSquareInterval
    vfMidOddLiSquareInterval
    vfMidOddLiCumulativeDisplacement
  ring_nf at hzero ⊢
  exact hzero

/-! ## Dyadic parity-aligned transfer -/

def vfMidDyadicOddLiWeightedRemoval
    (L : ℕ → ℕ → ℂ) (A B : ℕ) : ℂ :=
  ∑ r ∈ Finset.Ico A B,
    vfMidOddLiWeightedCutoffRemoval L r 2 r

def vfMidDyadicOddLiDisplacementBoundary
    (Actual L : ℕ → ℕ → ℂ) (A B : ℕ) : ℂ :=
  ∑ r ∈ Finset.Ico A B,
    vfMidOddLiSquareDisplacementInterval Actual L r r

/-- The full physical chronological owner census on a dyadic range is the
odd-prefixed Li removal minus the sum of upper displacement boundaries. -/
theorem vfMidDyadicOwnerLateRemoval_cast_eq_oddLiRemoval_sub_displacement
    {Actual L : ℕ → ℕ → ℂ}
    (hActual : IsAllScaleActualPrimeState Actual)
    (hL : IsAllScaleLiState L)
    {A B : ℕ} (hA : 3 ≤ A) :
    ((vfMidDyadicOwnerLateRemoval 2 A B : ℝ) : ℂ) =
      vfMidDyadicOddLiWeightedRemoval L A B -
        vfMidDyadicOddLiDisplacementBoundary Actual L A B := by
  unfold vfMidDyadicOwnerLateRemoval
    vfMidDyadicOddLiWeightedRemoval
    vfMidDyadicOddLiDisplacementBoundary
  push_cast
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  have hr3 : 3 ≤ r :=
    hA.trans (Finset.mem_Ico.mp hr).1
  have hblock :=
    vfMidSquareBandLateOwnerCards_cast_eq_oddLiRemoval_sub_displacement
      hActual hL hr3
  push_cast at hblock
  exact hblock

/-- **Exact parity-aligned dyadic transfer identity.**
The target T-H is now split without the deterministic q=2 mismatch:
an odd-prefixed pure-Li reference correction minus only the upper
actual-minus-model displacement boundary sum. -/
theorem vfMidDyadicLateCorrection_cast_eq_oddLiCorrection_sub_displacement
    {Actual L : ℕ → ℕ → ℂ}
    (hActual : IsAllScaleActualPrimeState Actual)
    (hL : IsAllScaleLiState L)
    {A B : ℕ} (hA : 3 ≤ A) (hAB : A ≤ B) :
    ((vfMidDyadicLateRemoval 2 A B -
        vfMidDyadicLateReference 2 A B : ℝ) : ℂ) =
      (vfMidDyadicOddLiWeightedRemoval L A B -
        (vfMidDyadicLateReference 2 A B : ℂ)) -
      vfMidDyadicOddLiDisplacementBoundary Actual L A B := by
  have hT :=
    vfMidDyadicLateRemoval_eq_ownerCensus
      2 A B (by omega : 2 ≤ A) (by omega : 2 ≤ A) hAB
  have hOwner :=
    vfMidDyadicOwnerLateRemoval_cast_eq_oddLiRemoval_sub_displacement
      (A := A) (B := B) hActual hL hA
  rw [hT]
  push_cast
  rw [hOwner]
  ring

end RHLean.Analysis
