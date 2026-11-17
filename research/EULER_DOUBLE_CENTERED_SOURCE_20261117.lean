import «research.EULER_RANK_ONE_FRACTIONAL_ROWS_20261027»

/-!
# Symmetric centering of the complete original frozen Euler source

Both historical fractional coordinates are retained.  The lower-prefix
Möbius inversion removes the full continuous rank-one term before any norm
is taken.  The divisor-row union and its exact complement partition the
original ordered square; neither mixed orientation is discarded.

This module proves identities and a root-sized linear bound.  It asserts
no estimate on the complete non-divisor remainder and no RH consequence.
-/

set_option autoImplicit false

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis

/-- Exact rational scale at the strict historical cutoff. -/
def eulerDoubleCenterScaleQ (R : ℕ) : ℚ :=
  ((R + 1 : ℕ) : ℚ) / ((R - 1 : ℕ) : ℚ)

/-- Both historical fractional coordinates and the original joint fraction. -/
def eulerDoubleCenteredKernelQ (R a b : ℕ) : ℚ :=
  eulerDoubleCenterScaleQ R * eulerHistoricalFracQ R a *
    eulerHistoricalFracQ R b - eulerFractionQ R a b

def eulerDoubleCenteredSourceQ (R : ℕ) : ℚ :=
  ∑ b ∈ Finset.Icc 1 (R - 1), eulerMuQ b *
    ∑ a ∈ Finset.Icc 1 (R - 1), eulerMuQ a * eulerDoubleCenteredKernelQ R a b

/-- The union, counted once, of BOTH divisor-row orientations. -/
def eulerDoubleCenteredDivisorKernelQ (R a b : ℕ) : ℚ :=
  if a ∣ R - 1 ∨ b ∣ R - 1 then eulerDoubleCenteredKernelQ R a b else 0

/-- The literal complementary kernel, retaining the same Möbius coefficients. -/
def eulerDoubleCenteredInteriorKernelQ (R a b : ℕ) : ℚ :=
  if a ∣ R - 1 ∨ b ∣ R - 1 then 0 else eulerDoubleCenteredKernelQ R a b

def eulerDoubleCenteredDivisorQ (R : ℕ) : ℚ :=
  ∑ b ∈ Finset.Icc 1 (R - 1), eulerMuQ b *
    ∑ a ∈ Finset.Icc 1 (R - 1), eulerMuQ a *
      eulerDoubleCenteredDivisorKernelQ R a b

/-- The doubly non-divisor residual Xi on the complete original ordered carrier. -/
def eulerDoubleCenteredXiQ (R : ℕ) : ℚ :=
  ∑ b ∈ Finset.Icc 1 (R - 1), eulerMuQ b *
    ∑ a ∈ Finset.Icc 1 (R - 1), eulerMuQ a *
      eulerDoubleCenteredInteriorKernelQ R a b

theorem eulerMuQ_abs_le_one (a : ℕ) : |eulerMuQ a| ≤ 1 := by
  rcases ArithmeticFunction.moebius_eq_or a with h | h | h <;>
    simp [eulerMuQ, h]

theorem eulerHistoricalFracQ_eq_mod_div (R a : ℕ) (ha : 0 < a) :
    eulerHistoricalFracQ R a = ((R - 1) % a : ℕ) / (a : ℚ) := by
  have ha0 : (a : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ha)
  have he : (((R - 1) % a : ℕ) : ℚ) +
      (a : ℚ) * (((R - 1) / a : ℕ) : ℚ) = ((R - 1 : ℕ) : ℚ) := by
    exact_mod_cast Nat.mod_add_div (R - 1) a
  unfold eulerHistoricalFracQ
  field_simp [ha0]
  linarith

theorem eulerHistoricalFracQ_nonneg_lt_one (R a : ℕ) (ha : 0 < a) :
    0 ≤ eulerHistoricalFracQ R a ∧ eulerHistoricalFracQ R a < 1 := by
  rw [eulerHistoricalFracQ_eq_mod_div R a ha]
  have haQ : (0 : ℚ) < a := by exact_mod_cast ha
  constructor
  · positivity
  · apply (div_lt_iff₀ haQ).2
    exact_mod_cast (Nat.mod_lt (R - 1) ha)

theorem eulerHistoricalFracQ_zero_of_dvd (R a : ℕ) (ha : 0 < a)
    (hd : a ∣ R - 1) : eulerHistoricalFracQ R a = 0 := by
  rw [eulerHistoricalFracQ_eq_mod_div R a ha, Nat.mod_eq_zero_of_dvd hd]
  simp

/-- Complete historical fractional mass, using genuine finite Möbius inversion. -/
theorem eulerHistoricalFracQ_signed_sum (R : ℕ) (hR : 2 ≤ R) :
    (∑ a ∈ Finset.Icc 1 (R - 1), eulerMuQ a * eulerHistoricalFracQ R a) =
      ((R - 1 : ℕ) : ℚ) * eulerReciprocalHistoricalQ R - 1 := by
  have hlinear :
      (∑ a ∈ Finset.Icc 1 (R - 1),
        eulerMuQ a * (((R - 1 : ℕ) : ℚ) / (a : ℚ))) =
      ((R - 1 : ℕ) : ℚ) * eulerReciprocalHistoricalQ R := by
    unfold eulerReciprocalHistoricalQ
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _ha
    ring
  unfold eulerHistoricalFracQ
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [hlinear, eulerHistoricalFloorInversionQ R hR]

/-- The historical reciprocal Möbius prefix has an absolute bound of one. -/
theorem eulerReciprocalHistoricalQ_abs_le_one (R : ℕ) (hR : 2 ≤ R) :
    |eulerReciprocalHistoricalQ R| ≤ 1 := by
  classical
  let S := Finset.Icc 1 (R - 1)
  let f := fun a => eulerMuQ a * eulerHistoricalFracQ R a
  have hmem : 1 ∈ S := by simp only [S, Finset.mem_Icc]; omega
  have hf1 : f 1 = 0 := by
    dsimp [f]
    rw [eulerHistoricalFracQ_zero_of_dvd R 1 (by omega) (one_dvd _), mul_zero]
  have hsum : (∑ a ∈ S, f a) = ∑ a ∈ S.erase 1, f a := by
    simpa only [hf1, add_zero] using (Finset.sum_erase_add S f hmem).symm
  have hcard : (S.erase 1).card = R - 1 - 1 := by
    rw [Finset.card_erase_of_mem hmem]
    simp [S, Nat.card_Icc]
  have hbound : |∑ a ∈ S, f a| ≤ ((R - 1 - 1 : ℕ) : ℚ) := by
    rw [hsum]
    calc
      |∑ a ∈ S.erase 1, f a| ≤ ∑ a ∈ S.erase 1, |f a| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a ∈ S.erase 1, (1 : ℚ) := by
        apply Finset.sum_le_sum
        intro a ha
        have haS := (Finset.mem_erase.mp ha).2
        have ha0 : 0 < a := (Finset.mem_Icc.mp haS).1
        obtain ⟨hu0, hu1⟩ := eulerHistoricalFracQ_nonneg_lt_one R a ha0
        dsimp [f]
        rw [abs_mul, abs_of_nonneg hu0]
        exact (mul_le_mul_of_nonneg_right (eulerMuQ_abs_le_one a) hu0).trans
          (by simpa using hu1.le)
      _ = ((R - 1 - 1 : ℕ) : ℚ) := by simp [hcard]
  have hmass := eulerHistoricalFracQ_signed_sum R hR
  change (∑ a ∈ S, f a) = _ at hmass
  have hNpos : (0 : ℚ) < ((R - 1 : ℕ) : ℚ) := by
    exact_mod_cast (show 0 < R - 1 by omega)
  have hpred : ((R - 1 - 1 : ℕ) : ℚ) = ((R - 1 : ℕ) : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ R - 1)]
    norm_num
  rw [hmass, hpred] at hbound
  obtain ⟨hl, hu⟩ := abs_le.mp hbound
  apply abs_le.mpr
  constructor
  · apply (mul_le_mul_left hNpos).mp
    nlinarith
  · apply (mul_le_mul_left hNpos).mp
    nlinarith

private theorem eulerDoubleCenteredSourceQ_eq_square_sub (R : ℕ) :
    eulerDoubleCenteredSourceQ R =
      eulerDoubleCenterScaleQ R *
        (∑ a ∈ Finset.Icc 1 (R - 1), eulerMuQ a * eulerHistoricalFracQ R a) ^ 2 -
      eulerFractionBilinearQ R := by
  let S := Finset.Icc 1 (R - 1)
  have hsep :
      (∑ b ∈ S, eulerMuQ b * ∑ a ∈ S, eulerMuQ a *
        (eulerDoubleCenterScaleQ R * eulerHistoricalFracQ R a *
          eulerHistoricalFracQ R b)) =
      eulerDoubleCenterScaleQ R *
        (∑ a ∈ S, eulerMuQ a * eulerHistoricalFracQ R a) ^ 2 := by
    simp_rw [pow_two, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b _hb
    apply Finset.sum_congr rfl
    intro a _ha
    ring
  unfold eulerDoubleCenteredSourceQ eulerDoubleCenteredKernelQ
  simp_rw [mul_sub, Finset.sum_sub_distrib, mul_sub, Finset.sum_sub_distrib]
  change
    (∑ b ∈ S, eulerMuQ b * ∑ a ∈ S, eulerMuQ a *
      (eulerDoubleCenterScaleQ R * eulerHistoricalFracQ R a *
        eulerHistoricalFracQ R b)) - eulerFractionBilinearQ R = _
  rw [hsep]

/-- Symmetric subtraction removes the whole coherent rank-one contribution. -/
theorem eulerFloorBilinearQ_eq_double_centered (R : ℕ) (hR : 2 ≤ R) :
    eulerFloorBilinearQ R =
      2 * ((R + 1 : ℕ) : ℚ) * eulerReciprocalHistoricalQ R -
        eulerDoubleCenterScaleQ R + eulerDoubleCenteredSourceQ R := by
  have hsource := eulerFloorBilinearQ_eq_continuous_sub_fractional R
  rw [eulerContinuousBilinearQ_eq_reciprocal_square] at hsource
  have hfrac : eulerFractionBilinearQ R =
      (squareRootEndpoint R : ℚ) * eulerReciprocalHistoricalQ R ^ 2 -
        eulerFloorBilinearQ R := by linarith
  rw [eulerDoubleCenteredSourceQ_eq_square_sub,
    eulerHistoricalFracQ_signed_sum R hR, hfrac]
  rw [eulerRootEndpoint_factor R hR]
  simp only [Nat.cast_mul]
  have hN0 : ((R - 1 : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (show R - 1 ≠ 0 by omega)
  unfold eulerDoubleCenterScaleQ
  field_simp [hN0] <;> ring

theorem eulerDoubleCenteredKernelQ_eq_parts (R a b : ℕ) :
    eulerDoubleCenteredKernelQ R a b =
      eulerDoubleCenteredDivisorKernelQ R a b +
        eulerDoubleCenteredInteriorKernelQ R a b := by
  unfold eulerDoubleCenteredDivisorKernelQ eulerDoubleCenteredInteriorKernelQ
  split_ifs <;> ring

theorem eulerDoubleCenteredSourceQ_eq_divisor_add_xi (R : ℕ) :
    eulerDoubleCenteredSourceQ R =
      eulerDoubleCenteredDivisorQ R + eulerDoubleCenteredXiQ R := by
  unfold eulerDoubleCenteredSourceQ eulerDoubleCenteredDivisorQ eulerDoubleCenteredXiQ
  simp_rw [eulerDoubleCenteredKernelQ_eq_parts, mul_add, Finset.sum_add_distrib]

theorem eulerDoubleCenteredKernelQ_divisor (R a b : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hd : a ∣ R - 1 ∨ b ∣ R - 1) :
    eulerDoubleCenteredKernelQ R a b = -eulerFractionQ R a b := by
  rcases hd with hd | hd
  · simp [eulerDoubleCenteredKernelQ, eulerHistoricalFracQ_zero_of_dvd R a ha hd]
  · simp [eulerDoubleCenteredKernelQ, eulerHistoricalFracQ_zero_of_dvd R b hb hd]

/-- Complete source return with every discarded row still explicitly present. -/
theorem eulerFloorBilinearQ_eq_linear_add_divisor_add_xi (R : ℕ) (hR : 2 ≤ R) :
    eulerFloorBilinearQ R =
      2 * ((R + 1 : ℕ) : ℚ) * eulerReciprocalHistoricalQ R -
        eulerDoubleCenterScaleQ R +
          eulerDoubleCenteredDivisorQ R + eulerDoubleCenteredXiQ R := by
  rw [eulerFloorBilinearQ_eq_double_centered R hR,
    eulerDoubleCenteredSourceQ_eq_divisor_add_xi]
  ring

/-- The returned rational expression is the original complex frozen-floor source. -/
theorem eulerSelfDualBilinear_eq_double_centered (R : ℕ) (hR : 2 ≤ R) :
    eulerSelfDualBilinear R =
      ((2 * ((R + 1 : ℕ) : ℚ) * eulerReciprocalHistoricalQ R -
        eulerDoubleCenterScaleQ R +
          eulerDoubleCenteredDivisorQ R + eulerDoubleCenteredXiQ R : ℚ) : ℂ) := by
  rw [← eulerFloorBilinearQ_cast_eq_original R,
    eulerFloorBilinearQ_eq_linear_add_divisor_add_xi R hR]

end RHLean.Proof
