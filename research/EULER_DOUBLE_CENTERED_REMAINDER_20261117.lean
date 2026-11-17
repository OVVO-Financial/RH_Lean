import «research.EULER_DOUBLE_CENTERED_SOURCE_20261117»
import RHLean.Proof.DeathShellSubpolynomial

/-!
# Uniform payment of the complete double-centering remainder

The union of both divisor-row orientations is retained once, and the
unconditional divisor-count estimate pays the whole removed source.
The explicit finite bound uses tau(R-1), a convenient upper bound on the
number of squarefree divisor rows.  No bound on Xi is assumed or proved.
-/

set_option autoImplicit false

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

theorem eulerDoubleCenterScaleQ_bounds (R : ℕ) (hR : 2 ≤ R) :
    0 ≤ eulerDoubleCenterScaleQ R ∧ eulerDoubleCenterScaleQ R ≤ 3 := by
  have hN : (0 : ℚ) < ((R - 1 : ℕ) : ℚ) := by
    exact_mod_cast (show 0 < R - 1 by omega)
  unfold eulerDoubleCenterScaleQ
  constructor
  · positivity
  · apply (div_le_iff₀ hN).mpr
    exact_mod_cast (show R + 1 ≤ 3 * (R - 1) by omega)

theorem eulerDoubleCentered_linear_abs_le (R : ℕ) (hR : 2 ≤ R) :
    |2 * ((R + 1 : ℕ) : ℚ) * eulerReciprocalHistoricalQ R -
      eulerDoubleCenterScaleQ R| ≤ 2 * (R : ℚ) + 5 := by
  obtain ⟨ht0, ht3⟩ := eulerDoubleCenterScaleQ_bounds R hR
  have hm := eulerReciprocalHistoricalQ_abs_le_one R hR
  have hP : ((R + 1 : ℕ) : ℚ) = (R : ℚ) + 1 := by norm_num
  have hmul := mul_le_mul_of_nonneg_left hm
    (by positivity : (0 : ℚ) ≤ 2 * ((R + 1 : ℕ) : ℚ))
  calc
    |2 * ((R + 1 : ℕ) : ℚ) * eulerReciprocalHistoricalQ R -
        eulerDoubleCenterScaleQ R| ≤
        |2 * ((R + 1 : ℕ) : ℚ) * eulerReciprocalHistoricalQ R| +
          |eulerDoubleCenterScaleQ R| := abs_sub_le _ _
    _ = 2 * ((R + 1 : ℕ) : ℚ) * |eulerReciprocalHistoricalQ R| +
        eulerDoubleCenterScaleQ R := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℚ) ≤ 2 * ((R + 1 : ℕ) : ℚ)),
        abs_of_nonneg ht0]
    _ ≤ 2 * (R : ℚ) + 5 := by
      rw [hP]
      rw [hP] at hmul
      nlinarith [hmul, abs_nonneg (eulerReciprocalHistoricalQ R),
        (show (0 : ℚ) ≤ (R : ℚ) from Nat.cast_nonneg R)]

private theorem doubleCenteredDivisor_term_bound (R a b : ℕ)
    (ha : 0 < a) (hb : 0 < b) :
    |eulerMuQ b * (eulerMuQ a * eulerDoubleCenteredDivisorKernelQ R a b)| ≤
      (if a ∣ R - 1 then (1 : ℚ) else 0) +
        (if b ∣ R - 1 then (1 : ℚ) else 0) := by
  by_cases hd : a ∣ R - 1 ∨ b ∣ R - 1
  · rw [eulerDoubleCenteredDivisorKernelQ, if_pos hd,
      eulerDoubleCenteredKernelQ_divisor R a b ha hb hd]
    obtain ⟨hv0, hv1⟩ := eulerFractionQ_nonneg_lt_one (R := R) ha hb
    rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hv0]
    have hinner : |eulerMuQ a| * eulerFractionQ R a b ≤ 1 := by
      calc
        |eulerMuQ a| * eulerFractionQ R a b ≤
            1 * eulerFractionQ R a b :=
          mul_le_mul_of_nonneg_right (eulerMuQ_abs_le_one a) hv0
        _ ≤ 1 := by simpa using hv1.le
    have houter : |eulerMuQ b| * (|eulerMuQ a| * eulerFractionQ R a b) ≤ 1 := by
      calc
        |eulerMuQ b| * (|eulerMuQ a| * eulerFractionQ R a b) ≤
            1 * (|eulerMuQ a| * eulerFractionQ R a b) :=
          mul_le_mul_of_nonneg_right (eulerMuQ_abs_le_one b)
            (mul_nonneg (abs_nonneg _) hv0)
        _ ≤ 1 := by simpa using hinner
    apply houter.trans
    rcases hd with hd | hd
    · simp only [if_pos hd]
      split_ifs <;> norm_num
    · simp only [if_pos hd]
      split_ifs <;> norm_num
  · simp [eulerDoubleCenteredDivisorKernelQ, hd, not_or.mp hd]

private theorem divisorIndicator_sum (R : ℕ) (hR : 2 ≤ R) :
    (∑ a ∈ Finset.Icc 1 (R - 1), if a ∣ R - 1 then (1 : ℚ) else 0) =
      ((R - 1).divisors.card : ℚ) := by
  classical
  have hN0 : R - 1 ≠ 0 := by omega
  have hset : (Finset.Icc 1 (R - 1)).filter (fun a => a ∣ R - 1) =
      (R - 1).divisors := by
    ext a
    constructor
    · intro ha
      exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp ha).2, hN0⟩
    · intro ha
      have had := Nat.dvd_of_mem_divisors ha
      have hap := Nat.pos_of_mem_divisors ha
      have hal := Nat.le_of_dvd (by omega : 0 < R - 1) had
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hap, hal⟩, had⟩
  rw [← Finset.sum_filter, hset]
  simp

/-- Complete two-orientation divisor union, with a fully explicit finite bound. -/
theorem eulerDoubleCenteredDivisorQ_abs_le (R : ℕ) (hR : 2 ≤ R) :
    |eulerDoubleCenteredDivisorQ R| ≤
      2 * ((R - 1 : ℕ) : ℚ) * ((R - 1).divisors.card : ℚ) := by
  classical
  let S := Finset.Icc 1 (R - 1)
  let i := fun a => if a ∣ R - 1 then (1 : ℚ) else 0
  have hc : (∑ a ∈ S, i a) = ((R - 1).divisors.card : ℚ) :=
    divisorIndicator_sum R hR
  have hinner (b : ℕ) : (∑ a ∈ S, (i a + i b)) =
      ((R - 1).divisors.card : ℚ) + ((R - 1 : ℕ) : ℚ) * i b := by
    rw [Finset.sum_add_distrib, hc]
    simp [S, Nat.card_Icc]
  unfold eulerDoubleCenteredDivisorQ
  simp_rw [Finset.mul_sum]
  change |∑ b ∈ S, ∑ a ∈ S,
    eulerMuQ b * (eulerMuQ a * eulerDoubleCenteredDivisorKernelQ R a b)| ≤ _
  calc
    |∑ b ∈ S, ∑ a ∈ S,
        eulerMuQ b * (eulerMuQ a * eulerDoubleCenteredDivisorKernelQ R a b)| ≤
        ∑ b ∈ S, |∑ a ∈ S,
          eulerMuQ b * (eulerMuQ a * eulerDoubleCenteredDivisorKernelQ R a b)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b ∈ S, ∑ a ∈ S,
        |eulerMuQ b * (eulerMuQ a * eulerDoubleCenteredDivisorKernelQ R a b)| := by
      apply Finset.sum_le_sum
      intro b _hb
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b ∈ S, ∑ a ∈ S, (i a + i b) := by
      apply Finset.sum_le_sum
      intro b hb
      apply Finset.sum_le_sum
      intro a ha
      exact doubleCenteredDivisor_term_bound R a b
        (Finset.mem_Icc.mp ha).1 (Finset.mem_Icc.mp hb).1
    _ = 2 * ((R - 1 : ℕ) : ℚ) * ((R - 1).divisors.card : ℚ) := by
      simp_rw [hinner]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hc]
      simp [S, Nat.card_Icc]
      <;> ring

/-- Every removed term is included in the explicit original-source error. -/
theorem eulerDoubleCentered_remainder_le_divisors (R : ℕ) (hR : 2 ≤ R) :
    |eulerFloorBilinearQ R - eulerDoubleCenteredXiQ R| ≤
      2 * (R : ℚ) + 5 +
        2 * ((R - 1 : ℕ) : ℚ) * ((R - 1).divisors.card : ℚ) := by
  have he : eulerFloorBilinearQ R - eulerDoubleCenteredXiQ R =
      (2 * ((R + 1 : ℕ) : ℚ) * eulerReciprocalHistoricalQ R -
        eulerDoubleCenterScaleQ R) + eulerDoubleCenteredDivisorQ R := by
    rw [eulerFloorBilinearQ_eq_linear_add_divisor_add_xi R hR]
    ring
  rw [he]
  exact (abs_add _ _).trans (add_le_add (eulerDoubleCentered_linear_abs_le R hR)
    (eulerDoubleCenteredDivisorQ_abs_le R hR))

/-- Root times every positive power, with the constant chosen before R. -/
theorem eulerDoubleCentered_remainder_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℕ, 2 ≤ R →
      |(eulerFloorBilinearQ R : ℝ) - (eulerDoubleCenteredXiQ R : ℝ)| ≤
        C * (R : ℝ) ^ (1 + ε) := by
  obtain ⟨D, hD, hdiv⟩ := card_divisors_le_subpolynomial hε
  refine ⟨7 + 2 * D, by positivity, ?_⟩
  intro R hR
  have hR0 : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by omega)
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast (show 1 ≤ R by omega)
  have hN0 : (0 : ℝ) ≤ ((R - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hNR : ((R - 1 : ℕ) : ℝ) ≤ (R : ℝ) := by exact_mod_cast Nat.sub_le R 1
  have hp1 : (1 : ℝ) ≤ (R : ℝ) ^ ε := Real.one_le_rpow hR1 hε.le
  have hdivR : ((R - 1).divisors.card : ℝ) ≤ D * (R : ℝ) ^ ε := by
    exact (hdiv (R - 1) (by omega)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hN0 hNR hε.le) hD)
  have hfinite :
      |(eulerFloorBilinearQ R : ℝ) - (eulerDoubleCenteredXiQ R : ℝ)| ≤
        2 * (R : ℝ) + 5 +
          2 * ((R - 1 : ℕ) : ℝ) * ((R - 1).divisors.card : ℝ) := by
    exact_mod_cast eulerDoubleCentered_remainder_le_divisors R hR
  have hlinear : 2 * (R : ℝ) + 5 ≤ 7 * (R : ℝ) * (R : ℝ) ^ ε := by
    calc
      2 * (R : ℝ) + 5 ≤ 7 * (R : ℝ) := by linarith
      _ ≤ 7 * (R : ℝ) * (R : ℝ) ^ ε := by nlinarith
  have hrows : 2 * ((R - 1 : ℕ) : ℝ) * ((R - 1).divisors.card : ℝ) ≤
      2 * (R : ℝ) * (D * (R : ℝ) ^ ε) := by
    apply mul_le_mul
    · linarith
    · exact hdivR
    · exact Nat.cast_nonneg _
    · positivity
  calc
    |(eulerFloorBilinearQ R : ℝ) - (eulerDoubleCenteredXiQ R : ℝ)| ≤
        2 * (R : ℝ) + 5 +
          2 * ((R - 1 : ℕ) : ℝ) * ((R - 1).divisors.card : ℝ) := hfinite
    _ ≤ 7 * (R : ℝ) * (R : ℝ) ^ ε +
        2 * (R : ℝ) * (D * (R : ℝ) ^ ε) := add_le_add hlinear hrows
    _ = (7 + 2 * D) * (R : ℝ) ^ (1 + ε) := by
      rw [Real.rpow_add hR0, Real.rpow_one]
      ring

/-- The same subpower error on the original complex frozen-floor carrier. -/
theorem eulerSelfDual_doubleCentered_remainder_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℕ, 2 ≤ R →
      ‖eulerSelfDualBilinear R - (eulerDoubleCenteredXiQ R : ℂ)‖ ≤
        C * (R : ℝ) ^ (1 + ε) := by
  obtain ⟨C, hC, hbound⟩ := eulerDoubleCentered_remainder_subpower ε hε
  refine ⟨C, hC, ?_⟩
  intro R hR
  rw [← eulerFloorBilinearQ_cast_eq_original R]
  have he : (eulerFloorBilinearQ R : ℂ) - (eulerDoubleCenteredXiQ R : ℂ) =
      (((eulerFloorBilinearQ R : ℝ) - (eulerDoubleCenteredXiQ R : ℝ) : ℝ) : ℂ) := by
    norm_cast
  rw [he, Complex.norm_real, Real.norm_eq_abs]
  exact hbound R hR

end RHLean.Proof
