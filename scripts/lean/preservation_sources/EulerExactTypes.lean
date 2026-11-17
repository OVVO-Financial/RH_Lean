import «research.EULER_DOUBLE_CENTERED_REMAINDER_20261117»

/-! Independent public-type assertions for the complete original Euler source.
These statements retain the strict root cutoff, both row orientations, and
the actual Möbius coefficients.  No bound on Xi is supplied as an assumption.
-/

set_option autoImplicit false

open RHLean.Proof

example (R : ℕ) (hR : 2 ≤ R) :
    |eulerReciprocalHistoricalQ R| ≤ 1 :=
  eulerReciprocalHistoricalQ_abs_le_one R hR

example (R : ℕ) (hR : 2 ≤ R) :
    eulerFloorBilinearQ R =
      2 * ((R + 1 : ℕ) : ℚ) * eulerReciprocalHistoricalQ R -
        eulerDoubleCenterScaleQ R + eulerDoubleCenteredSourceQ R :=
  eulerFloorBilinearQ_eq_double_centered R hR

example (R a b : ℕ) :
    eulerDoubleCenteredKernelQ R a b =
      eulerDoubleCenteredDivisorKernelQ R a b +
        eulerDoubleCenteredInteriorKernelQ R a b :=
  eulerDoubleCenteredKernelQ_eq_parts R a b

example (R : ℕ) :
    eulerDoubleCenteredSourceQ R =
      eulerDoubleCenteredDivisorQ R + eulerDoubleCenteredXiQ R :=
  eulerDoubleCenteredSourceQ_eq_divisor_add_xi R

example (R a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hd : a ∣ R - 1 ∨ b ∣ R - 1) :
    eulerDoubleCenteredKernelQ R a b = -eulerFractionQ R a b :=
  eulerDoubleCenteredKernelQ_divisor R a b ha hb hd

example (R : ℕ) (hR : 2 ≤ R) :
    eulerFloorBilinearQ R =
      2 * ((R + 1 : ℕ) : ℚ) * eulerReciprocalHistoricalQ R -
        eulerDoubleCenterScaleQ R +
          eulerDoubleCenteredDivisorQ R + eulerDoubleCenteredXiQ R :=
  eulerFloorBilinearQ_eq_linear_add_divisor_add_xi R hR

example (R : ℕ) (hR : 2 ≤ R) :
    eulerSelfDualBilinear R =
      ((2 * ((R + 1 : ℕ) : ℚ) * eulerReciprocalHistoricalQ R -
        eulerDoubleCenterScaleQ R +
          eulerDoubleCenteredDivisorQ R + eulerDoubleCenteredXiQ R : ℚ) : ℂ) :=
  eulerSelfDualBilinear_eq_double_centered R hR

example (R a : ℕ) (ha : 0 < a) :
    0 ≤ eulerHistoricalFracQ R a ∧ eulerHistoricalFracQ R a < 1 :=
  eulerHistoricalFracQ_nonneg_lt_one R a ha

example (R : ℕ) (hR : 2 ≤ R) :
    0 ≤ eulerDoubleCenterScaleQ R ∧ eulerDoubleCenterScaleQ R ≤ 3 :=
  eulerDoubleCenterScaleQ_bounds R hR

example (R : ℕ) (hR : 2 ≤ R) :
    |2 * ((R + 1 : ℕ) : ℚ) * eulerReciprocalHistoricalQ R -
      eulerDoubleCenterScaleQ R| ≤ 2 * (R : ℚ) + 5 :=
  eulerDoubleCentered_linear_abs_le R hR

example (R : ℕ) (hR : 2 ≤ R) :
    |eulerDoubleCenteredDivisorQ R| ≤
      2 * ((R - 1 : ℕ) : ℚ) * ((R - 1).divisors.card : ℚ) :=
  eulerDoubleCenteredDivisorQ_abs_le R hR

example (R : ℕ) (hR : 2 ≤ R) :
    |eulerFloorBilinearQ R - eulerDoubleCenteredXiQ R| ≤
      2 * (R : ℚ) + 5 +
        2 * ((R - 1 : ℕ) : ℚ) * ((R - 1).divisors.card : ℚ) :=
  eulerDoubleCentered_remainder_le_divisors R hR

example (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℕ, 2 ≤ R →
      |(eulerFloorBilinearQ R : ℝ) - (eulerDoubleCenteredXiQ R : ℝ)| ≤
        C * (R : ℝ) ^ (1 + ε) :=
  eulerDoubleCentered_remainder_subpower ε hε

example (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℕ, 2 ≤ R →
      ‖eulerSelfDualBilinear R - (eulerDoubleCenteredXiQ R : ℂ)‖ ≤
        C * (R : ℝ) ^ (1 + ε) :=
  eulerSelfDual_doubleCentered_remainder_subpower ε hε

example (R : ℕ) (hR : 2 ≤ R) :
    |eulerDoubleCenteredDivisorQ R| ≤
      2 * ((R - 1 : ℕ) : ℚ) * (2 : ℚ) ^ (R - 1).primeFactors.card :=
  eulerDoubleCenteredDivisorQ_abs_le_primeFactors R hR

example (R : ℕ) (hR : 2 ≤ R) :
    |eulerFloorBilinearQ R - eulerDoubleCenteredXiQ R| ≤
      2 * (R : ℚ) + 5 +
        2 * ((R - 1 : ℕ) : ℚ) * (2 : ℚ) ^ (R - 1).primeFactors.card :=
  eulerDoubleCentered_remainder_le_primeFactors R hR

#print eulerReciprocalHistoricalQ_abs_le_one
#print eulerFloorBilinearQ_eq_double_centered
#print eulerDoubleCenteredKernelQ_eq_parts
#print eulerDoubleCenteredSourceQ_eq_divisor_add_xi
#print eulerDoubleCenteredKernelQ_divisor
#print eulerFloorBilinearQ_eq_linear_add_divisor_add_xi
#print eulerSelfDualBilinear_eq_double_centered
#print eulerHistoricalFracQ_nonneg_lt_one
#print eulerDoubleCenterScaleQ_bounds
#print eulerDoubleCentered_linear_abs_le
#print eulerDoubleCenteredDivisorQ_abs_le
#print eulerDoubleCentered_remainder_le_divisors
#print eulerDoubleCentered_remainder_subpower
#print eulerSelfDual_doubleCentered_remainder_subpower
#print eulerDoubleCenteredDivisorQ_abs_le_primeFactors
#print eulerDoubleCentered_remainder_le_primeFactors
