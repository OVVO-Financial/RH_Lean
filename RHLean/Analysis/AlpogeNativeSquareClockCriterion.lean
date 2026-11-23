import RHLean.Analysis.AlpogeNativeWindowLandau
import RHLean.Analysis.AlpogeSignedSquareInterpolation

/-!
# The native R-coordinate upper bound is a sufficient RH input

The existing native window theorem uses the endpoint `X_R = R² - 1`.
This file makes the elementary exponent conversion explicit and consumes an
eventual one-sided `R^(1+η)` bound, for every positive `η`, directly in that
theorem. Neither an absolute bound nor an ordinary-prime sign condition is
required. The quantitative bound is an explicit hypothesis, not proved here.
-/

noncomputable section

namespace RHLean.Analysis

/-- The natural root power is controlled by the corresponding endpoint power.
The factor depends on the exponent only, never on the radius. -/
theorem nativeSquareClock_rpow_le_endpoint (R : ℕ) (hR : 2 ≤ R)
    (η : ℝ) (hη : 0 ≤ η) :
    (R : ℝ) ^ (1 + 2 * η) ≤
      (2 : ℝ) ^ (1 / 2 + η) * ((R ^ 2 - 1 : ℕ) : ℝ) ^ (1 / 2 + η) := by
  have hRreal : (2 : ℝ) ≤ R := by exact_mod_cast hR
  have hsquare : 1 ≤ R ^ 2 := by nlinarith
  have hcast : ((R ^ 2 - 1 : ℕ) : ℝ) = (R : ℝ) ^ 2 - 1 := by
    rw [Nat.cast_sub hsquare, Nat.cast_pow, Nat.cast_one]
  have hbase : (R : ℝ) ^ 2 ≤ 2 * ((R ^ 2 - 1 : ℕ) : ℝ) := by
    rw [hcast]
    nlinarith
  calc
    (R : ℝ) ^ (1 + 2 * η) = ((R : ℝ) ^ 2) ^ (1 / 2 + η) := by
      rw [← Real.rpow_natCast_mul (Nat.cast_nonneg R)]
      congr 1
      norm_num
      ring
    _ ≤ (2 * ((R ^ 2 - 1 : ℕ) : ℝ)) ^ (1 / 2 + η) :=
      Real.rpow_le_rpow (sq_nonneg _) hbase (by linarith)
    _ = (2 : ℝ) ^ (1 / 2 + η) * ((R ^ 2 - 1 : ℕ) : ℝ) ^ (1 / 2 + η) :=
      Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)

/-- The native all-scale root-coordinate target is sufficient. The constant
and eventual threshold may depend on `η`; they are uniform in `R`.

This consumes the existing one-sided square-clock/window/Landau chain.
The complete signed-source estimate in `h` remains the open arithmetic input. -/
theorem riemannHypothesis_of_eventual_squareClock_Gz_rpow
    (h : ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 ≤ C ∧ ∃ R₀ : ℕ,
      ∀ R : ℕ, 2 ≤ R → R₀ ≤ R →
        nativeAlpogeGz (R ^ 2 - 1) ≤ C * (R : ℝ) ^ (1 + η)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_squareClock_Gz_windows (δ := 1) (by norm_num)
  intro η hη
  obtain ⟨C, hC, R₀, hbound⟩ := h (2 * η) (by linarith)
  refine ⟨C * (2 : ℝ) ^ (1 / 2 + η), fun A₀ => ?_⟩
  let A := max A₀ (max 2 R₀)
  refine ⟨A, le_max_left _ _, fun R hAR _hwindow => ?_⟩
  have hR : 2 ≤ R :=
    (le_max_left 2 R₀).trans ((le_max_right A₀ (max 2 R₀)).trans hAR)
  have hR₀ : R₀ ≤ R :=
    (le_max_right 2 R₀).trans ((le_max_right A₀ (max 2 R₀)).trans hAR)
  calc
    nativeAlpogeGz (R ^ 2 - 1) ≤ C * (R : ℝ) ^ (1 + 2 * η) :=
      hbound R hR hR₀
    _ ≤ C * ((2 : ℝ) ^ (1 / 2 + η) *
        ((R ^ 2 - 1 : ℕ) : ℝ) ^ (1 / 2 + η)) :=
      mul_le_mul_of_nonneg_left (nativeSquareClock_rpow_le_endpoint R hR η hη.le) hC
    _ = (C * (2 : ℝ) ^ (1 / 2 + η)) *
        ((R ^ 2 - 1 : ℕ) : ℝ) ^ (1 / 2 + η) := by ring

/-- A fixed eventual one-sided linear bound on the same native square clock
is a stronger sufficient input. No lower bound on `Gz` is needed. -/
theorem riemannHypothesis_of_eventual_squareClock_Gz_linear
    (C : ℝ) (hC : 0 ≤ C) (R₀ : ℕ)
    (h : ∀ R : ℕ, 2 ≤ R → R₀ ≤ R →
      nativeAlpogeGz (R ^ 2 - 1) ≤ C * (R : ℝ)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_eventual_squareClock_Gz_rpow
  intro η hη
  refine ⟨C, hC, R₀, fun R hR hR₀ => ?_⟩
  apply (h R hR hR₀).trans
  apply mul_le_mul_of_nonneg_left _ hC
  exact Real.self_le_rpow_of_one_le
    (by exact_mod_cast (show 1 ≤ R by omega)) (by linarith)

/-- The stronger absolute square-lattice bound also reaches RH through the
existing signed interpolation theorem and the native one-sided root consumer.
The different endpoints `R²` and `R²-1` are connected explicitly. -/
theorem riemannHypothesis_of_square_lattice_Gz_critical
    (C : ℝ) (hC : 0 ≤ C)
    (hSquare : ∀ R : ℕ, 2 ≤ R →
      |nativeAlpogeGz (R ^ 2)| ≤ C * (R : ℝ)) :
    RiemannHypothesis := by
  let K := 2 * C + 3 * alpogeGzInterpolationSlope
  have hK : 0 ≤ K := by
    dsimp [K]
    linarith [alpogeGzInterpolationSlope_nonneg]
  apply riemannHypothesis_of_eventual_squareClock_Gz_linear K hK 3
  intro R _hR hR₀
  have hsq : 5 ≤ R ^ 2 := by nlinarith
  have hN : 4 ≤ R ^ 2 - 1 := by omega
  have hbound := nativeAlpogeGz_all_of_square_lattice_critical
    C hC hSquare (R ^ 2 - 1) hN
  have hsqrt : Real.sqrt ((R ^ 2 - 1 : ℕ) : ℝ) ≤ (R : ℝ) := by
    have hle : ((R ^ 2 - 1 : ℕ) : ℝ) ≤ (R : ℝ) ^ 2 := by
      exact_mod_cast (Nat.sub_le (R ^ 2) 1)
    have heq := Real.sq_sqrt (Nat.cast_nonneg (R ^ 2 - 1))
    nlinarith [Real.sqrt_nonneg ((R ^ 2 - 1 : ℕ) : ℝ), Nat.cast_nonneg (α := ℝ) R]
  exact (le_abs_self _).trans (hbound.trans (mul_le_mul_of_nonneg_left hsqrt hK))

end RHLean.Analysis
