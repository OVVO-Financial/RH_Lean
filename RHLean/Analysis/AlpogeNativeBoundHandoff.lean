import RHLean.Analysis.AlpogeNativeSquareClockCriterion

/-!
# Exact source and bound handoff for the native Alpoge consumer

`statementOCSz` and `statementOCGz` reproduce the finite arithmetic
expressions in upstream `src/Formalism/StatementOC.lean` at snapshot
`7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`. They use RH_Lean's Mathlib
von Mangoldt function, include every prime power, and import no upstream
theorem. The source equalities below are exact finite algebra.

The quantitative propositions are explicit assumptions. In particular,
the fixed-coefficient small-epsilon window hypothesis implies the native
all-positive-exponent window hypothesis, with the constant chosen before
the requested window location. This normalizes the quantifiers and then
uses the existing native RH consumer. It does not construct a bound,
verify the upstream proof closure, or supply the open native estimate.
-/

noncomputable section

open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis.AlpogeNativeBoundHandoff

/-- The literal finite `Sz` expression in the pinned upstream statement. -/
def statementOCSz (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n * (x / (n : ℝ) - 1)

/-- The complete upstream arithmetic expression, with its Euler centering. -/
def statementOCGz (x : ℝ) : ℝ :=
  statementOCSz x - x * Real.log x + (1 + Real.eulerMascheroniConstant) * x

theorem statementOCSz_eq_nativePrincipalPrimeSum (x : ℝ) :
    statementOCSz x = alpogeNativePrincipalPrimeSum x := rfl

/-- Equality of the actual finite prime-power sources; no estimate is used. -/
theorem statementOCGz_eq_native (x : ℝ) :
    statementOCGz x = alpogeNativeGzArithmetic x := by
  unfold statementOCGz
  rw [statementOCSz_eq_nativePrincipalPrimeSum]
  exact (alpogeNativeGzArithmetic_eq_principal x).symm

theorem statementOCGz_natCast (N : ℕ) :
    statementOCGz (N : ℝ) = nativeAlpogeGz N :=
  (statementOCGz_eq_native (N : ℝ)).trans (alpogeNativeGzArithmetic_natCast N)

/-- Complete one-sided real windows, arbitrarily far out. The constant may
depend on the exponent, but is selected before the requested location. -/
def RealWindowBound (δ : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧
    ∀ y ∈ Set.Icc Y (Y ^ (1 + δ)),
      alpogeNativeGzArithmetic y ≤ C * y ^ (1 / 2 + η)

/-- The existing eventual root-coordinate hypothesis on the complete source. -/
def SquareClockBound : Prop :=
  ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 ≤ C ∧ ∃ R₀ : ℕ,
    ∀ R : ℕ, 2 ≤ R → R₀ ≤ R →
      nativeAlpogeGz (R ^ 2 - 1) ≤ C * (R : ℝ) ^ (1 + η)

/-- An eventual all-real bound is a stronger sufficient input than windows. -/
def EventualRealBound : Prop :=
  ∀ η : ℝ, 0 < η → ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    alpogeNativeGzArithmetic x ≤ C * x ^ (1 / 2 + η)

/-- The scalar window conclusion of the upstream form, stated on its literal
finite source. `K` and `ε₁` are fixed outside all epsilon and window choices.
The coefficient `C` may depend on epsilon, but never on `Y₀` or `Y`. -/
def SmallEpsilonWindowBound (K ε₁ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∃ C : ℝ, ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧
    ∀ y ∈ Set.Icc Y (Y ^ ((3 : ℝ) / 2)),
      statementOCGz y ≤ C * y ^ (1 / 2 + K * ε)

/-- Restrict the same eventual real bound to natural endpoints, retaining a
single constant and threshold for all endpoints at each chosen exponent. -/
theorem eventualNativeBound_of_eventualRealBound (h : EventualRealBound) :
    ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ,
      ∀ N : ℕ, N₀ ≤ N → 1 ≤ N →
        nativeAlpogeGz N ≤ C * (N : ℝ) ^ (1 / 2 + η) := by
  intro η hη
  obtain ⟨C, x₀, hx⟩ := h η hη
  refine ⟨|C|, abs_nonneg C, ⌈max x₀ 1⌉₊, ?_⟩
  intro N hN₀ _hN
  have hceil : (⌈max x₀ 1⌉₊ : ℝ) ≤ N := by exact_mod_cast hN₀
  have hxN : x₀ ≤ (N : ℝ) :=
    (le_max_left x₀ 1).trans ((Nat.le_ceil (max x₀ 1)).trans hceil)
  calc
    nativeAlpogeGz N = alpogeNativeGzArithmetic (N : ℝ) :=
      (alpogeNativeGzArithmetic_natCast N).symm
    _ ≤ C * (N : ℝ) ^ (1 / 2 + η) := hx N hxN
    _ ≤ |C| * (N : ℝ) ^ (1 / 2 + η) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (Nat.cast_nonneg N) _)

/-- Restrict an eventual bound to any requested complete multiplicative
window. The source bound remains an explicit premise. -/
theorem realWindowBound_of_eventualRealBound (δ : ℝ)
    (h : EventualRealBound) : RealWindowBound δ := by
  intro η hη
  obtain ⟨C, x₀, hx⟩ := h η hη
  refine ⟨C, fun Y₀ => ⟨max Y₀ x₀, le_max_left _ _, ?_⟩⟩
  intro y hy
  exact hx y ((le_max_right Y₀ x₀).trans hy.1)

/-- The fixed exponent coefficient costs only a choice of sufficiently small
epsilon. Windows are requested beyond `1`, so increasing the exponent is
valid. Replacing `C` by `|C|` does not change its uniformity in window location.
No sign assumption on `K` or `C` is needed. -/
theorem realWindowBound_of_smallEpsilonWindowBound {K ε₁ : ℝ}
    (hε₁ : 0 < ε₁) (h : SmallEpsilonWindowBound K ε₁) :
    RealWindowBound (1 / 2) := by
  intro η hη
  let ε := min (ε₁ / 2) (η / (|K| + 1))
  have hden : 0 < |K| + 1 := by positivity
  have hε : 0 < ε := lt_min (by linarith) (div_pos hη hden)
  have hεlt : ε < ε₁ :=
    lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hεle : ε ≤ η / (|K| + 1) := min_le_right _ _
  have hprod : ε * (|K| + 1) ≤ η := (le_div_iff₀ hden).mp hεle
  have hKε : K * ε ≤ η := by
    have hmul := mul_le_mul_of_nonneg_right (le_abs_self K) hε.le
    nlinarith
  obtain ⟨C, hC⟩ := h ε hε hεlt
  refine ⟨|C|, fun Y₀ => ?_⟩
  obtain ⟨Y, hY, hwindow⟩ := hC (max Y₀ 1)
  refine ⟨Y, (le_max_left Y₀ 1).trans hY, ?_⟩
  intro y hy
  have hy1 : 1 ≤ y := (le_max_right Y₀ 1).trans (hY.trans hy.1)
  have hexp : (1 : ℝ) + 1 / 2 = 3 / 2 := by norm_num
  rw [hexp] at hy
  calc
    alpogeNativeGzArithmetic y = statementOCGz y := (statementOCGz_eq_native y).symm
    _ ≤ C * y ^ (1 / 2 + K * ε) := hwindow y hy
    _ ≤ |C| * y ^ (1 / 2 + K * ε) :=
      mul_le_mul_of_nonneg_right (le_abs_self C)
        (Real.rpow_nonneg (by linarith : 0 ≤ y) _)
    _ ≤ |C| * y ^ (1 / 2 + η) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hy1 (by linarith)) (abs_nonneg C)

/-- Conditional RH consumer for the explicitly quantified complete windows. -/
theorem riemannHypothesis_of_realWindowBound {δ : ℝ} (hδ : 0 < δ)
    (h : RealWindowBound δ) : RiemannHypothesis :=
  riemannHypothesis_of_Gz_windows hδ h

/-- Conditional RH consumer for the existing native square-clock input. -/
theorem riemannHypothesis_of_squareClockBound (h : SquareClockBound) :
    RiemannHypothesis :=
  riemannHypothesis_of_eventual_squareClock_Gz_rpow h

/-- Conditional RH consumer for an eventual bound on all real arguments. -/
theorem riemannHypothesis_of_eventualRealBound (h : EventualRealBound) :
    RiemannHypothesis :=
  riemannHypothesis_of_realWindowBound (δ := 1) (by norm_num)
    (realWindowBound_of_eventualRealBound 1 h)

/-- Exact source transfer and exponent normalization suffice once the full
small-epsilon window bound has been supplied. That bound is assumed here. -/
theorem riemannHypothesis_of_smallEpsilonWindowBound {K ε₁ : ℝ}
    (hε₁ : 0 < ε₁) (h : SmallEpsilonWindowBound K ε₁) :
    RiemannHypothesis :=
  riemannHypothesis_of_realWindowBound (δ := 1 / 2) (by norm_num)
    (realWindowBound_of_smallEpsilonWindowBound hε₁ h)

end RHLean.Analysis.AlpogeNativeBoundHandoff
