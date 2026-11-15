import «research.UNIVERSAL_ENVELOPE_ZERO_LOG»
import «research.UNIVERSAL_ENVELOPE_OWNER_EQUIVALENCE»
import RHLean.Analysis.MertensEnergyRHForward

/-!
# Exact bridges to the repository energy criterion and Mathlib RH

These bridges make the terminal proposition explicit.  The open-strip zero
formulation is connected to Mathlib's full RiemannHypothesis through the
existing unconditional Mertens-energy consumer.  Both directions preserve
the every-positive-loss quantifiers and handle the integer zero endpoint.
-/

noncomputable section

namespace RHLean.Analysis.UniversalEnvelope

open RHLean.Proof RHLean.Analysis.MertensExponent

theorem mertensEnergy_of_mertens_half
    (hhalf : MertensGrowthAtMost (1 / 2 : ℝ)) : MertensEnergyBoundedStatement := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := hhalf (ε / 2) (by linarith)
  refine ⟨C ^ 2, sq_nonneg C, ?_⟩
  intro n
  by_cases hn : n = 0
  · subst n
    simpa using sq_nonneg C
  · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hs := (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg hC (Real.rpow_nonneg hn0.le _))).mpr (hbound n (by omega))
    have hp : ((n : ℝ) ^ ((1 / 2 : ℝ) + ε / 2)) ^ (2 : ℕ) =
        (n : ℝ) ^ (1 + ε) := by
      rw [← Real.rpow_mul_natCast hn0.le]
      congr 1
      ring
    calc
      ‖mertensSummatory n‖ ^ 2 ≤ (C * (n : ℝ) ^ ((1 / 2 : ℝ) + ε / 2)) ^ 2 := hs
      _ = C ^ 2 * (n : ℝ) ^ (1 + ε) := by rw [mul_pow, hp]
      _ ≤ C ^ 2 * ((n + 1 : ℕ) : ℝ) ^ (1 + ε) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hn0.le (by exact_mod_cast Nat.le_succ n) (by linarith)) (sq_nonneg C)

theorem mertens_half_of_mertensEnergy
    (henergy : MertensEnergyBoundedStatement) : MertensGrowthAtMost (1 / 2 : ℝ) := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := henergy (2 * ε) (by linarith)
  refine ⟨Real.sqrt C * (2 : ℝ) ^ ((1 / 2 : ℝ) + ε), by positivity, ?_⟩
  intro n hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hscale : ((n + 1 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
    exact_mod_cast (show n + 1 ≤ 2 * n by omega)
  have hmajorant : ‖mertensSummatory n‖ ^ 2 ≤
      C * ((2 : ℝ) ^ (1 + 2 * ε) * (n : ℝ) ^ (1 + 2 * ε)) := by
    calc
      ‖mertensSummatory n‖ ^ 2 ≤ C * ((n + 1 : ℕ) : ℝ) ^ (1 + 2 * ε) := hbound n
      _ ≤ C * (2 * (n : ℝ)) ^ (1 + 2 * ε) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) hscale (by linarith)) hC
      _ = _ := by rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hn0.le]
  have hp (x : ℝ) (hx : 0 ≤ x) :
      (x ^ ((1 / 2 : ℝ) + ε)) ^ (2 : ℕ) = x ^ (1 + 2 * ε) := by
    rw [← Real.rpow_mul_natCast hx]
    congr 1
    ring
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  calc
    ‖mertensSummatory n‖ ^ 2 ≤
        C * ((2 : ℝ) ^ (1 + 2 * ε) * (n : ℝ) ^ (1 + 2 * ε)) := hmajorant
    _ = (Real.sqrt C * (2 : ℝ) ^ ((1 / 2 : ℝ) + ε) * (n : ℝ) ^ ((1 / 2 : ℝ) + ε)) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hC, hp 2 (by norm_num), hp n hn0.le]
      ring

theorem mertens_half_iff_mertensEnergy :
    MertensGrowthAtMost (1 / 2 : ℝ) ↔ MertensEnergyBoundedStatement :=
  ⟨mertensEnergy_of_mertens_half, mertens_half_of_mertensEnergy⟩

/-- Mathlib RH directly supplies every actual zero in the open critical strip. -/
theorem criticalZeros_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∀ ρ : ℂ, NontrivialZetaZero ρ → ρ.re = (1 / 2 : ℝ) := by
  intro ρ hρ
  apply hRH ρ hρ.1
  · rintro ⟨n, hn⟩
    have hreal := congrArg Complex.re hn
    simp only [Complex.mul_re, Complex.neg_re, Complex.re_ofNat, Complex.add_re,
      Complex.natCast_re, Complex.one_re, Complex.neg_im, Complex.im_ofNat,
      Complex.add_im, Complex.natCast_im, Complex.one_im, zero_add, neg_zero,
      zero_mul, sub_zero] at hreal
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith [hρ.2.1]
  · intro hone
    have hreal := congrArg Complex.re hone
    simp only [Complex.one_re] at hreal
    linarith [hρ.2.2]

/-- The open-strip formulation and Mathlib's full RH proposition coincide. -/
theorem criticalZeros_iff_riemannHypothesis :
    (∀ ρ : ℂ, NontrivialZetaZero ρ → ρ.re = (1 / 2 : ℝ)) ↔ RiemannHypothesis := by
  constructor
  · intro h
    exact riemannHypothesis_of_mertensEnergy
      (mertensEnergy_of_mertens_half (growthAtMost_half_iff_criticalZeros.mpr h))
  · exact criticalZeros_of_riemannHypothesis

theorem mertens_half_iff_riemannHypothesis :
    MertensGrowthAtMost (1 / 2 : ℝ) ↔ RiemannHypothesis :=
  growthAtMost_half_iff_criticalZeros.trans criticalZeros_iff_riemannHypothesis

theorem zeroLog_iff_mertensEnergy :
    SquareRootAmplificationZeroLogGrowthStatement ↔ MertensEnergyBoundedStatement :=
  zeroLog_iff_mertens_half.trans mertens_half_iff_mertensEnergy

theorem zeroLog_iff_riemannHypothesis :
    SquareRootAmplificationZeroLogGrowthStatement ↔ RiemannHypothesis :=
  zeroLog_iff_criticalZeros.trans criticalZeros_iff_riemannHypothesis

theorem native_owner_zero_iff_riemannHypothesis :
    OwnerPrefix.NativeOwnerBound 0 ↔ RiemannHypothesis :=
  OwnerPrefix.native_owner_zero_iff_criticalZeros.trans criticalZeros_iff_riemannHypothesis

end RHLean.Analysis.UniversalEnvelope

end
