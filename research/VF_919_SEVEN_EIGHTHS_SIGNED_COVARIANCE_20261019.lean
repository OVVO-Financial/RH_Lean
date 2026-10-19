import RHLean.Analysis.MathlibMertensHook
import «research.MERTENS_CONVERSE_IDENTIFICATION»

/-!
# The exact seven-eighths signed Mobius covariance threshold

The native physical population is the genuine rational Mobius function, not
a fictitious independent sign model or an Eisenstein character proxy.

At every integer X, let K_X be the squarefree diagonal and C_X the sum
over all distinct ordered-by-size pairs 1 <= i < j <= X. Then

    |M(X)|^2 = K_X + 2*C_X.

The precise seven-eighths covariance contract is

    2*C_X <= (A_epsilon * X^(7/8 + epsilon))^2 - K_X.

Its quantifiers are ALL X and EVERY positive epsilon, with a constant that
may depend on epsilon. It is equivalent to seven-eighths Mertens growth and,
using the repository's independently proved converse, to confinement of
nontrivial zeta zeros to [1/8,7/8].

An externally supplied unconditional seven-eighths nonvanishing theorem
therefore discharges the contract, but none is imported here. Neither the
contract nor its equivalence is an unconditional proof of nonvanishing.
-/

noncomputable section

namespace RHLean.Analysis

open MertensExponent
open scoped ArithmeticFunction.Moebius BigOperators

/-- Exact NNS zero-target signed covariance with the physical diagonal. -/
theorem vf919_mertens_sq_eq_signedPair (x : ℕ) :
    ‖mertensSummatory x‖ ^ 2 =
      realMertensDiagonal (x + 1) +
        2 * realMertensPositiveLagPairSum (x + 1) :=
  (norm_mertensSummatory_sq_eq_realMertensLength_sq x).trans
    (realMertensLength_sq_eq_diagonal_add_two_mul_positiveLagPairSum (x + 1))

/-- The exact seven-eighths pair-energy claim, WITHOUT dropping the
squarefree diagonal or replacing signed covariance by absolute mass. -/
def VF919SevenEighthsSignedCovarianceBound : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℕ, 1 ≤ x →
      realMertensDiagonal (x + 1) +
          2 * realMertensPositiveLagPairSum (x + 1) ≤
        (C * Real.rpow (x : ℝ) ((7 : ℝ) / 8 + ε)) ^ 2

/-- No analytic estimate is hidden in this exact equivalence: it is the
Green--Kubo square identity plus the definition of a Mertens power bound. -/
theorem vf919_sevenEighthsSignedCovariance_iff_mertensGrowth :
    VF919SevenEighthsSignedCovarianceBound ↔
      MertensGrowthAtMost ((7 : ℝ) / 8) := by
  constructor
  · intro h ε hε
    obtain ⟨C, hC, hbound⟩ := h ε hε
    refine ⟨C, hC, ?_⟩
    intro x hx
    have hsq :
        ‖mertensSummatory x‖ ^ 2 ≤
          (C * Real.rpow (x : ℝ) ((7 : ℝ) / 8 + ε)) ^ 2 := by
      exact (vf919_mertens_sq_eq_signedPair x).trans_le (hbound x hx)
    exact (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg x) _))).mp hsq
  · intro h ε hε
    obtain ⟨C, hC, hbound⟩ := h ε hε
    refine ⟨C, hC, ?_⟩
    intro x hx
    have hsq :
        ‖mertensSummatory x‖ ^ 2 ≤
          (C * Real.rpow (x : ℝ) ((7 : ℝ) / 8 + ε)) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg x) _))).mpr
          (hbound x hx)
    rw [← vf919_mertens_sq_eq_signedPair x]
    exact hsq

/-- The covariance bound is precisely the 7/8 zeta-zero-strip criterion.
This is an equivalence, not a new unconditional zero-free theorem. -/
theorem vf919_sevenEighthsSignedCovariance_iff_zetaStrip :
    VF919SevenEighthsSignedCovarianceBound ↔
      (∀ ρ : ℂ, NontrivialZetaZero ρ →
        (1 : ℝ) / 8 ≤ ρ.re ∧ ρ.re ≤ (7 : ℝ) / 8) :=
  vf919_sevenEighthsSignedCovariance_iff_mertensGrowth.trans
    growthAtMost_sevenEighths_iff_strip

/-- An actual zeta 7/8 nonvanishing theorem yields the exact physical
Mobius pair-covariance bound. Its premise is conspicuous and unimported. -/
theorem vf919_sevenEighthsSignedCovariance_of_zetaNonzero
    (hz : ∀ s : ℂ, (7 : ℝ) / 8 < s.re → riemannZeta s ≠ 0) :
    VF919SevenEighthsSignedCovarianceBound := by
  apply vf919_sevenEighthsSignedCovariance_iff_zetaStrip.mpr
  intro ρ hρ
  have hr : ρ.re ≤ (7 : ℝ) / 8 := by
    by_contra hh
    exact hz ρ (lt_of_not_ge hh) hρ.1
  have hρref := nontrivialZero_one_sub hρ
  have hleftBound : (1 - ρ).re ≤ (7 : ℝ) / 8 := by
    by_contra hh
    exact hz (1 - ρ) (lt_of_not_ge hh) hρref.1
  have hRe : (1 - ρ).re = 1 - ρ.re := by simp
  constructor
  · rw [hRe] at hleftBound
    linarith
  · exact hr

/-- This is the actual signed upper-pair inequality the arithmetic research
must obtain, including the negative squarefree diagonal payment. -/
theorem vf919_sevenEighthsSignedPair_upper_of_zetaNonzero
    (hz : ∀ s : ℂ, (7 : ℝ) / 8 < s.re → riemannZeta s ≠ 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℕ, 1 ≤ x →
      2 * realMertensPositiveLagPairSum (x + 1) ≤
        (C * Real.rpow (x : ℝ) ((7 : ℝ) / 8 + ε)) ^ 2 -
          realMertensDiagonal (x + 1) := by
  obtain ⟨C, hC, hbound⟩ :=
    (vf919_sevenEighthsSignedCovariance_of_zetaNonzero hz) ε hε
  refine ⟨C, hC, ?_⟩
  intro x hx
  linarith [hbound x hx]

#print axioms vf919_mertens_sq_eq_signedPair
#print axioms vf919_sevenEighthsSignedCovariance_iff_mertensGrowth
#print axioms vf919_sevenEighthsSignedCovariance_iff_zetaStrip
#print axioms vf919_sevenEighthsSignedCovariance_of_zetaNonzero
#print axioms vf919_sevenEighthsSignedPair_upper_of_zetaNonzero

end RHLean.Analysis
