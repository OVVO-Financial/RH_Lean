import «research.MERTENS_EXPONENT_STRIP_MAP»

/-!
# Endpoint regressions and the independent rightmost-zero coordinate

The finite witness below refutes the unit horizontal envelope only. It is not
misrepresented as a refutation of every possible constant. The zero coordinate
is defined from the genuine zeta zeros, independently of the Mertens exponent.
The proved comparison is `Theta <= lambda_M`; the converse remains separate.
-/

noncomputable section
namespace RHLean.Analysis.MertensExponent
open Set
open scoped ArithmeticFunction.Moebius BigOperators

/-- Exact finite arithmetic: the unit constant envelope already fails at 5. -/
theorem mertens_five : mertensSummatory 5 = (-2 : ℂ) := by
  have h2 : μ 2 = (-1 : ℤ) := ArithmeticFunction.moebius_apply_prime (by norm_num)
  have h3 : μ 3 = (-1 : ℤ) := ArithmeticFunction.moebius_apply_prime (by norm_num)
  have h4 : μ 4 = (0 : ℤ) := by
    have h := ArithmeticFunction.moebius_apply_prime_pow
      (p := 2) (k := 2) (by norm_num) (by norm_num)
    norm_num at h
    exact h
  have h5 : μ 5 = (-1 : ℤ) := ArithmeticFunction.moebius_apply_prime (by norm_num)
  norm_num [mertensSummatory, Finset.sum_range_succ,
    ArithmeticFunction.moebius_apply_one, h2, h3, h4, h5]

/-- C=1 and exponent zero fail. This conclusion does not quantify over C. -/
theorem unit_horizontal_envelope_fails :
    ¬ (∀ n : ℕ, 1 ≤ n → ‖mertensSummatory n‖ ≤ Real.rpow (n : ℝ) 0) := by
  intro h
  have h5 := h 5 (by norm_num)
  norm_num [mertens_five] at h5

/-- Every finite prefix has a constant envelope, so a census alone cannot
refute a global existential-constant statement. -/
theorem finite_prefix_constant_envelope (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, n ≤ N → ‖mertensSummatory n‖ ≤ C := by
  refine ⟨(N : ℝ), Nat.cast_nonneg N, fun n hn => ?_⟩
  exact (mertens_norm_le n).trans (by exact_mod_cast hn)

/-- The genuine zero-coordinate set, not a definition through Mertens growth. -/
def zeroRealParts : Set ℝ :=
  {b | ∃ ρ : ℂ, NontrivialZetaZero ρ ∧ ρ.re = b}

/-- Rightmost-zero supremum in the open critical strip. -/
def zetaRightmostRealPart : ℝ := sSup zeroRealParts

theorem zeroRealParts_bddAbove : BddAbove zeroRealParts := by
  refine ⟨1, ?_⟩
  rintro b ⟨ρ, hρ, rfl⟩
  exact hρ.2.2.le

/-- Every genuine zero lies at or left of the independent zero supremum. -/
theorem zero_re_le_rightmost {ρ : ℂ} (hρ : NontrivialZetaZero ρ) :
    ρ.re ≤ zetaRightmostRealPart :=
  le_csSup zeroRealParts_bddAbove ⟨ρ, hρ, rfl⟩

/-- Supremum version of the direct map. Nonemptiness is an explicit input;
no numerical zero-existence assertion is used as an axiom. -/
theorem rightmost_le_growthExponent (hne : ∃ ρ : ℂ, NontrivialZetaZero ρ) :
    zetaRightmostRealPart ≤ mertensGrowthExponent := by
  obtain ⟨ρ, hρ⟩ := hne
  apply csSup_le (show zeroRealParts.Nonempty from ⟨ρ.re, ρ, hρ, rfl⟩)
  rintro b ⟨z, hz, rfl⟩
  exact zero_re_le_growthExponent hz

/-- Symmetric zero confinement is exactly the rightmost-coordinate upper
bound. Its equivalence with Mertens growth would additionally need the
unproved-in-this-PR reverse analytic direction. -/
theorem strip_iff_rightmost_le (a : ℝ)
    (hne : ∃ ρ : ℂ, NontrivialZetaZero ρ) :
    ZerosInSymmetricStrip a ↔ zetaRightmostRealPart ≤ a := by
  constructor
  · intro h
    obtain ⟨ρ, hρ⟩ := hne
    apply csSup_le (show zeroRealParts.Nonempty from ⟨ρ.re, ρ, hρ, rfl⟩)
    rintro b ⟨z, hz, rfl⟩
    exact (h z hz).2
  · intro h ρ hρ
    have hr := (zero_re_le_rightmost hρ).trans h
    have hl := (zero_re_le_rightmost (nontrivialZero_one_sub hρ)).trans h
    simp only [Complex.sub_re, Complex.one_re] at hl
    exact ⟨by linarith, hr⟩

end RHLean.Analysis.MertensExponent
